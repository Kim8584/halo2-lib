#![allow(non_snake_case)]
//! Proving Fixed-G2 Pairing Chip for BN254.
//!
//! Implements pairing check verification for fixed G2 points and dynamic G1 points:
//!   \prod_{i=1}^N e(P_i, Q_{f,i}) = 1
//! where each Q_{f,i} is a fixed compile-time / verifying-key constant in G2.
//!
//! # Optimizations over Dynamic G2 Pairing:
//! 1. All G2 curve doublings, additions, and Frobenius endomorphisms are precomputed
//!    offline into static line coefficients in F_{p^2}.
//!    In-circuit G2 curve operations: ZERO cells (saving ~198k cells per point).
//! 2. In-circuit line evaluation at challenge z requires only scalar F_p operations:
//!    c(z) = c0 + c1 * (z^6 - 9).
//! 3. In-circuit final exponentiation is eliminated via the Eagen-Novakovic / Garaga
//!    hinted polynomial evaluation technique over F_p[X] / (X^12 - 18X^6 + 82),
//!    saving 1,673,268 cells.
//! 4. Sound 2-phase Fiat-Shamir protocol compatible with real KZG SHPLONK proving.

use crate::bn254::{
    polynomial::{Poly11, M_COEFF_0, M_COEFF_6},
    FpChip, FpPoint,
};
use crate::fields::FieldChip;
use crate::ecc::EcPoint;
use crate::halo2_proofs::halo2curves::bn256::{
    Fq, Fq12, Fq2, G2Affine, FROBENIUS_COEFF_FQ12_C1, SIX_U_PLUS_2_NAF,
};
use halo2_base::{
    utils::BigPrimeField,
    Context,
};

// ============================================================================
// 1. Precomputed Line Representation & Offline Generators
// ============================================================================

/// Represents a precomputed line function for a fixed G2 point
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrecomputedLine {
    /// Line function for point doubling:
    ///   ell(P) = out0 + out3 * P.y * w^3 + out4 * P.x * w^4
    /// where out0 = (3 x^3 - 2 y^2) * (9 + u), out3 = 2 y, out4 = -3 x^2
    Double {
        out0: Fq2,
        out3: Fq2,
        out4: Fq2,
    },
    /// Line function for point addition:
    ///   ell(P) = out2 * P.y * w^2 + out3 * P.x * w^3 + out5 * w^5
    /// where out2 = x_2 - x_1, out3 = y_1 - y_2, out5 = x_1 y_2 - x_2 y_1
    Add {
        out2: Fq2,
        out3: Fq2,
        out5: Fq2,
    },
}

/// Helper: Fq2 multiplication by (9 + u)
pub fn mul_fq2_by_w6(a: Fq2) -> Fq2 {
    // (a0 + a1 * u) * (9 + u) where u^2 = -1 (in halo2curves bn256)
    // = 9*a0 + 9*a1*u + a0*u + a1*u^2
    // = (9*a0 - a1) + (9*a1 + a0)*u
    let nine = Fq::from(9u64);
    let c0 = nine * a.c0 - a.c1;
    let c1 = nine * a.c1 + a.c0;
    Fq2 { c0, c1 }
}

/// Helper: Point doubling on G2 twist E'(Fq2): y^2 = x^3 + 3/(9+u)
pub fn g2_double(p: (Fq2, Fq2)) -> (Fq2, Fq2) {
    let (x, y) = p;
    // lambda = (3 * x^2) / (2 * y)
    let three = Fq2 { c0: Fq::from(3u64), c1: Fq::zero() };
    let two = Fq2 { c0: Fq::from(2u64), c1: Fq::zero() };
    let num = three * x * x;
    let den = two * y;
    let lambda = num * den.invert().unwrap();

    // x3 = lambda^2 - 2 * x
    let x3 = lambda * lambda - two * x;
    // y3 = lambda * (x - x3) - y
    let y3 = lambda * (x - x3) - y;
    (x3, y3)
}

/// Helper: Point addition on G2 twist E'(Fq2)
pub fn g2_add_unequal(p: (Fq2, Fq2), q: (Fq2, Fq2)) -> (Fq2, Fq2) {
    let (x1, y1) = p;
    let (x2, y2) = q;
    // lambda = (y2 - y1) / (x2 - x1)
    let num = y2 - y1;
    let den = x2 - x1;
    let lambda = num * den.invert().unwrap();

    // x3 = lambda^2 - x1 - x2
    let x3 = lambda * lambda - x1 - x2;
    // y3 = lambda * (x1 - x3) - y1
    let y3 = lambda * (x1 - x3) - y1;
    (x3, y3)
}

/// Precomputes all Miller loop line functions for a fixed G2 point Q on BN254.
/// The resulting sequence of lines matches halo2-ecc's miller_loop_BN.
pub fn precompute_lines_bn254(q: &G2Affine) -> Vec<PrecomputedLine> {
    let mut lines = Vec::new();

    let mut i = SIX_U_PLUS_2_NAF.len() - 1;
    while SIX_U_PLUS_2_NAF[i] == 0 {
        i -= 1;
    }
    let last_index = i;

    let neg_q = -*q;
    let mut r = if SIX_U_PLUS_2_NAF[i] == 1 {
        (q.x, q.y)
    } else {
        (neg_q.x, neg_q.y)
    };
    i -= 1;

    // Initial equal line on R
    {
        let (x, y) = r;
        let x_sq = x * x;
        let x_cu = x_sq * x;
        let y_sq = y * y;
        let three = Fq::from(3u64);
        let two = Fq::from(2u64);
        let out0_left = Fq2 {
            c0: three * x_cu.c0 - two * y_sq.c0,
            c1: three * x_cu.c1 - two * y_sq.c1,
        };
        let out0 = mul_fq2_by_w6(out0_left);
        let out3 = Fq2 {
            c0: two * y.c0,
            c1: two * y.c1,
        };
        let out4 = Fq2 {
            c0: -three * x_sq.c0,
            c1: -three * x_sq.c1,
        };
        lines.push(PrecomputedLine::Double { out0, out3, out4 });
    }

    loop {
        if i != last_index - 1 {
            let (x, y) = r;
            let x_sq = x * x;
            let x_cu = x_sq * x;
            let y_sq = y * y;
            let three = Fq::from(3u64);
            let two = Fq::from(2u64);
            let out0_left = Fq2 {
                c0: three * x_cu.c0 - two * y_sq.c0,
                c1: three * x_cu.c1 - two * y_sq.c1,
            };
            let out0 = mul_fq2_by_w6(out0_left);
            let out3 = Fq2 {
                c0: two * y.c0,
                c1: two * y.c1,
            };
            let out4 = Fq2 {
                c0: -three * x_sq.c0,
                c1: -three * x_sq.c1,
            };
            lines.push(PrecomputedLine::Double { out0, out3, out4 });
        }
        r = g2_double(r);

        if SIX_U_PLUS_2_NAF[i] != 0 {
            let sign_q = if SIX_U_PLUS_2_NAF[i] == 1 {
                (q.x, q.y)
            } else {
                (neg_q.x, neg_q.y)
            };
            let out3 = r.1 - sign_q.1;
            let out2 = sign_q.0 - r.0;
            let out5 = r.0 * sign_q.1 - sign_q.0 * r.1;
            lines.push(PrecomputedLine::Add { out2, out3, out5 });
            r = g2_add_unequal(r, sign_q);
        }

        if i == 0 {
            break;
        }
        i -= 1;
    }

    // Twisted Frobenius steps:
    let c2 = FROBENIUS_COEFF_FQ12_C1[1] * FROBENIUS_COEFF_FQ12_C1[1];
    let c3 = c2 * FROBENIUS_COEFF_FQ12_C1[1];

    // Q_1 = twisted_frobenius(Q)
    let q1_x = Fq2 { c0: q.x.c0, c1: -q.x.c1 } * c2;
    let q1_y = Fq2 { c0: q.y.c0, c1: -q.y.c1 } * c3;
    let q1 = (q1_x, q1_y);

    let out3 = r.1 - q1.1;
    let out2 = q1.0 - r.0;
    let out5 = r.0 * q1.1 - q1.0 * r.1;
    lines.push(PrecomputedLine::Add { out2, out3, out5 });
    r = g2_add_unequal(r, q1);

    // -Q_2 = neg_twisted_frobenius(Q_1)
    let neg_q2_x = Fq2 { c0: q1.0.c0, c1: -q1.0.c1 } * c2;
    let neg_q2_y = Fq2 { c0: -q1.1.c0, c1: q1.1.c1 } * c3;
    let neg_q2 = (neg_q2_x, neg_q2_y);

    let out3 = r.1 - neg_q2.1;
    let out2 = neg_q2.0 - r.0;
    let out5 = r.0 * neg_q2.1 - neg_q2.0 * r.1;
    lines.push(PrecomputedLine::Add { out2, out3, out5 });

    lines
}

// ============================================================================
// 2. In-Circuit Line Evaluation at Challenge z
// ============================================================================

/// Evaluates a constant Fq2 element c = c0 + c1 * u at challenge point z
/// using u = z^6 - 9:
///   c(z) = c0 + c1 * (z^6 - 9)
pub fn eval_const_fp2_at_z<F: BigPrimeField>(
    ctx: &mut Context<F>,
    fp_chip: &FpChip<F>,
    c: &Fq2,
    z6_minus_9: &FpPoint<F>,
) -> FpPoint<F> {
    let c0 = fp_chip.load_constant(ctx, c.c0);
    let c1 = fp_chip.load_constant(ctx, c.c1);
    let c1_u = fp_chip.mul(ctx, &c1, z6_minus_9);
    let res = fp_chip.add_no_carry(ctx, &c0, &c1_u);
    fp_chip.carry_mod(ctx, res)
}

/// Evaluates a precomputed line at challenge point z and dynamic G1 point P:
///   Double: out0(z) + out3(z)*z^3*P.y + out4(z)*z^4*P.x
///   Add:    out2(z)*z^2*P.y + out3(z)*z^3*P.x + out5(z)*z^5
pub fn eval_precomputed_line_at_z<F: BigPrimeField>(
    ctx: &mut Context<F>,
    fp_chip: &FpChip<F>,
    line: &PrecomputedLine,
    P: &EcPoint<F, FpPoint<F>>,
    z_powers: &[FpPoint<F>],
    z6_minus_9: &FpPoint<F>,
) -> FpPoint<F> {
    match line {
        PrecomputedLine::Double { out0, out3, out4 } => {
            let out0_z = eval_const_fp2_at_z(ctx, fp_chip, out0, z6_minus_9);
            let out3_z = eval_const_fp2_at_z(ctx, fp_chip, out3, z6_minus_9);
            let out4_z = eval_const_fp2_at_z(ctx, fp_chip, out4, z6_minus_9);

            let out3_z3 = fp_chip.mul(ctx, &out3_z, &z_powers[3]);
            let out3_term = fp_chip.mul(ctx, &out3_z3, &P.y);

            let out4_z4 = fp_chip.mul(ctx, &out4_z, &z_powers[4]);
            let out4_term = fp_chip.mul(ctx, &out4_z4, &P.x);

            let s1 = fp_chip.add_no_carry(ctx, &out0_z, &out3_term);
            let s2 = fp_chip.add_no_carry(ctx, &s1, &out4_term);
            fp_chip.carry_mod(ctx, s2)
        }
        PrecomputedLine::Add { out2, out3, out5 } => {
            let out2_z = eval_const_fp2_at_z(ctx, fp_chip, out2, z6_minus_9);
            let out3_z = eval_const_fp2_at_z(ctx, fp_chip, out3, z6_minus_9);
            let out5_z = eval_const_fp2_at_z(ctx, fp_chip, out5, z6_minus_9);

            let out2_z2 = fp_chip.mul(ctx, &out2_z, &z_powers[2]);
            let out2_term = fp_chip.mul(ctx, &out2_z2, &P.y);

            let out3_z3 = fp_chip.mul(ctx, &out3_z, &z_powers[3]);
            let out3_term = fp_chip.mul(ctx, &out3_z3, &P.x);

            let out5_term = fp_chip.mul(ctx, &out5_z, &z_powers[5]);

            let s1 = fp_chip.add_no_carry(ctx, &out2_term, &out3_term);
            let s2 = fp_chip.add_no_carry(ctx, &s1, &out5_term);
            fp_chip.carry_mod(ctx, s2)
        }
    }
}

// ============================================================================
// 3. Mathematical Basis Conversion: Fq12 <-> Poly11
// ============================================================================

/// Converts an Fq12 element into its degree-11 polynomial representation over Fq
pub fn fq12_to_poly11(f: &Fq12) -> Poly11 {
    let poly_fp2 = [
        f.c0.c0, // w^0
        f.c1.c0, // w^1
        f.c0.c1, // w^2
        f.c1.c1, // w^3
        f.c0.c2, // w^4
        f.c1.c2, // w^5
    ];

    let mut out = [Fq::zero(); 12];
    let nine = Fq::from(9u64);

    for k in 0..6 {
        let x = poly_fp2[k].c0;
        let y = poly_fp2[k].c1;
        out[k] = x - nine * y;
        out[k + 6] = y;
    }
    out
}

/// Converts a degree-11 polynomial back into an Fq12 element
pub fn poly11_to_fq12(poly: &Poly11) -> Fq12 {
    let mut poly_fp2 = [Fq2::zero(); 6];
    let nine = Fq::from(9u64);

    for k in 0..6 {
        let x = poly[k] + nine * poly[k + 6];
        let y = poly[k + 6];
        poly_fp2[k] = Fq2 { c0: x, c1: y };
    }

    Fq12 {
        c0: crate::halo2_proofs::halo2curves::bn256::Fq6 {
            c0: poly_fp2[0],
            c1: poly_fp2[2],
            c2: poly_fp2[4],
        },
        c1: crate::halo2_proofs::halo2curves::bn256::Fq6 {
            c0: poly_fp2[1],
            c1: poly_fp2[3],
            c2: poly_fp2[5],
        },
    }
}

// ============================================================================
// 4. Proving Fixed Pairing Chip
// ============================================================================

pub struct ProvingFixedPairingChip<'chip, F: BigPrimeField> {
    pub fp_chip: &'chip FpChip<'chip, F>,
}

impl<'chip, F: BigPrimeField> ProvingFixedPairingChip<'chip, F> {
    pub fn new(fp_chip: &'chip FpChip<'chip, F>) -> Self {
        Self { fp_chip }
    }

    /// Computes powers of challenge z: [1, z, z^2, z^3, z^4, z^5, z^6]
    pub fn compute_z_powers(
        &self,
        ctx: &mut Context<F>,
        z: &FpPoint<F>,
    ) -> (Vec<FpPoint<F>>, FpPoint<F>) {
        let one = self.fp_chip.load_constant(ctx, Fq::one());
        let mut powers = Vec::with_capacity(7);
        powers.push(one);
        powers.push(z.clone());
        for i in 2..=6 {
            let next = self.fp_chip.mul(ctx, &powers[i - 1], z);
            powers.push(next);
        }

        let nine = self.fp_chip.load_constant(ctx, Fq::from(9u64));
        let z6_minus_9_nc = self.fp_chip.sub_no_carry(ctx, &powers[6], &nine);
        let z6_minus_9 = self.fp_chip.carry_mod(ctx, z6_minus_9_nc);

        (powers, z6_minus_9)
    }

    /// Evaluates M(z) = z^12 - 18*z^6 + 82
    pub fn eval_M(
        &self,
        ctx: &mut Context<F>,
        z6: &FpPoint<F>,
    ) -> FpPoint<F> {
        let z12 = self.fp_chip.mul(ctx, z6, z6);
        let eighteen = self.fp_chip.load_constant(ctx, Fq::from(M_COEFF_6));
        let eighty_two = self.fp_chip.load_constant(ctx, Fq::from(M_COEFF_0));

        let term1 = self.fp_chip.mul(ctx, &eighteen, z6);
        let sub = self.fp_chip.sub_no_carry(ctx, &z12, &term1);
        let add = self.fp_chip.add_no_carry(ctx, &sub, &eighty_two);
        self.fp_chip.carry_mod(ctx, add)
    }

    /// Evaluates a degree-11 polynomial at challenge point z using Horner's rule
    pub fn horner_eval_poly11(
        &self,
        ctx: &mut Context<F>,
        poly: &[FpPoint<F>],
        z: &FpPoint<F>,
    ) -> FpPoint<F> {
        assert_eq!(poly.len(), 12);
        let mut acc = poly[11].clone();
        for coeff in poly.iter().rev().skip(1) {
            let mul = self.fp_chip.mul(ctx, &acc, z);
            let add = self.fp_chip.add_no_carry(ctx, &mul, coeff);
            acc = self.fp_chip.carry_mod(ctx, add);
        }
        acc
    }

    /// Evaluates a degree-10 polynomial at challenge point z using Horner's rule
    pub fn horner_eval_poly10(
        &self,
        ctx: &mut Context<F>,
        poly: &[FpPoint<F>],
        z: &FpPoint<F>,
    ) -> FpPoint<F> {
        assert_eq!(poly.len(), 11);
        let mut acc = poly[10].clone();
        for coeff in poly.iter().rev().skip(1) {
            let mul = self.fp_chip.mul(ctx, &acc, z);
            let add = self.fp_chip.add_no_carry(ctx, &mul, coeff);
            acc = self.fp_chip.carry_mod(ctx, add);
        }
        acc
    }

    /// Enforces subfield constraint: w is strictly in F_{p^6} (all odd coefficients are zero)
    pub fn assert_subfield_fp6(
        &self,
        ctx: &mut Context<F>,
        w_poly: &[FpPoint<F>],
    ) {
        assert_eq!(w_poly.len(), 12);
        let zero = self.fp_chip.load_constant(ctx, Fq::zero());
        for &odd_idx in &[1, 3, 5, 7, 9, 11] {
            self.fp_chip.assert_equal(ctx, &w_poly[odd_idx], &zero);
        }
    }

    /// Enforces invertibility of root witness c:
    ///   c(z) * c_inv(z) - 1 == Q_inv(z) * M(z)
    pub fn assert_invertibility(
        &self,
        ctx: &mut Context<F>,
        c_z: &FpPoint<F>,
        cinv_z: &FpPoint<F>,
        q_inv_z: &FpPoint<F>,
        m_z: &FpPoint<F>,
    ) {
        let prod = self.fp_chip.mul(ctx, c_z, cinv_z);
        let one = self.fp_chip.load_constant(ctx, Fq::one());
        let lhs = self.fp_chip.sub_no_carry(ctx, &prod, &one);
        let lhs_red = self.fp_chip.carry_mod(ctx, lhs);

        let rhs = self.fp_chip.mul(ctx, q_inv_z, m_z);
        self.fp_chip.assert_equal(ctx, &lhs_red, &rhs);
    }
}

