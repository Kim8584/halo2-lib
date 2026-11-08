#![allow(non_snake_case)]
//! Proving Pairing Chip for BN254.
//!
//! Implements pairing verification for non-fixed points $(P_1, Q_1)$ and $(P_2, Q_2)$
//! verifying $e(P_1, Q_1) \cdot e(P_2, Q_2) = 1$ without in-circuit final exponentiation.
//!
//! # Protocol Overview
//!
//! 1. **Elimination of Final Exponentiation**:
//!    Instead of evaluating $f^{(p^{12}-1)/r}$ in-circuit, the prover witnesses the root $c$
//!    such that $c^{\lambda_s} = f \cdot w$, where $w \in \mathbb{F}_{p^6}$.
//!    The accumulator is initialized to $c^{-1}$ and folded Horner-style directly into the
//!    Miller loop steps. The final accumulator evaluates identically to $1 \in \mathbb{F}_{p^{12}}$.
//!
//! 2. **Hinted $\mathbb{F}_{p^{12}}$ Polynomial Evaluations at Challenge $z$**:
//!    Every element $A \in \mathbb{F}_{p^{12}}$ is isomorphic to a polynomial $A(X) \in \mathbb{F}_p[X] / (M(X))$
//!    of degree $\le 11$, where $M(X) = X^{12} - 18X^6 + 82$.
//!    Prover witnesses the quotient polynomials $Q_i(X)$ for polynomial multiplication steps:
//!    $$A_i(X) \cdot B_i(X) = Q_i(X) \cdot M(X) + C_i(X)$$
//!    At a random challenge $z \in \mathbb{F}_p$, verifying $A(X) \cdot B(X) \equiv C(X) \pmod{M(X)}$ reduces
//!    by the Schwartz-Zippel lemma to checking:
//!    $$A_i(z) \cdot B_i(z) - C_i(z) = Q_i(z) \cdot M(z)$$
//!    A single batched check with challenge $\alpha \in \mathbb{F}_p$ verifies all steps at once:
//!    $$\sum_i \alpha^i [A_i(z) B_i(z) - C_i(z)] = \left(\sum_i \alpha^i Q_i(z)\right) \cdot M(z)$$
//!
//! 3. **Non-Fixed $P$ and $Q$ Dynamic Lines**:
//!    $P_i \in E(\mathbb{F}_p)$ and $Q_i \in E(\mathbb{F}_{p^2})$ are dynamic (not fixed).
//!    Lines are evaluated dynamically using standard point addition and doubling formulas.
//!    Since $u = w^6 - 9$, any $\mathbb{F}_{p^2}$ line coefficient $c_0 + c_1 u$ evaluated at $w=z$
//!    is simply $c_0 + c_1(z^6 - 9) \in \mathbb{F}_p$.
//!
//! 4. **Soundness Guarantee**:
//!    The subfield scaling factor $w$ is constrained to $\mathbb{F}_{p^6}$ (all odd degree coefficients are zero),
//!    preventing known subgroup forgery attacks. Invertibility of $c$ is checked via $c(z) c^{-1}(z) - 1 = Q_{\text{inv}}(z) M(z)$.

use super::{FpChip, FpPoint, FqPoint};
use crate::fields::FieldChip;
use crate::halo2_proofs::halo2curves::bn256::{Fq, Fq12, Fq2, Fq6};
use halo2_base::utils::BigPrimeField;
use halo2_base::Context;

// ============================================================================
// Mathematical Constants & Off-Circuit Polynomial Math
// ============================================================================

/// Minimal polynomial modulus M(X) = X^12 - 18*X^6 + 82
pub const M_COEFF_6: u64 = 18;
pub const M_COEFF_0: u64 = 82;

/// Evaluates M(z) = z^12 - 18*z^6 + 82 in Fq
pub fn eval_M_native(z: Fq) -> Fq {
    let z2 = z.square();
    let z6 = z2.square() * z2;
    let z12 = z6.square();
    let eighteen = Fq::from(M_COEFF_6);
    let eighty_two = Fq::from(M_COEFF_0);
    z12 - eighteen * z6 + eighty_two
}

/// Degree-11 polynomial representation in F_p[X] / (X^12 - 18X^6 + 82)
pub type Poly11 = [Fq; 12];
/// Degree-10 polynomial representation in F_p[X]
pub type Poly10 = [Fq; 11];

/// Converts an Fq12 element into its degree-11 polynomial representation over Fq
pub fn fq12_to_poly11(f: &Fq12) -> Poly11 {
    // f = c0 + c1 * w with c0, c1 in Fq6
    // c0 = c00 + c01 * w^2 + c02 * w^4
    // c1 = c10 + c11 * w^2 + c12 * w^4
    // where each cij = x_ij + y_ij * u in Fq2
    // using u = w^6 - 9:
    // (x + y*u) w^k = (x - 9y) w^k + y w^(k+6)
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

    let c0 = Fq6 {
        c0: poly_fp2[0],
        c1: poly_fp2[2],
        c2: poly_fp2[4],
    };
    let c1 = Fq6 {
        c0: poly_fp2[1],
        c1: poly_fp2[3],
        c2: poly_fp2[5],
    };
    Fq12 { c0, c1 }
}

/// Evaluates a degree-11 polynomial at challenge point z in Fq
pub fn eval_poly11_native(poly: &Poly11, z: Fq) -> Fq {
    poly.iter()
        .rev()
        .fold(Fq::zero(), |acc, &coeff| acc * z + coeff)
}

/// Evaluates a degree-10 polynomial at challenge point z in Fq
pub fn eval_poly10_native(poly: &Poly10, z: Fq) -> Fq {
    poly.iter()
        .rev()
        .fold(Fq::zero(), |acc, &coeff| acc * z + coeff)
}

/// Multiplies two degree-11 polynomials to produce a degree-22 product
pub fn poly_mul_deg11_native(a: &Poly11, b: &Poly11) -> [Fq; 23] {
    let mut prod = [Fq::zero(); 23];
    for i in 0..12 {
        for j in 0..12 {
            prod[i + j] += a[i] * b[j];
        }
    }
    prod
}

/// Divides a degree-22 polynomial by M(X) = X^12 - 18X^6 + 82
/// Returns quotient Q of degree 10, remainder R of degree 11
pub fn poly_div_by_M_native(p: &[Fq; 23]) -> (Poly10, Poly11) {
    let mut rem = *p;
    let mut q = [Fq::zero(); 11];

    let eighteen = Fq::from(M_COEFF_6);
    let eighty_two = Fq::from(M_COEFF_0);

    for i in (12..=22).rev() {
        let lead = rem[i];
        q[i - 12] = lead;
        rem[i] = Fq::zero();

        rem[i - 6] += eighteen * lead;
        rem[i - 12] -= eighty_two * lead;
    }

    let mut r = [Fq::zero(); 12];
    r.copy_from_slice(&rem[0..12]);
    (q, r)
}

/// Scaling factor w in F_{p^6}: odd degree coefficients are zero
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScalingFactorFp6 {
    pub w0: Fq,
    pub w2: Fq,
    pub w4: Fq,
    pub w6: Fq,
    pub w8: Fq,
    pub w10: Fq,
}

impl ScalingFactorFp6 {
    pub fn one() -> Self {
        Self {
            w0: Fq::one(),
            w2: Fq::zero(),
            w4: Fq::zero(),
            w6: Fq::zero(),
            w8: Fq::zero(),
            w10: Fq::zero(),
        }
    }

    pub fn to_poly11(&self) -> Poly11 {
        [
            self.w0,
            Fq::zero(),
            self.w2,
            Fq::zero(),
            self.w4,
            Fq::zero(),
            self.w6,
            Fq::zero(),
            self.w8,
            Fq::zero(),
            self.w10,
            Fq::zero(),
        ]
    }

    pub fn to_fq12(&self) -> Fq12 {
        poly11_to_fq12(&self.to_poly11())
    }
}

/// A witness record for one polynomial step: A(X) * B(X) = Q(X) * M(X) + C(X)
#[derive(Clone, Debug)]
pub struct StepWitness {
    pub name: &'static str,
    pub a: Fq12,
    pub b: Fq12,
    pub c: Fq12,
    pub q: Poly10,
}

pub fn record_mul(name: &'static str, a: Fq12, b: Fq12) -> StepWitness {
    let c = a * b;
    let a_poly = fq12_to_poly11(&a);
    let b_poly = fq12_to_poly11(&b);
    let prod = poly_mul_deg11_native(&a_poly, &b_poly);
    let (q_poly, _rem) = poly_div_by_M_native(&prod);
    StepWitness {
        name,
        a,
        b,
        c,
        q: q_poly,
    }
}

// ============================================================================
// Proving Pairing Chip (In-Circuit Implementation)
// ============================================================================

/// Chip for verifying pairing relations via hinted polynomial evaluations.
pub struct ProvingPairingChip<'chip, F: BigPrimeField> {
    pub fp_chip: &'chip FpChip<'chip, F>,
}

impl<'chip, F: BigPrimeField> ProvingPairingChip<'chip, F> {
    pub fn new(fp_chip: &'chip FpChip<'chip, F>) -> Self {
        Self { fp_chip }
    }

    /// Loads a degree-11 polynomial (12 coefficients in Fq) as private witnesses
    pub fn load_private_poly11(
        &self,
        ctx: &mut Context<F>,
        poly: &Poly11,
    ) -> Vec<FpPoint<F>> {
        poly.iter()
            .map(|&c| self.fp_chip.load_private(ctx, c))
            .collect()
    }

    /// Loads a degree-10 polynomial (11 coefficients in Fq) as private witnesses
    pub fn load_private_poly10(
        &self,
        ctx: &mut Context<F>,
        poly: &Poly10,
    ) -> Vec<FpPoint<F>> {
        poly.iter()
            .map(|&c| self.fp_chip.load_private(ctx, c))
            .collect()
    }

    /// Precomputes powers of challenge z: [1, z, z^2, ..., z^11]
    pub fn compute_z_powers(
        &self,
        ctx: &mut Context<F>,
        z: &FpPoint<F>,
    ) -> Vec<FpPoint<F>> {
        let one = self.fp_chip.load_constant(ctx, Fq::one());
        let mut powers = Vec::with_capacity(12);
        powers.push(one);
        powers.push(z.clone());

        for i in 2..12 {
            let next = self.fp_chip.mul(ctx, &powers[i - 1], z);
            powers.push(next);
        }
        powers
    }

    /// Evaluates M(z) = z^12 - 18*z^6 + 82 in-circuit
    pub fn eval_M(
        &self,
        ctx: &mut Context<F>,
        z_powers: &[FpPoint<F>],
    ) -> FpPoint<F> {
        let z6 = &z_powers[6];
        let z12 = self.fp_chip.mul(ctx, z6, z6);

        let eighteen = self.fp_chip.load_constant(ctx, Fq::from(M_COEFF_6));
        let eighty_two = self.fp_chip.load_constant(ctx, Fq::from(M_COEFF_0));

        let term1 = self.fp_chip.mul(ctx, &eighteen, z6);
        let sub = self.fp_chip.sub_no_carry(ctx, &z12, &term1);
        let add = self.fp_chip.add_no_carry(ctx, &sub, &eighty_two);
        self.fp_chip.carry_mod(ctx, add)
    }

    /// Evaluates a degree-11 polynomial at challenge point z using precomputed z powers
    pub fn eval_poly11_at_z(
        &self,
        ctx: &mut Context<F>,
        poly: &[FpPoint<F>],
        z_powers: &[FpPoint<F>],
    ) -> FpPoint<F> {
        assert_eq!(poly.len(), 12);
        assert_eq!(z_powers.len(), 12);

        // sum_{j=0}^{11} poly[j] * z^j
        let mut sum = self.fp_chip.mul(ctx, &poly[0], &z_powers[0]);
        for j in 1..12 {
            let term = self.fp_chip.mul(ctx, &poly[j], &z_powers[j]);
            let sum_nocarry = self.fp_chip.add_no_carry(ctx, &sum, &term);
            sum = self.fp_chip.carry_mod(ctx, sum_nocarry);
        }
        sum
    }

    /// Evaluates a degree-10 polynomial at challenge point z
    pub fn eval_poly10_at_z(
        &self,
        ctx: &mut Context<F>,
        poly: &[FpPoint<F>],
        z_powers: &[FpPoint<F>],
    ) -> FpPoint<F> {
        assert_eq!(poly.len(), 11);

        let mut sum = self.fp_chip.mul(ctx, &poly[0], &z_powers[0]);
        for j in 1..11 {
            let term = self.fp_chip.mul(ctx, &poly[j], &z_powers[j]);
            let sum_nocarry = self.fp_chip.add_no_carry(ctx, &sum, &term);
            sum = self.fp_chip.carry_mod(ctx, sum_nocarry);
        }
        sum
    }

    /// Evaluates an assigned Fp2 element (c0, c1) at challenge z using u = z^6 - 9
    pub fn eval_fp2_at_z(
        &self,
        ctx: &mut Context<F>,
        pt: &FqPoint<F>,
        z6_minus_9: &FpPoint<F>,
    ) -> FpPoint<F> {
        assert_eq!(pt.0.len(), 2);
        let c0 = &pt[0];
        let c1 = &pt[1];

        // pt(z) = c0 + c1 * (z^6 - 9)
        let c1_u = self.fp_chip.mul(ctx, c1, z6_minus_9);
        let res = self.fp_chip.add_no_carry(ctx, c0, &c1_u);
        self.fp_chip.carry_mod(ctx, res)
    }

    /// Evaluates dynamic line (doubling) at challenge point z for non-fixed P and Q
    /// Doubling line output format: [Some(out0), None, None, Some(out3), Some(out4), None]
    /// Line(z) = out0(z) + out3(z)*z^3 + out4(z)*z^4
    pub fn eval_doubling_line_at_z(
        &self,
        ctx: &mut Context<F>,
        line: &[Option<FqPoint<F>>],
        z_powers: &[FpPoint<F>],
        z6_minus_9: &FpPoint<F>,
    ) -> FpPoint<F> {
        let out0 = line[0].as_ref().expect("out0 present");
        let out3 = line[3].as_ref().expect("out3 present");
        let out4 = line[4].as_ref().expect("out4 present");

        let out0_z = self.eval_fp2_at_z(ctx, out0, z6_minus_9);
        let out3_z = self.eval_fp2_at_z(ctx, out3, z6_minus_9);
        let out4_z = self.eval_fp2_at_z(ctx, out4, z6_minus_9);

        let out3_term = self.fp_chip.mul(ctx, &out3_z, &z_powers[3]);
        let out4_term = self.fp_chip.mul(ctx, &out4_z, &z_powers[4]);

        let sum1 = self.fp_chip.add_no_carry(ctx, &out0_z, &out3_term);
        let sum2 = self.fp_chip.add_no_carry(ctx, &sum1, &out4_term);
        self.fp_chip.carry_mod(ctx, sum2)
    }

    /// Evaluates dynamic line (addition) at challenge point z for non-fixed P and Q
    /// Addition line output format: [None, None, Some(out2), Some(out3), None, Some(out5)]
    /// Line(z) = out2(z)*z^2 + out3(z)*z^3 + out5(z)*z^5
    pub fn eval_addition_line_at_z(
        &self,
        ctx: &mut Context<F>,
        line: &[Option<FqPoint<F>>],
        z_powers: &[FpPoint<F>],
        z6_minus_9: &FpPoint<F>,
    ) -> FpPoint<F> {
        let out2 = line[2].as_ref().expect("out2 present");
        let out3 = line[3].as_ref().expect("out3 present");
        let out5 = line[5].as_ref().expect("out5 present");

        let out2_z = self.eval_fp2_at_z(ctx, out2, z6_minus_9);
        let out3_z = self.eval_fp2_at_z(ctx, out3, z6_minus_9);
        let out5_z = self.eval_fp2_at_z(ctx, out5, z6_minus_9);

        let out2_term = self.fp_chip.mul(ctx, &out2_z, &z_powers[2]);
        let out3_term = self.fp_chip.mul(ctx, &out3_z, &z_powers[3]);
        let out5_term = self.fp_chip.mul(ctx, &out5_z, &z_powers[5]);

        let sum1 = self.fp_chip.add_no_carry(ctx, &out2_term, &out3_term);
        let sum2 = self.fp_chip.add_no_carry(ctx, &sum1, &out5_term);
        self.fp_chip.carry_mod(ctx, sum2)
    }

    /// Soundness Check: Constrains subfield scaling factor w to F_{p^6}
    /// (enforces all odd degree coefficients w_1, w_3, w_5, w_7, w_9, w_11 == 0).
    pub fn verify_subfield_fp6(
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

    /// Soundness Check: Verifies c(z) * c^-1(z) - 1 == Q_inv(z) * M(z)
    pub fn verify_invertibility(
        &self,
        ctx: &mut Context<F>,
        c_z: &FpPoint<F>,
        c_inv_z: &FpPoint<F>,
        q_inv_z: &FpPoint<F>,
        m_z: &FpPoint<F>,
    ) {
        let prod = self.fp_chip.mul(ctx, c_z, c_inv_z);
        let one = self.fp_chip.load_constant(ctx, Fq::one());
        let lhs = self.fp_chip.sub_no_carry(ctx, &prod, &one);
        let lhs_norm = self.fp_chip.carry_mod(ctx, lhs);

        let rhs = self.fp_chip.mul(ctx, q_inv_z, m_z);
        self.fp_chip.assert_equal(ctx, &lhs_norm, &rhs);
    }

    /// Verifies the batched Schwartz-Zippel RLC check at challenge z:
    ///   sum_i alpha^i * [ A_i(z) * B_i(z) - C_i(z) ] == big_Q(z) * M(z)
    pub fn verify_batched_schwartz_zippel(
        &self,
        ctx: &mut Context<F>,
        a_evals: &[FpPoint<F>],
        b_evals: &[FpPoint<F>],
        c_evals: &[FpPoint<F>],
        alpha: &FpPoint<F>,
        big_q_z: &FpPoint<F>,
        m_z: &FpPoint<F>,
    ) {
        let n = a_evals.len();
        assert_eq!(b_evals.len(), n);
        assert_eq!(c_evals.len(), n);

        let one = self.fp_chip.load_constant(ctx, Fq::one());
        let mut curr_alpha = one;
        let mut lhs = self.fp_chip.load_constant(ctx, Fq::zero());

        for i in 0..n {
            let ab = self.fp_chip.mul(ctx, &a_evals[i], &b_evals[i]);
            let diff = self.fp_chip.sub_no_carry(ctx, &ab, &c_evals[i]);
            let diff_norm = self.fp_chip.carry_mod(ctx, diff);
            let term = self.fp_chip.mul(ctx, &curr_alpha, &diff_norm);

            let new_lhs = self.fp_chip.add_no_carry(ctx, &lhs, &term);
            lhs = self.fp_chip.carry_mod(ctx, new_lhs);

            if i + 1 < n {
                curr_alpha = self.fp_chip.mul(ctx, &curr_alpha, alpha);
            }
        }

        let rhs = self.fp_chip.mul(ctx, big_q_z, m_z);
        self.fp_chip.assert_equal(ctx, &lhs, &rhs);
    }

    /// Verifies that the final accumulator equals 1 in F_{p^12}
    pub fn verify_final_accumulator_is_one(
        &self,
        ctx: &mut Context<F>,
        final_acc_poly: &[FpPoint<F>],
    ) {
        assert_eq!(final_acc_poly.len(), 12);
        let one = self.fp_chip.load_constant(ctx, Fq::one());
        let zero = self.fp_chip.load_constant(ctx, Fq::zero());

        self.fp_chip.assert_equal(ctx, &final_acc_poly[0], &one);
        for i in 1..12 {
            self.fp_chip.assert_equal(ctx, &final_acc_poly[i], &zero);
        }
    }
}
