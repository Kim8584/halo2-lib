use halo2_base::halo2_proofs::halo2curves::bn256::Fq;
use halo2_base::halo2_proofs::arithmetic::Field;

/// Minimal polynomial modulus M(X) = X^12 - 18*X^6 + 82
pub const M_COEFF_6: u64 = 18;
pub const M_COEFF_0: u64 = 82;

pub type Poly11 = [Fq; 12];
pub type Poly10 = [Fq; 11];
pub type Poly22 = [Fq; 23];

/// Evaluates M(z) = z^12 - 18*z^6 + 82 natively
pub fn eval_M(z: Fq) -> Fq {
    let z2 = z.square();
    let z6 = z2.square() * z2;
    let z12 = z6.square();
    let eighteen = Fq::from(M_COEFF_6);
    let eighty_two = Fq::from(M_COEFF_0);
    z12 - eighteen * z6 + eighty_two
}

/// Evaluates a degree-11 polynomial at challenge point z using Horner's rule
pub fn eval_poly11(poly: &Poly11, z: Fq) -> Fq {
    poly.iter()
        .rev()
        .fold(Fq::zero(), |acc, &coeff| acc * z + coeff)
}

/// Evaluates a degree-10 polynomial at challenge point z using Horner's rule
pub fn eval_poly10(poly: &Poly10, z: Fq) -> Fq {
    poly.iter()
        .rev()
        .fold(Fq::zero(), |acc, &coeff| acc * z + coeff)
}

/// Multiplies two degree-11 polynomials to produce a degree-22 product
pub fn poly_mul_deg11(a: &Poly11, b: &Poly11) -> Poly22 {
    let mut prod = [Fq::zero(); 23];
    for i in 0..12 {
        for j in 0..12 {
            prod[i + j] += a[i] * b[j];
        }
    }
    prod
}

/// Computes a - b for degree-11 polynomials
pub fn poly_sub_deg11(a: &Poly11, b: &Poly11) -> Poly11 {
    let mut out = [Fq::zero(); 12];
    for i in 0..12 {
        out[i] = a[i] - b[i];
    }
    out
}

/// Divides a degree-22 polynomial by M(X) = X^12 - 18X^6 + 82
/// Returns (quotient of degree 10, remainder of degree 11)
pub fn poly_div_by_M(p: &Poly22) -> (Poly10, Poly11) {
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

/// Combines two error polynomials E0(X) and E1(X) using challenge rho:
/// R_rho(X) = E0(X) + rho * E1(X)
pub fn combine_errors_deg22(e0: &Poly22, e1: &Poly22, rho: Fq) -> Poly22 {
    let mut out = [Fq::zero(); 23];
    for i in 0..23 {
        out[i] = e0[i] + rho * e1[i];
    }
    out
}
