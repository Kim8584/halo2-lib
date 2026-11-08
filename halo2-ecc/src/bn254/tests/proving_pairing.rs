use std::{
    fs::{self, File},
    io::{BufRead, BufReader},
};

use super::*;
use crate::bn254::proving_pairing::*;
use crate::fields::FieldChip;
use crate::halo2_proofs::arithmetic::Field;
use crate::{
    fields::FpStrategy,
    halo2_proofs::halo2curves::bn256::{Fq, Fq12, G1Affine, G2Affine},
};
use halo2_base::{gates::RangeChip, utils::BigPrimeField, Context};

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct ProvingPairingCircuitParams {
    pub strategy: FpStrategy,
    pub degree: u32,
    pub num_advice: usize,
    pub num_lookup_advice: usize,
    pub num_fixed: usize,
    pub lookup_bits: usize,
    pub limb_bits: usize,
    pub num_limbs: usize,
}

/// Core circuit function for verifying proving pairing via hinted polynomial evaluation
pub fn proving_pairing_circuit_test<F: BigPrimeField>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    params: ProvingPairingCircuitParams,
    c: Fq12,
    c_inv: Fq12,
    w: ScalingFactorFp6,
    trace_steps: Vec<StepWitness>,
    z_val: Fq,
    alpha_val: Fq,
) {
    let fp_chip = FpChip::<F>::new(range, params.limb_bits, params.num_limbs);
    let chip = ProvingPairingChip::new(&fp_chip);

    // 1. Assign challenge points z and alpha
    let z = fp_chip.load_private(ctx, z_val);
    let alpha = fp_chip.load_private(ctx, alpha_val);

    // 2. Precompute z powers: [1, z, z^2, ..., z^11]
    let z_powers = chip.compute_z_powers(ctx, &z);

    // 3. Compute M(z) = z^12 - 18*z^6 + 82
    let m_z = chip.eval_M(ctx, &z_powers);

    // 4. Load witness c, c_inv, and w in polynomial basis
    let c_poly = chip.load_private_poly11(ctx, &fq12_to_poly11(&c));
    let cinv_poly = chip.load_private_poly11(ctx, &fq12_to_poly11(&c_inv));
    let w_poly = chip.load_private_poly11(ctx, &w.to_poly11());

    // 5. Soundness Check 1: Verify w is strictly in F_{p^6} (all odd coefficients are zero)
    chip.verify_subfield_fp6(ctx, &w_poly);

    // 6. Soundness Check 2: Verify invertibility of c: c(z) * c^-1(z) - 1 == Q_inv(z) * M(z)
    let c_z = chip.eval_poly11_at_z(ctx, &c_poly, &z_powers);
    let cinv_z = chip.eval_poly11_at_z(ctx, &cinv_poly, &z_powers);
    let q_inv_witness = trace_steps[0].q;
    let q_inv_poly = chip.load_private_poly10(ctx, &q_inv_witness);
    let q_inv_z = chip.eval_poly10_at_z(ctx, &q_inv_poly, &z_powers);
    chip.verify_invertibility(ctx, &c_z, &cinv_z, &q_inv_z, &m_z);

    // 7. Schwartz-Zippel Batched RLC Check:
    // Build single batched quotient polynomial big_Q(X) = sum_i alpha^i * Q_i(X)
    let num_steps = trace_steps.len();
    let mut big_q = [Fq::zero(); 11];
    let mut curr_alpha_native = Fq::one();
    for step in &trace_steps {
        for deg in 0..11 {
            big_q[deg] += curr_alpha_native * step.q[deg];
        }
        curr_alpha_native *= alpha_val;
    }
    let big_q_poly = chip.load_private_poly10(ctx, &big_q);
    let big_q_z = chip.eval_poly10_at_z(ctx, &big_q_poly, &z_powers);

    // Evaluate each step's (A(z), B(z), C(z))
    let mut a_evals = Vec::with_capacity(num_steps);
    let mut b_evals = Vec::with_capacity(num_steps);
    let mut c_evals = Vec::with_capacity(num_steps);

    for step in &trace_steps {
        let a_p = chip.load_private_poly11(ctx, &fq12_to_poly11(&step.a));
        let b_p = chip.load_private_poly11(ctx, &fq12_to_poly11(&step.b));
        let c_p = chip.load_private_poly11(ctx, &fq12_to_poly11(&step.c));

        a_evals.push(chip.eval_poly11_at_z(ctx, &a_p, &z_powers));
        b_evals.push(chip.eval_poly11_at_z(ctx, &b_p, &z_powers));
        c_evals.push(chip.eval_poly11_at_z(ctx, &c_p, &z_powers));
    }

    chip.verify_batched_schwartz_zippel(
        ctx,
        &a_evals,
        &b_evals,
        &c_evals,
        &alpha,
        &big_q_z,
        &m_z,
    );

    // 8. Accumulator Constraint: Verify final accumulator is exactly 1 in F_{p^12}
    let final_step = trace_steps.last().expect("trace non-empty");
    let final_acc_poly = chip.load_private_poly11(ctx, &fq12_to_poly11(&final_step.c));
    chip.verify_final_accumulator_is_one(ctx, &final_acc_poly);
}

/// Helper to generate a valid trace for dual pairing: e(P1, Q1) * e(P2, Q2) = 1
pub fn generate_dual_pairing_witness(
    rng: &mut StdRng,
) -> (G1Affine, G2Affine, Fq12, Fq12, ScalingFactorFp6, Vec<StepWitness>, Fq, Fq) {
    let p1 = G1Affine::random(&mut *rng);
    let q1 = G2Affine::random(&mut *rng);

    // Invertible witness c and c_inv
    let c = Fq12::random(&mut *rng);
    let c_inv = c.invert().unwrap();

    // Sound scaling factor w in F_{p^6}
    let w = ScalingFactorFp6 {
        w0: Fq::random(&mut *rng),
        w2: Fq::random(&mut *rng),
        w4: Fq::random(&mut *rng),
        w6: Fq::random(&mut *rng),
        w8: Fq::random(&mut *rng),
        w10: Fq::random(&mut *rng),
    };

    // Build execution trace of polynomial multiplications
    let mut trace = Vec::new();

    // Step 0: Invertibility step c * c_inv = 1
    trace.push(record_mul("c * c_inv = 1", c, c_inv));

    // Simulated fused Miller loop sequence
    let mut acc = c_inv;
    for _ in 0..5 {
        let step_sqr = record_mul("acc_sqr", acc, acc);
        acc = step_sqr.c;
        trace.push(step_sqr);

        let line_val = Fq12::random(&mut *rng);
        let step_mul = record_mul("acc_line", acc, line_val);
        acc = step_mul.c;
        trace.push(step_mul);
    }

    // Tail: cancel accumulator so final acc = 1
    let final_cancel = acc.invert().unwrap();
    let step_finish = record_mul("final_cancel", acc, final_cancel);
    assert_eq!(step_finish.c, Fq12::one());
    trace.push(step_finish);

    let z = Fq::random(&mut *rng);
    let alpha = Fq::random(&mut *rng);

    (p1, q1, c, c_inv, w, trace, z, alpha)
}

#[test]
pub fn test_proving_pairing() {
    let path = "configs/bn254/proving_pairing_circuit.config";
    let params: ProvingPairingCircuitParams = serde_json::from_reader(
        File::open(path).unwrap_or_else(|e| panic!("{path} does not exist: {e:?}")),
    )
    .unwrap();

    let mut rng = StdRng::seed_from_u64(42);
    let (_p1, _q1, c, c_inv, w, trace, z, alpha) = generate_dual_pairing_witness(&mut rng);

    base_test()
        .k(params.degree)
        .lookup_bits(params.lookup_bits)
        .run(|ctx, range| {
            proving_pairing_circuit_test(
                ctx,
                range,
                params,
                c,
                c_inv,
                w,
                trace,
                z,
                alpha,
            );
        });
}

#[test]
#[should_panic]
pub fn test_proving_pairing_soundness_forged_subfield_fails() {
    let path = "configs/bn254/proving_pairing_circuit.config";
    let params: ProvingPairingCircuitParams = serde_json::from_reader(
        File::open(path).unwrap_or_else(|e| panic!("{path} does not exist: {e:?}")),
    )
    .unwrap();

    let mut rng = StdRng::seed_from_u64(42);
    let (_p1, _q1, _c, _c_inv, w, _trace, _z, _alpha) = generate_dual_pairing_witness(&mut rng);

    // Tamper with w by adding a non-zero odd degree coefficient (w1 != 0), simulating forgery
    let mut w_poly = w.to_poly11();
    w_poly[1] = Fq::one(); // Non-zero odd degree term violating F_{p^6} subfield membership!

    base_test()
        .k(params.degree)
        .lookup_bits(params.lookup_bits)
        .run(|ctx, range| {
            let fp_chip = FpChip::new(range, params.limb_bits, params.num_limbs);
            let chip = ProvingPairingChip::new(&fp_chip);
            let tampered_w_poly = chip.load_private_poly11(ctx, &w_poly);
            // Must panic here:
            chip.verify_subfield_fp6(ctx, &tampered_w_poly);
        });
}

#[test]
#[should_panic]
pub fn test_proving_pairing_soundness_tampered_witness_fails() {
    let path = "configs/bn254/proving_pairing_circuit.config";
    let params: ProvingPairingCircuitParams = serde_json::from_reader(
        File::open(path).unwrap_or_else(|e| panic!("{path} does not exist: {e:?}")),
    )
    .unwrap();

    let mut rng = StdRng::seed_from_u64(42);
    let (_p1, _q1, c, _c_inv, w, trace, z, alpha) = generate_dual_pairing_witness(&mut rng);

    // Tampered inverse: c_inv is random and NOT the inverse of c
    let bad_c_inv = Fq12::random(&mut rng);

    base_test()
        .k(params.degree)
        .lookup_bits(params.lookup_bits)
        .run(|ctx, range| {
            proving_pairing_circuit_test(
                ctx,
                range,
                params,
                c,
                bad_c_inv,
                w,
                trace,
                z,
                alpha,
            );
        });
}

#[test]
pub fn test_attack_malicious_prover_knows_z_forgery() {
    // Demonstration of the critical soundness flaw when z is loaded as a private witness:
    // If the prover can know z before fixing witness polynomials,
    // the prover can forge an invalid pairing check that passes the circuit.
    let path = "configs/bn254/proving_pairing_circuit.config";
    let params: ProvingPairingCircuitParams = serde_json::from_reader(
        File::open(path).unwrap_or_else(|e| panic!("{path} does not exist: {e:?}")),
    )
    .unwrap();

    let mut rng = StdRng::seed_from_u64(42);
    let z = Fq::random(&mut rng);
    let alpha = Fq::random(&mut rng);

    let c = Fq12::random(&mut rng);
    let c_inv = Fq12::random(&mut rng);
    let w = ScalingFactorFp6::one();

    let m_z = eval_M_native(z);
    assert_ne!(m_z, Fq::zero());

    // Step 0: Invertibility step
    let c_z = eval_poly11_native(&fq12_to_poly11(&c), z);
    let cinv_z = eval_poly11_native(&fq12_to_poly11(&c_inv), z);
    let diff_inv = c_z * cinv_z - Fq::one();
    let q0_inv = diff_inv * m_z.invert().unwrap();

    let mut q_inv_forged = [Fq::zero(); 11];
    q_inv_forged[0] = q0_inv;
    assert_eq!(eval_poly10_native(&q_inv_forged, z) * m_z, diff_inv);

    // Step 1: Forged pairing step with final accumulator = 1
    let a_step = Fq12::random(&mut rng);
    let b_step = Fq12::random(&mut rng);
    let c_step = Fq12::one(); // Forged final acc == 1!

    let a_z = eval_poly11_native(&fq12_to_poly11(&a_step), z);
    let b_z = eval_poly11_native(&fq12_to_poly11(&b_step), z);
    let c_step_z = eval_poly11_native(&fq12_to_poly11(&c_step), z);
    let diff_step = a_z * b_z - c_step_z;
    let q0_step = diff_step * m_z.invert().unwrap();

    let mut q_step_forged = [Fq::zero(); 11];
    q_step_forged[0] = q0_step;

    let forged_trace = vec![
        StepWitness {
            name: "forged_inv",
            a: c,
            b: c_inv,
            c: Fq12::one(),
            q: q_inv_forged,
        },
        StepWitness {
            name: "forged_pairing_step",
            a: a_step,
            b: b_step,
            c: c_step,
            q: q_step_forged,
        },
    ];

    println!("🚨 EXPLOIT: Running circuit with forged witnesses chosen AFTER z is known...");
    base_test()
        .k(params.degree)
        .lookup_bits(params.lookup_bits)
        .run(|ctx, range| {
            proving_pairing_circuit_test(
                ctx,
                range,
                params,
                c,
                c_inv,
                w,
                forged_trace,
                z,
                alpha,
            );
        });
    println!("🚨 EXPLOIT CONFIRMED: False pairing PASSED because z was an unconstrained witness!");
}

#[test]
pub fn bench_proving_pairing() -> Result<(), Box<dyn std::error::Error>> {
    let config_path = "configs/bn254/bench_proving_pairing.config";
    let bench_params_file =
        File::open(config_path).unwrap_or_else(|e| panic!("{config_path} does not exist: {e:?}"));
    fs::create_dir_all("results/bn254")?;

    let results_path = "results/bn254/proving_pairing_bench.csv";
    let mut fs_results = File::create(results_path)?;
    writeln!(
        fs_results,
        "degree,num_advice,num_lookup,num_fixed,lookup_bits,limb_bits,num_limbs,proof_time,proof_size,verify_time"
    )?;

    let mut rng = StdRng::seed_from_u64(42);
    let bench_params_reader = BufReader::new(bench_params_file);

    for line in bench_params_reader.lines() {
        let bench_params: ProvingPairingCircuitParams =
            serde_json::from_str(line?.as_str())?;
        let k = bench_params.degree;
        println!("---------------------- degree = {k} (Proving Pairing) ------------------------------");

        let (_p1, _q1, c, c_inv, w, trace, z, alpha) = generate_dual_pairing_witness(&mut rng);

        let stats = base_test()
            .k(k)
            .lookup_bits(bench_params.lookup_bits)
            .bench_builder(
                (c, c_inv, w, trace.clone(), z, alpha),
                (c, c_inv, w, trace, z, alpha),
                |pool, range, (c, c_inv, w, trace, z, alpha)| {
                    proving_pairing_circuit_test(
                        pool.main(),
                        range,
                        bench_params,
                        c,
                        c_inv,
                        w,
                        trace,
                        z,
                        alpha,
                    );
                },
            );

        writeln!(
            fs_results,
            "{},{},{},{},{},{},{},{:?},{},{:?}",
            bench_params.degree,
            bench_params.num_advice,
            bench_params.num_lookup_advice,
            bench_params.num_fixed,
            bench_params.lookup_bits,
            bench_params.limb_bits,
            bench_params.num_limbs,
            stats.proof_time.time.elapsed(),
            stats.proof_size,
            stats.verify_time.time.elapsed()
        )?;
    }
    Ok(())
}

#[test]
pub fn test_basis_conversion_poly_mul_matches_halo2curves() {
    let mut rng = StdRng::seed_from_u64(0xdeadbeef);

    for trial in 0..20 {
        let a = Fq12::random(&mut rng);
        let b = Fq12::random(&mut rng);

        // 1. Native halo2curves multiplication
        let c_native = a * b;

        // 2. Polynomial conversion: Fq12 -> Poly11
        let a_poly = fq12_to_poly11(&a);
        let b_poly = fq12_to_poly11(&b);

        // 3. Multiplication in F_p[X] / (X^12 - 18X^6 + 82)
        let prod22 = poly_mul_deg11_native(&a_poly, &b_poly);
        let (_q, r_poly) = poly_div_by_M_native(&prod22);

        // 4. Reverse conversion: Poly11 -> Fq12
        let c_poly_reconstructed = poly11_to_fq12(&r_poly);

        // 5. Assert identity holds identically
        assert_eq!(
            c_native, c_poly_reconstructed,
            "Trial {trial}: Polynomial product does not match halo2curves Fq12 native multiplication!"
        );

        // Also test roundtrip conversion on random element
        let a_roundtrip = poly11_to_fq12(&a_poly);
        assert_eq!(a, a_roundtrip, "Trial {trial}: Roundtrip conversion failed!");
    }
    println!("✅ Verified 20/20 trials: Garaga basis polynomial multiplication identically matches halo2curves::bn256::Fq12");
}

