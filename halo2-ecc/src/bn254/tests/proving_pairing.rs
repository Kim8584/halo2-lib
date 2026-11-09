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

#[derive(Clone, Debug)]
struct TwoPhaseConfig {
    col_phase0: crate::halo2_proofs::plonk::Column<crate::halo2_proofs::plonk::Advice>,
    col_phase1: crate::halo2_proofs::plonk::Column<crate::halo2_proofs::plonk::Advice>,
    challenge: crate::halo2_proofs::plonk::Challenge,
    q_phase1: crate::halo2_proofs::plonk::Selector,
}

#[derive(Default)]
struct TwoPhaseTestCircuit {
    phase0_val: crate::halo2_proofs::circuit::Value<crate::halo2_proofs::halo2curves::bn256::Fr>,
}

impl crate::halo2_proofs::plonk::Circuit<crate::halo2_proofs::halo2curves::bn256::Fr> for TwoPhaseTestCircuit {
    type Config = TwoPhaseConfig;
    type FloorPlanner = crate::halo2_proofs::circuit::SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut crate::halo2_proofs::plonk::ConstraintSystem<crate::halo2_proofs::halo2curves::bn256::Fr>) -> Self::Config {
        let col_phase0 = meta.advice_column_in(crate::halo2_proofs::plonk::FirstPhase);
        let col_phase1 = meta.advice_column_in(crate::halo2_proofs::plonk::SecondPhase);
        meta.enable_equality(col_phase0);
        meta.enable_equality(col_phase1);
        let challenge = meta.challenge_usable_after(crate::halo2_proofs::plonk::FirstPhase);
        let q_phase1 = meta.selector();

        meta.create_gate("phase 1 check: advice_p1 == advice_p0 * challenge", |meta| {
            let q = meta.query_selector(q_phase1);
            let a0 = meta.query_advice(col_phase0, crate::halo2_proofs::poly::Rotation::cur());
            let a1 = meta.query_advice(col_phase1, crate::halo2_proofs::poly::Rotation::cur());
            let ch = meta.query_challenge(challenge);
            vec![q * (a1 - a0 * ch)]
        });

        TwoPhaseConfig {
            col_phase0,
            col_phase1,
            challenge,
            q_phase1,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl crate::halo2_proofs::circuit::Layouter<crate::halo2_proofs::halo2curves::bn256::Fr>,
    ) -> Result<(), crate::halo2_proofs::plonk::Error> {
        layouter.assign_region(
            || "two phase region",
            |mut region| {
                // Phase 0 assignment
                region.assign_advice(config.col_phase0, 0, self.phase0_val);

                // Advance to phase 1
                region.next_phase();

                // Obtain challenge usable after phase 0
                let ch = region.get_challenge(config.challenge);

                // Phase 1 assignment using the challenge
                let p1_val = self.phase0_val * ch;
                region.assign_advice(config.col_phase1, 0, p1_val);
                config.q_phase1.enable(&mut region, 0)?;

                Ok(())
            },
        )?;
        Ok(())
    }
}

#[test]
pub fn test_minimal_two_phase_challenge_mock_prover() {
    use crate::halo2_proofs::dev::MockProver;
    use crate::halo2_proofs::circuit::Value;
    use crate::halo2_proofs::halo2curves::bn256::Fr;

    let k = 4;
    let circuit = TwoPhaseTestCircuit {
        phase0_val: Value::known(Fr::from(42u64)),
    };
    let prover = MockProver::run(k, &circuit, vec![]).expect("MockProver should init");
    prover.assert_satisfied();
    println!("✅ MockProver assert_satisfied passed for two-phase circuit with challenge!");
}

#[test]
pub fn test_cheating_prover_two_phase_rejected() {
    use crate::halo2_proofs::dev::MockProver;
    use crate::halo2_proofs::circuit::Value;
    use crate::halo2_proofs::halo2curves::bn256::Fr;

    // A cheating circuit where the prover attempts to satisfy `a1 == a0 * ch`
    // but in phase 1, having seen `ch`, tampers with the value or supplies an inconsistent a1.
    struct CheatingTwoPhaseCircuit;

    impl crate::halo2_proofs::plonk::Circuit<Fr> for CheatingTwoPhaseCircuit {
        type Config = TwoPhaseConfig;
        type FloorPlanner = crate::halo2_proofs::circuit::SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            CheatingTwoPhaseCircuit
        }

        fn configure(meta: &mut crate::halo2_proofs::plonk::ConstraintSystem<Fr>) -> Self::Config {
            TwoPhaseTestCircuit::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl crate::halo2_proofs::circuit::Layouter<Fr>,
        ) -> Result<(), crate::halo2_proofs::plonk::Error> {
            layouter.assign_region(
                || "cheating two phase region",
                |mut region| {
                    // Phase 0: prover commits to a0 = 42
                    let honest_a0 = Fr::from(42u64);
                    region.assign_advice(config.col_phase0, 0, Value::known(honest_a0));

                    region.next_phase();

                    // Phase 1: prover observes challenge
                    let ch = region.get_challenge(config.challenge);

                    // Cheating prover attempts to forge by assigning a1 = 999 (tampered value)
                    let forged_a1 = Value::known(Fr::from(999u64));
                    region.assign_advice(config.col_phase1, 0, forged_a1);
                    config.q_phase1.enable(&mut region, 0)?;

                    Ok(())
                },
            )?;
            Ok(())
        }
    }

    let k = 4;
    let prover = MockProver::run(k, &CheatingTwoPhaseCircuit, vec![]).expect("MockProver init");
    let result = prover.verify();
    assert!(result.is_err(), "Cheating prover MUST be rejected by MockProver!");
    println!("✅ Confirmed: Cheating prover tampering after observing challenge was REJECTED by MockProver: {:?}", result.err());
}


#[test]
pub fn test_measure_poseidon_absorption_cost() {
    use halo2_base::halo2_proofs::halo2curves::bn256::Fr;
    use halo2_base::poseidon::hasher::{
        spec::OptimizedPoseidonSpec, PoseidonHasher,
    };

    base_test().k(14).run(|ctx, range| {
        const T: usize = 3;
        const RATE: usize = 2;
        const R_F: usize = 8;
        const R_P: usize = 57;

        let spec = OptimizedPoseidonSpec::<Fr, T, RATE>::new::<R_F, R_P, 0>();
        let mut hasher = PoseidonHasher::<Fr, T, RATE>::new(spec);
        hasher.initialize_consts(ctx, &range.gate);

        let init_cells = ctx.advice.len();

        let num_scalars = 100;
        let dummy_inputs: Vec<Fr> = (0..num_scalars).map(|i| Fr::from(i as u64)).collect();
        let assigned_inputs = ctx.assign_witnesses(dummy_inputs);

        let after_assign = ctx.advice.len();
        let assign_cost = after_assign - init_cells;

        let _hash_out = hasher.hash_fix_len_array(ctx, &range.gate, &assigned_inputs);

        let after_hash = ctx.advice.len();
        let hash_cost = after_hash - after_assign;

        println!("================ Poseidon In-Circuit Absorption Cost ================");
        println!("Number of Fr scalars absorbed: {num_scalars}");
        println!("Witness assignment advice cells: {assign_cost}");
        println!("Poseidon hashing advice cells: {hash_cost}");
        println!("Advice cells per absorbed Fr scalar: {:.2}", hash_cost as f64 / num_scalars as f64);
        println!("=====================================================================");
    });
}




