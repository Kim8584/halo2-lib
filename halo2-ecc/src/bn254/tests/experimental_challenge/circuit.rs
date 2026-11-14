use halo2_base::{
    gates::{
        flex_gate::threads::MultiPhaseCoreManager,
        RangeChip,
    },
    halo2_proofs::{
        arithmetic::Field,
        circuit::{Layouter, SimpleFloorPlanner, Value},
        halo2curves::bn256::{Bn256, Fq, Fr, G1Affine},
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ConstraintSystem, Error,
        },
        poly::{
            commitment::ParamsProver,
            kzg::{
                commitment::KZGCommitmentScheme,
                multiopen::{ProverSHPLONK, VerifierSHPLONK},
                strategy::SingleStrategy,
            },
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    },
    utils::BigPrimeField,
    virtual_region::{lookups::LookupAnyManager, manager::VirtualRegionManager},
    Context,
};
use rand::rngs::StdRng;
use rand_core::SeedableRng;

use crate::bn254::{FpChip, FpPoint};
use crate::fields::FieldChip;

use super::{
    challenge::ChallengeConversionChip,
    config::Milestone1Config,
    polynomial::*,
};

pub fn horner_eval_fp<F: BigPrimeField>(
    ctx: &mut Context<F>,
    fp_chip: &FpChip<F>,
    poly: &[FpPoint<F>],
    x: &FpPoint<F>,
) -> FpPoint<F> {
    let mut acc = poly[poly.len() - 1].clone();
    for coeff in poly.iter().rev().skip(1) {
        let mul = fp_chip.mul(ctx, &acc, x);
        let add = fp_chip.add_no_carry(ctx, &mul, coeff);
        acc = fp_chip.carry_mod(ctx, add);
    }
    acc
}

pub fn eval_M_in_circuit<F: BigPrimeField>(
    ctx: &mut Context<F>,
    fp_chip: &FpChip<F>,
    zeta: &FpPoint<F>,
) -> FpPoint<F> {
    let zeta2 = fp_chip.mul(ctx, zeta, zeta);
    let zeta4 = fp_chip.mul(ctx, &zeta2, &zeta2);
    let zeta6 = fp_chip.mul(ctx, &zeta4, &zeta2);
    let zeta12 = fp_chip.mul(ctx, &zeta6, &zeta6);

    let eighteen = fp_chip.load_constant(ctx, Fq::from(M_COEFF_6));
    let eighty_two = fp_chip.load_constant(ctx, Fq::from(M_COEFF_0));

    let term1 = fp_chip.mul(ctx, &eighteen, &zeta6);
    let sub = fp_chip.sub_no_carry(ctx, &zeta12, &term1);
    let add = fp_chip.add_no_carry(ctx, &sub, &eighty_two);
    fp_chip.carry_mod(ctx, add)
}

#[derive(Clone, Debug)]
pub struct Milestone1Circuit {
    pub k: usize,
    pub lookup_bits: usize,
    pub limb_bits: usize,
    pub num_limbs: usize,

    // Phase 0 witness polynomials:
    // Identity 0: A0 * B0 - C0 = Q0 * M
    pub a0: Poly11,
    pub b0: Poly11,
    pub c0: Poly11,

    // Identity 1: A1 * B1 - C1 = Q1 * M
    pub a1: Poly11,
    pub b1: Poly11,
    pub c1: Poly11,

    // Test tamper flag
    pub tamper_q: bool,
}

impl Circuit<Fr> for Milestone1Circuit {
    type Config = Milestone1Config<Fr>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            k: self.k,
            lookup_bits: self.lookup_bits,
            limb_bits: self.limb_bits,
            num_limbs: self.num_limbs,
            a0: [Fq::zero(); 12],
            b0: [Fq::zero(); 12],
            c0: [Fq::zero(); 12],
            a1: [Fq::zero(); 12],
            b1: [Fq::zero(); 12],
            c1: [Fq::zero(); 12],
            tamper_q: false,
        }
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let num_advice_per_phase = vec![25, 25];
        let num_lookup_advice_per_phase = vec![1, 1];
        Milestone1Config::configure(
            meta,
            15, // k = 15
            num_advice_per_phase,
            num_lookup_advice_per_phase,
            14, // lookup_bits = 14
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        config.range_config.load_lookup_table(&mut layouter)?;

        let mut core = MultiPhaseCoreManager::new(false);
        let lookup_manager = [(); 3].map(|_| LookupAnyManager::new(false, core.copy_manager.clone()));
        let range_chip = RangeChip::new(config.range_config.lookup_bits(), lookup_manager);

        // Precompute off-circuit error polynomials and quotients
        let a0_mul_b0 = poly_mul_deg11(&self.a0, &self.b0);
        let mut e0 = a0_mul_b0;
        for i in 0..12 {
            e0[i] -= self.c0[i];
        }
        let (mut q0, _rem0) = poly_div_by_M(&e0);
        if self.tamper_q {
            q0[0] += Fq::one();
        }

        let a1_mul_b1 = poly_mul_deg11(&self.a1, &self.b1);
        let mut e1 = a1_mul_b1;
        for i in 0..12 {
            e1[i] -= self.c1[i];
        }
        let (q1, _rem1) = poly_div_by_M(&e1);

        // --- PHASE 0 ---
        let mut a0_points = Vec::with_capacity(12);
        let mut b0_points = Vec::with_capacity(12);
        let mut c0_points = Vec::with_capacity(12);
        let mut q0_points = Vec::with_capacity(11);

        let mut a1_points = Vec::with_capacity(12);
        let mut b1_points = Vec::with_capacity(12);
        let mut c1_points = Vec::with_capacity(12);
        let mut q1_points = Vec::with_capacity(11);

        {
            let ctx = core.main(0);
            let fp_chip = FpChip::<Fr>::new(&range_chip, self.limb_bits, self.num_limbs);

            for i in 0..12 {
                a0_points.push(fp_chip.load_private(ctx, self.a0[i]));
                b0_points.push(fp_chip.load_private(ctx, self.b0[i]));
                c0_points.push(fp_chip.load_private(ctx, self.c0[i]));
                a1_points.push(fp_chip.load_private(ctx, self.a1[i]));
                b1_points.push(fp_chip.load_private(ctx, self.b1[i]));
                c1_points.push(fp_chip.load_private(ctx, self.c1[i]));
            }
            for i in 0..11 {
                q0_points.push(fp_chip.load_private(ctx, q0[i]));
                q1_points.push(fp_chip.load_private(ctx, q1[i]));
            }
        }

        layouter.assign_region(
            || "Milestone 1 Two-Phase Region",
            |mut region| {
                let usable_rows = config.range_config.gate.max_rows;

                // 1. Assign Phase 0
                core.phase_manager[0].assign_raw(
                    &(config.range_config.gate.basic_gates[0].clone(), usable_rows),
                    &mut region,
                );

                region.next_phase();

                // 2. Query challenge zeta
                let zeta_ch: Value<Fr> = region.get_challenge(config.zeta);

                {
                    let ctx = core.main(1);
                    let fp_chip = FpChip::<Fr>::new(&range_chip, self.limb_bits, self.num_limbs);
                    let conv_chip = ChallengeConversionChip::new(&range_chip, &fp_chip);

                    let zeta_fp_pt = conv_chip.process_challenge(ctx, zeta_ch);

                    // Horner evaluation chains at zeta:
                    let a0_z = horner_eval_fp(ctx, &fp_chip, &a0_points, &zeta_fp_pt);
                    let b0_z = horner_eval_fp(ctx, &fp_chip, &b0_points, &zeta_fp_pt);
                    let c0_z = horner_eval_fp(ctx, &fp_chip, &c0_points, &zeta_fp_pt);
                    let q0_z = horner_eval_fp(ctx, &fp_chip, &q0_points, &zeta_fp_pt);

                    let a1_z = horner_eval_fp(ctx, &fp_chip, &a1_points, &zeta_fp_pt);
                    let b1_z = horner_eval_fp(ctx, &fp_chip, &b1_points, &zeta_fp_pt);
                    let c1_z = horner_eval_fp(ctx, &fp_chip, &c1_points, &zeta_fp_pt);
                    let q1_z = horner_eval_fp(ctx, &fp_chip, &q1_points, &zeta_fp_pt);

                    let m_z = eval_M_in_circuit(ctx, &fp_chip, &zeta_fp_pt);

                    // Verify Identity 0 at zeta:
                    // A0(z) * B0(z) - C0(z) == Q0(z) * M(z)
                    let a0b0 = fp_chip.mul(ctx, &a0_z, &b0_z);
                    let diff0 = fp_chip.sub_no_carry(ctx, &a0b0, &c0_z);
                    let diff0_red = fp_chip.carry_mod(ctx, diff0);
                    let rhs0 = fp_chip.mul(ctx, &q0_z, &m_z);
                    fp_chip.assert_equal(ctx, &diff0_red, &rhs0);

                    // Verify Identity 1 at zeta:
                    // A1(z) * B1(z) - C1(z) == Q1(z) * M(z)
                    let a1b1 = fp_chip.mul(ctx, &a1_z, &b1_z);
                    let diff1 = fp_chip.sub_no_carry(ctx, &a1b1, &c1_z);
                    let diff1_red = fp_chip.carry_mod(ctx, diff1);
                    let rhs1 = fp_chip.mul(ctx, &q1_z, &m_z);
                    fp_chip.assert_equal(ctx, &diff1_red, &rhs1);
                }

                // Assign Phase 1
                core.phase_manager[1].assign_raw(
                    &(config.range_config.gate.basic_gates[1].clone(), usable_rows),
                    &mut region,
                );

                // Assign copy constraints across both phases
                core.copy_manager.assign_raw(&config.range_config.gate.constants, &mut region);

                Ok(())
            },
        )?;

        Ok(())
    }
}

pub fn sample_honest_circuit_witness(rng: &mut StdRng) -> Milestone1Circuit {
    let mut a0 = [Fq::zero(); 12];
    let mut b0 = [Fq::zero(); 12];
    let mut a1 = [Fq::zero(); 12];
    let mut b1 = [Fq::zero(); 12];

    for i in 0..12 {
        a0[i] = Fq::random(&mut *rng);
        b0[i] = Fq::random(&mut *rng);
        a1[i] = Fq::random(&mut *rng);
        b1[i] = Fq::random(&mut *rng);
    }

    let prod0 = poly_mul_deg11(&a0, &b0);
    let (_q0, c0) = poly_div_by_M(&prod0);

    let prod1 = poly_mul_deg11(&a1, &b1);
    let (_q1, c1) = poly_div_by_M(&prod1);

    Milestone1Circuit {
        k: 15,
        lookup_bits: 14,
        limb_bits: 88,
        num_limbs: 3,
        a0,
        b0,
        c0,
        a1,
        b1,
        c1,
        tamper_q: false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_base::halo2_proofs::dev::MockProver;

    #[test]
    pub fn test_milestone1_honest_mock_prover() {
        let mut rng = StdRng::seed_from_u64(0xcafe);
        let circuit = sample_honest_circuit_witness(&mut rng);
        let prover = MockProver::run(circuit.k as u32, &circuit, vec![]).expect("MockProver run");
        prover.assert_satisfied();
        println!("✅ Test 1 Passed: Honest 3-phase polynomial batching verified under MockProver!");
    }

    #[test]
    pub fn test_milestone1_adversarial_tampered_multiplication_rejected() {
        let mut rng = StdRng::seed_from_u64(0xcafe);
        let mut circuit = sample_honest_circuit_witness(&mut rng);

        // Tamper with C0 so that A0 * B0 != C0 mod M
        circuit.c0[0] += Fq::one();

        let prover = MockProver::run(circuit.k as u32, &circuit, vec![]).expect("MockProver run");
        let result = prover.verify();
        assert!(result.is_err(), "Adversarial circuit with invalid multiplication MUST fail!");
        println!("✅ Test 2 Passed: Tampered multiplication C0 rejected by MockProver: {:?}", result.err().unwrap().len());
    }

    #[test]
    pub fn test_milestone1_adversarial_tampered_quotient_rejected() {
        let mut rng = StdRng::seed_from_u64(0xcafe);
        let mut circuit = sample_honest_circuit_witness(&mut rng);

        // Tamper with quotient Q0
        circuit.tamper_q = true;

        let prover = MockProver::run(circuit.k as u32, &circuit, vec![]).expect("MockProver run");
        let result = prover.verify();
        assert!(result.is_err(), "Adversarial circuit with tampered quotient Q0 MUST fail!");
        println!("✅ Test 3 Passed: Tampered quotient Q0 rejected by MockProver: {:?}", result.err().unwrap().len());
    }

    #[test]
    pub fn test_milestone1_real_shplonk_prover() {
        use halo2_base::utils::fs::gen_srs;

        let mut rng = StdRng::seed_from_u64(0x1337);
        let circuit = sample_honest_circuit_witness(&mut rng);
        let k = circuit.k as u32;

        println!("Generating SRS for k = {k}...");
        let params = gen_srs(k);

        println!("Generating VK...");
        let empty_circuit = circuit.without_witnesses();
        let vk = keygen_vk(&params, &empty_circuit).expect("keygen_vk should succeed");

        println!("Generating PK...");
        let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should succeed");

        println!("Creating proof with real SHPLONK prover...");
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            Challenge255<_>,
            _,
            Blake2bWrite<Vec<u8>, G1Affine, _>,
            _,
        >(&params, &pk, &[circuit], &[&[]], rng, &mut transcript)
        .expect("create_proof should succeed");
        let proof = transcript.finalize();
        println!("Proof generated, size: {} bytes", proof.len());

        println!("Verifying proof with real SHPLONK verifier...");
        let mut verifier_transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        let strategy = SingleStrategy::new(&params);
        let verify_result = verify_proof::<
            KZGCommitmentScheme<Bn256>,
            VerifierSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
            SingleStrategy<'_, Bn256>,
        >(params.verifier_params(), pk.get_vk(), strategy, &[&[]], &mut verifier_transcript);

        assert!(verify_result.is_ok(), "Real SHPLONK verification failed: {:?}", verify_result.err());
        println!("✅ Test 3 Passed: Real SHPLONK create_proof + verify_proof succeeded on 3-phase challenge circuit!");
    }
}
