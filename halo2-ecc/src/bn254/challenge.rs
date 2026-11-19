use halo2_base::{
    gates::{GateInstructions, RangeInstructions, RangeChip},
    halo2_proofs::{
        circuit::Value,
    },
    utils::{biguint_to_fe, fe_to_biguint, BigPrimeField},
    AssignedValue, Context,
    QuantumCell::{Constant, Existing},
};
use num_bigint::BigUint;
use crate::bn254::{FpChip, FpPoint};
use crate::bigint::{ProperUint};

pub const R_STR: &str = "21888242871839275222246405745257275088548364400416034343698204186575808495617";

pub struct ChallengeConversionChip<'range, 'chip, F: BigPrimeField> {
    pub range: &'range RangeChip<F>,
    pub fp_chip: &'chip FpChip<'chip, F>,
    pub r_limbs: [F; 3],
}

impl<'range, 'chip, F: BigPrimeField> ChallengeConversionChip<'range, 'chip, F> {
    pub fn new(range: &'range RangeChip<F>, fp_chip: &'chip FpChip<'chip, F>) -> Self {
        let r_big: BigUint = R_STR.parse().unwrap();
        let mask = (BigUint::from(1u64) << 88) - 1u32;
        let r0 = biguint_to_fe::<F>(&(&r_big & &mask));
        let r1 = biguint_to_fe::<F>(&((&r_big >> 88) & &mask));
        let r2 = biguint_to_fe::<F>(&(&r_big >> 176));
        Self {
            range,
            fp_chip,
            r_limbs: [r0, r1, r2],
        }
    }

    pub fn process_challenge(
        &self,
        ctx: &mut Context<F>,
        ch_val: Value<F>,
    ) -> FpPoint<F> {
        let mut ch = F::ZERO;
        ch_val.map(|v| ch = v);

        // Decompose into 3 limbs
        let ch_big = fe_to_biguint(&ch);
        let mask = (BigUint::from(1u64) << 88) - 1u32;
        let z0_val = biguint_to_fe::<F>(&(&ch_big & &mask));
        let z1_val = biguint_to_fe::<F>(&((&ch_big >> 88) & &mask));
        let z2_val = biguint_to_fe::<F>(&(&ch_big >> 176));

        let z0 = ctx.load_witness(z0_val);
        let z1 = ctx.load_witness(z1_val);
        let z2 = ctx.load_witness(z2_val);

        // Range check each limb
        self.range.range_check(ctx, z0, 88);
        self.range.range_check(ctx, z1, 88);
        self.range.range_check(ctx, z2, 88);

        // Native reconstruction equality
        let base_88 = self.range.gate().pow_of_two()[88];
        let term1 = self.range.gate().mul(ctx, z1, Constant(base_88));
        let sum01 = self.range.gate().add(ctx, z0, term1);

        let base_176 = self.range.gate().pow_of_two()[88 * 2];
        let term2 = self.range.gate().mul(ctx, z2, Constant(base_176));
        let reconstructed = self.range.gate().add(ctx, sum01, term2);

        let ch_cell = ctx.load_witness(ch);
        ctx.constrain_equal(&reconstructed, &ch_cell);

        // Enforce z < r integer comparison
        self.enforce_less_than_r(ctx, [z0, z1, z2]);

        // Convert to CRT representation for FpChip
        let proper_uint = ProperUint([z0, z1, z2].to_vec());
        let crt = proper_uint.into_crt(
            ctx,
            self.range.gate(),
            ch_big,
            &self.fp_chip.limb_bases,
            self.fp_chip.limb_bits,
        );

        crt
    }

    fn enforce_less_than_r(&self, ctx: &mut Context<F>, z_limbs: [AssignedValue<F>; 3]) {
        let mut borrow: Option<AssignedValue<F>> = None;
        for (&r_limb, z_limb) in self.r_limbs.iter().zip(z_limbs) {
            let lt = match borrow {
                None => self.range.is_less_than(ctx, z_limb, Constant(r_limb), 88),
                Some(borrow) => {
                    let plus_borrow = self.range.gate().add(ctx, Constant(r_limb), borrow);
                    self.range.is_less_than(
                        ctx,
                        Existing(z_limb),
                        Existing(plus_borrow),
                        88,
                    )
                }
            };
            borrow = Some(lt);
        }
        self.range.gate().assert_is_const(ctx, &borrow.unwrap(), &F::ONE);
    }
}
