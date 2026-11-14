use halo2_base::{
    gates::{
        flex_gate::FlexGateConfigParams,
        range::RangeConfig,
    },
    halo2_proofs::plonk::{Challenge, ConstraintSystem, FirstPhase},
    utils::ScalarField,
};

#[derive(Clone, Debug)]
pub struct Milestone1Config<F: ScalarField> {
    pub range_config: RangeConfig<F>,
    pub zeta: Challenge,
}

impl<F: ScalarField> Milestone1Config<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        k: usize,
        num_advice_per_phase: Vec<usize>,
        num_lookup_advice_per_phase: Vec<usize>,
        lookup_bits: usize,
    ) -> Self {
        let gate_params = FlexGateConfigParams {
            k,
            num_advice_per_phase,
            num_fixed: 1,
        };

        let range_config = RangeConfig::configure(
            meta,
            gate_params,
            &num_lookup_advice_per_phase,
            lookup_bits,
        );

        let zeta = meta.challenge_usable_after(FirstPhase);

        Self {
            range_config,
            zeta,
        }
    }
}
