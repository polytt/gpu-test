use halo2_base::halo2_proofs::{
    self,
    circuit::SimpleFloorPlanner,
    plonk::{self, Advice, Circuit, Column, ConstraintSystem, Expression, Instance, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;

#[derive(Clone, Default)]
pub struct IsTenCircuit<F> {
    _marker: PhantomData<F>,
}

#[derive(Clone)]
pub struct IsTenCircuitConfig {
    selector: Selector,
    advice: Column<Advice>,
    instance: Column<Instance>,
}

impl<F: halo2_base::halo2_proofs::arithmetic::FieldExt> Circuit<F> for IsTenCircuit<F> {
    type Config = IsTenCircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let selector = meta.selector();
        let advice = meta.advice_column();
        let instance = meta.instance_column();

        meta.enable_equality(instance);
        meta.enable_equality(advice);

        meta.create_gate("=10", |meta| {
            let s = meta.query_selector(selector);
            let a = meta.query_advice(advice, Rotation::cur());
            vec![s * (a - Expression::Constant(F::from_u128(10u128)))]
        });

        IsTenCircuitConfig {
            selector,
            advice,
            instance,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl halo2_proofs::circuit::Layouter<F>,
    ) -> Result<(), plonk::Error> {
        // Check public input is 10
        layouter.assign_region(
            || "is_10?!",
            |mut region| {
                config.selector.enable(&mut region, 0)?;

                // region.enable_selector(config.selector)?;
                region.assign_advice_from_instance(
                    || "10?",
                    config.instance,
                    0,
                    config.advice,
                    0,
                )?;

                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use halo2_base::halo2_proofs::{
        dev::metadata::{Column, VirtualCell},
        dev::{FailureLocation, MockProver, VerifyFailure},
        halo2curves::bn256::Fr,
        halo2curves::FieldExt,
    };

    #[test]
    fn test_valid_circuit() {
        let k = 21;
        let circuit = IsTenCircuit::<Fr>::default();
        let public_inputs = vec![Fr::from_u128(10u128)];
        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();

        // Check we don't panic
        prover.assert_satisfied();
    }

    #[test]
    fn test_invalid_circuit() {
        let k = 21;
        let circuit = IsTenCircuit::<Fr>::default();

        // Check the circuit errors for all values except 10
        for i in 0..20u128 {
            // 10 is valid, so skip it
            if i != 10 {
                let public_inputs = vec![Fr::from_u128(i)];
                let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();

                assert_eq!(
                    prover.verify(),
                    Err(vec![VerifyFailure::ConstraintNotSatisfied {
                        constraint: ((0, "=10").into(), 0, "").into(),
                        location: FailureLocation::InRegion {
                            region: (0, "is_10?!").into(),
                            offset: 0,
                        },
                        cell_values: vec![(
                            VirtualCell::from((Column::from((Advice::default().into(), 0)), 0)),
                            if i <= 1 {
                                format!("{i:x}")
                            } else {
                                format!("0x{i:x}")
                            }
                        )]
                    }])
                )
            }
        }
    }
}
