#![allow(clippy::type_complexity)]
use halo2_base::halo2_proofs::{circuit::*, halo2curves::FieldExt, plonk::*, poly::Rotation};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
pub struct FibConfig {
    pub advice: [Column<Advice>; 3],
    pub selector: Selector,
    pub instance: Column<Instance>,
}

pub struct FibChip<F: FieldExt> {
    config: FibConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FibChip<F> {
    pub fn construct(config: FibConfig) -> FibChip<F> {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    // Define a custom gate here
    pub fn configure(
        advice: [Column<Advice>; 3],
        instance: Column<Instance>,
        cs: &mut ConstraintSystem<F>,
    ) -> FibConfig {
        let col_a = advice[0];
        let col_b = advice[1];
        let col_c = advice[2];
        let selector = cs.selector();

        // Every column that will be checked against a value in another column
        // needs to be enabled for equality
        cs.enable_equality(col_a);
        cs.enable_equality(col_b);
        cs.enable_equality(col_c);
        cs.enable_equality(instance);

        cs.create_gate("add", |cells| {
            let s = cells.query_selector(selector);

            // Rotation::cur() is just a helper for 1 (any isize offset is allowed)
            // Boring rotations are better for performance
            let a = cells.query_advice(col_a, Rotation::cur());
            let b = cells.query_advice(col_b, Rotation::cur());
            let c = cells.query_advice(col_c, Rotation::cur());

            // If s = 0 (not turned on selector) - a, b, c can be anything and gate will still be 0
            // If s = 1 (turned on selector), the constraint needs to equal 0
            vec![s * (a + b - c)]
        });

        FibConfig {
            advice: [col_a, col_b, col_c],
            selector,
            instance,
        }
    }

    pub fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                // Even the first row needs to match formula of gate
                self.config.selector.enable(&mut region, 0)?;

                // Copies values from advice provider, we can only work with values in the advice
                let a_cell = region.assign_advice_from_instance(
                    || "a",
                    self.config.instance,
                    // Advice is a static column, so we can use absolute row offsets (basically just the vec![] we pass to prover)
                    0,
                    self.config.advice[0],
                    0,
                )?;

                let b_cell = region.assign_advice_from_instance(
                    || "b",
                    self.config.instance,
                    // Advice is a static coumn, so we can use absolute row offsets
                    1,
                    self.config.advice[1],
                    0,
                )?;

                println!("a: {:?}", a_cell.value());
                println!("b: {:?}", b_cell.value());

                let c_cell = region.assign_advice(
                    || "c",
                    self.config.advice[2],
                    0,
                    || {
                        a_cell
                            .value()
                            .and_then(|a| b_cell.value().and_then(|b| Value::known(*a + *b)))
                    },
                )?;

                Ok((a_cell, b_cell, c_cell))
            },
        )
    }

    pub fn assign_row(
        &self,
        mut layouter: impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "next_row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                // Copies the value from an assigned cell to another cell
                // THIS IS A CONSTRAINT TOO - this ensures that each row follows the other!
                a.copy_advice(|| "a", &mut region, self.config.advice[0], 0)?;
                b.copy_advice(|| "b", &mut region, self.config.advice[1], 0)?;

                let c_value = a.value().and_then(|a| b.value().map(|b| *a + *b));

                let c = region.assign_advice(|| "c", self.config.advice[2], 0, || c_value)?;

                // We return C from the region, this is how we can access region values outside of a region!
                Ok(c)
            },
        )
    }

    // Instance is global
    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use halo2_base::halo2_proofs::dev::MockProver;
    use halo2_base::halo2_proofs::halo2curves::bn256::Fr;

    #[derive(Default)]
    struct MyCircuit {
        fib_size: usize,
    }

    impl<F: FieldExt> Circuit<F> for MyCircuit {
        type Config = FibConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        // Circuit setup (doesn't change on input)
        fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config {
            let col_a = cs.advice_column();
            let col_b = cs.advice_column();
            let col_c = cs.advice_column();
            let instance = cs.instance_column();

            FibChip::configure([col_a, col_b, col_c], instance, cs)
        }

        // Changes for each proof
        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = FibChip::construct(config);

            let (_, mut b, mut c) = chip.assign_first_row(layouter.namespace(|| "first row"))?;

            // We've skipped the first 2 items in fib sequence (as they are awkward)
            // 0 should be 3, just using 0 to test row count - 57 should be =9
            for _ in 3..=self.fib_size - 1 {
                let new_c = chip.assign_row(layouter.namespace(|| "next_row"), &b, &c)?;
                b = c;
                c = new_c;
            }

            println!("c: {:?}", c.value());

            // chip.expose_public(layouter.namespace(|| "out"), &c, 2)?;

            Ok(())
        }
    }

    #[test]
    fn main() {
        let k = 20;

        let a = Fr::from(1);
        let b = Fr::from(1);
        // let out = Fr::from(102334155);

        let circuit = MyCircuit { fib_size: 1000000 };

        // Vector for the public input column (if we had more, we'd need to add additional)
        let public_input = vec![a, b];
        let instance_columns = vec![public_input];

        let prover = MockProver::<Fr>::run(k, &circuit, instance_columns).unwrap();
        prover.assert_satisfied();

        println!("Proof generated successfully!");
    }
}
