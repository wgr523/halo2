use ff::{BatchInvert, FromUniformBytes};
use halo2_proofs::{
    arithmetic::{CurveAffine, Field},
    circuit::{floor_planner::V1, Layouter, Value},
    dev::{metadata, FailureLocation, MockProver, VerifyFailure},
    halo2curves::pasta::EqAffine,
    plonk::*,
    poly::{
        commitment::ParamsProver,
        ipa::{
            commitment::{IPACommitmentScheme, ParamsIPA},
            multiopen::{ProverIPA, VerifierIPA},
            strategy::AccumulatorStrategy,
        },
        Rotation, VerificationStrategy,
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};
use halo2curves::bn256::{Fr,G1Affine};
use rand_core::{OsRng, RngCore};
use std::iter;

#[derive(Clone)]
struct MyConfig {
    q_enable: Selector,
    x: Column<Advice>,
    x_power: Column<Advice>,
    a: Column<Advice>,
    acc_sum: Column<Advice>,
}

impl MyConfig {
    fn configure<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enable = meta.selector();
        let x = meta.advice_column();
        let x_power = meta.advice_column();
        let a = meta.advice_column();
        let acc_sum = meta.advice_column();

        meta.create_gate("acc_sum should equal", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let x_prev = meta.query_advice(x, Rotation::prev());
            let x = meta.query_advice(x, Rotation::cur());

            let x_power_prev = meta.query_advice(x_power, Rotation::prev());
            let x_power = meta.query_advice(x_power, Rotation::cur());

            let a = meta.query_advice(a, Rotation::cur());
            let acc_sum_prev = meta.query_advice(acc_sum, Rotation::prev());
            let acc_sum = meta.query_advice(acc_sum, Rotation::cur());

            vec![
                q_enable.clone() * (x_prev - x.clone()),
                q_enable.clone() * (x_power.clone() - x_power_prev * x),
                q_enable * (acc_sum - x_power * a - acc_sum_prev),
            ]
        });
        meta.create_gate("a is binary", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let a = meta.query_advice(a, Rotation::cur());
            vec![q_enable * a.clone() * (a - Expression::Constant(F::ONE))]
        });
        Self {
            q_enable,
            x,
            x_power,
            a,
            acc_sum,
        }
    }
}

#[derive(Clone, Default)]
struct MyCircuit<F: Field, const H: usize> {
    a: Value<[F; H]>,
    x: Value<F>,
}

impl<F: Field, const H: usize> Circuit<F> for MyCircuit<F, H> {
    type Config = MyConfig;
    type FloorPlanner = V1;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        MyConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "test",
            |mut region| {
                for offset in 1..H {
                    config.q_enable.enable(&mut region, offset)?;
                }

                let mut acc_sum = Value::known(F::ZERO);
                let mut x_power = Value::known(F::ONE);
                for (idx, value) in self.a.transpose_array().iter().enumerate() {
                    
                    region.assign_advice(
                        || format!("a[{}]", idx),
                        config.a,
                        idx,
                        || value.clone(),
                    )?;
                    region.assign_advice(|| format!("x[{}]", idx), config.x, idx, || self.x)?;
                    region.assign_advice(
                        || format!("x_power[{}]", idx),
                        config.x_power,
                        idx,
                        || x_power,
                    )?;
                    region.assign_advice(
                        || format!("acc_sum[{}]", idx),
                        config.acc_sum,
                        idx,
                        || acc_sum,
                    )?;
                    // println!(
                    //     "{},{:?},{:?},{:?},{:?},",
                    //     idx, value, self.x, x_power, acc_sum
                    // );
                    x_power = x_power * self.x;
                    acc_sum = acc_sum + value.clone() * x_power;
                }
                Ok(())
            },
        )
    }
}

fn test_mock_prover<F: Ord + FromUniformBytes<64>, const H: usize>(
    k: u32,
    circuit: MyCircuit<F, H>,
    expected: Result<(), Vec<(metadata::Constraint, FailureLocation)>>,
) {
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    match (prover.verify(), expected) {
        (Ok(_), Ok(_)) => {}
        (Err(err), Err(expected)) => {
            assert_eq!(
                err.into_iter()
                    .map(|failure| match failure {
                        VerifyFailure::ConstraintNotSatisfied {
                            constraint,
                            location,
                            ..
                        } => (constraint, location),
                        _ => panic!("MockProver::verify has result unmatching expected"),
                    })
                    .collect::<Vec<_>>(),
                expected
            )
        }
        (Err(err), _) => panic!("MockProver::verify has result unmatching expected"),
        (Ok(_), Err(_)) => todo!(),
    };
}

fn test_prover<C: CurveAffine, const H: usize>(
    k: u32,
    circuit: MyCircuit<C::Scalar, H>,
    expected: bool,
) where
    C::Scalar: FromUniformBytes<64>,
{
    let params = ParamsIPA::<C>::new(k);
    let vk = keygen_vk(&params, &circuit).unwrap();
    let pk = keygen_pk(&params, vk, &circuit).unwrap();

    let proof = {
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

        create_proof::<IPACommitmentScheme<C>, ProverIPA<C>, _, _, _, _>(
            &params,
            &pk,
            &[circuit],
            &[&[]],
            OsRng,
            &mut transcript,
        )
        .expect("proof generation should not fail");

        transcript.finalize()
    };

    let accepted = {
        let strategy = AccumulatorStrategy::new(&params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);

        verify_proof::<IPACommitmentScheme<C>, VerifierIPA<C>, _, _, _>(
            &params,
            pk.get_vk(),
            strategy,
            &[&[]],
            &mut transcript,
        )
        .map(|strategy| strategy.finalize())
        .unwrap_or_default()
    };

    assert_eq!(accepted, expected);
}

fn main() {
    const H: usize = 262144;
    const K: u32 = 19;

    let circuit = &MyCircuit::<_, H> {
        a: Value::known([Fr::ONE; H]),
        x: Value::known(Fr::ONE + Fr::ONE),
    };
    
    {
        // test_mock_prover(K, circuit.clone(), Ok(()));
        let start = std::time::Instant::now();
        test_prover::<G1Affine, H>(K, circuit.clone(), true);
        let duration = start.elapsed();
        println!("test_prover运行时间: {:?}", duration);
    }

    // #[cfg(not(feature = "sanity-checks"))]
    // {
    //     use std::ops::IndexMut;

    //     let mut circuit = circuit.clone();
    //     circuit.shuffled = circuit.shuffled.map(|mut shuffled| {
    //         shuffled.index_mut(0).swap(0, 1);
    //         shuffled
    //     });

    //     test_mock_prover(
    //         K,
    //         circuit.clone(),
    //         Err(vec![(
    //             ((1, "z should end with 1").into(), 0, "").into(),
    //             FailureLocation::InRegion {
    //                 region: (0, "Shuffle original into shuffled").into(),
    //                 offset: 32,
    //             },
    //         )]),
    //     );
    //     test_prover::<EqAffine, W, H>(K, circuit, false);
    // }
}
