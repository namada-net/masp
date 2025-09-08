use std::sync::Arc;
use bellman::groth16::{Parameters, Proof};
use bellman::{ConstraintSystem, Index, SynthesisError, Variable};
use bellperson::multiexp::DensityTracker;
use bls12_381::Bls12;
use group::ff::{Field, PrimeField};

use pairing::Engine;
use rand_core::RngCore;
use crate::sapling::translation::{BellmanScalar, ProvingAssignment};

fn conv_bellscalar_to_bellperson_scalar(scalar: BellmanScalar) -> blstrs::Scalar {
    let bytes = scalar.to_bytes();
    blstrs::Scalar::from_bytes_le(&bytes).unwrap()
}

pub fn conv_bellperson_params(params: &Parameters<Bls12>) -> bellperson::groth16::Parameters<blstrs::Bls12> {
    let mut bytes = vec![];
    params.write(&mut bytes).unwrap();
    bellperson::groth16::Parameters::read(bytes.as_slice(), false).unwrap()
}

pub fn create_bellperson_proof<C, R>(
    circuit: C,
    params: &bellperson::groth16::Parameters<blstrs::Bls12>,
    mut rng: &mut R,
) -> Result<Proof<Bls12>, SynthesisError>
where
    C: bellman::Circuit<BellmanScalar>,
    R: RngCore,
{
    let r = conv_bellscalar_to_bellperson_scalar(BellmanScalar::random(&mut rng));
    let s = conv_bellscalar_to_bellperson_scalar(BellmanScalar::random(&mut rng));

    let mut prover = ProvingAssignment {
        a_aux_density: DensityTracker::new(),
        b_input_density: DensityTracker::new(),
        b_aux_density: DensityTracker::new(),
        a: vec![],
        b: vec![],
        c: vec![],
        input_assignment: vec![],
        aux_assignment: vec![],
    };
    prover.alloc_input(|| "", || Ok(<Bls12 as Engine>::Fr::ONE))?;

    circuit.synthesize(&mut prover)?;

    for i in 0..prover.input_assignment.len() {
        prover.enforce(|| "", |lc| lc + Variable::new_unchecked(Index::Input(i)), |lc| lc, |lc| lc);
    }

    let start = std::time::Instant::now();
    let input_assigments = {
        let input_assignment = std::mem::take(&mut prover.input_assignment);
        Arc::new(input_assignment.into_iter().map(|s| {
            let x = blstrs::Scalar::from_bytes_le(&s.to_bytes()).unwrap();
            x.to_repr()
        }).collect())
    };
    let aux_assigments = {
        let aux_assignment = std::mem::take(&mut prover.aux_assignment);
        Arc::new(aux_assignment.into_iter().map(|s| {
            let x = blstrs::Scalar::from_bytes_le(&s.to_bytes()).unwrap();
            x.to_repr()
        }).collect())
    };


    let proof = bellperson::groth16::create_proof_inner_inner(
        vec![bellperson::groth16::ProvingAssignment {
            a_aux_density: prover.a_aux_density,
            b_input_density: prover.b_input_density,
            b_aux_density: prover.b_aux_density,
            a: prover.a.into_iter().map(|x| {
                 blstrs::Scalar::from_bytes_le(&x.0.to_bytes()).unwrap()
            }).collect(),
            b: prover.b.into_iter().map(|x| {
                blstrs::Scalar::from_bytes_le(&x.0.to_bytes()).unwrap()
            }).collect(),
            c: prover.c.into_iter().map(|x| {
                blstrs::Scalar::from_bytes_le(&x.0.to_bytes()).unwrap()
            }).collect(),
            input_assignment: vec![],
            aux_assignment: vec![],
        }],
        start,
        vec![input_assigments],
        vec![aux_assigments],
        params,
        Some((vec![r], vec![s])),
        true,
    ).unwrap();
    Ok(convert_proof(&proof[0]))
}

fn convert_proof(proof: &bellperson::groth16::Proof<blstrs::Bls12>) -> Proof<Bls12> {
    Proof {
        a: <Bls12 as Engine>::G1Affine::from_uncompressed(&proof.a.to_uncompressed()).unwrap(),
        b: <Bls12 as Engine>::G2Affine::from_uncompressed(&proof.b.to_uncompressed()).unwrap(),
        c: <Bls12 as Engine>::G1Affine::from_uncompressed(&proof.c.to_uncompressed()).unwrap(),
    }
}