use bellman::groth16::Proof;
use bellman::{Circuit, ConstraintSystem, Index, SynthesisError, Variable};
use bls12_381::Bls12;
use pairing::Engine;
use rand_core::RngCore;
use zksync_bellman::{CurveAffine, EncodedPoint, ScalarEngine};
use masp_primitives::ff::Field;
use crate::sapling::translation::{BellmanScalar, ProvingAssignment};

pub fn create_zksync_proof<C, R: RngCore>(
    circuit: C,
    params: &zksync_bellman::groth16::Parameters<zksync_bellman::bls12_381::Bls12>,
    mut rng: &mut R,
) -> Result<Proof<Bls12>, SynthesisError>
where
    C: Circuit<<Bls12 as Engine>::Fr>,
{
    let r = conv_bellscalar_to_zksync_scalar(BellmanScalar::random(&mut rng));
    let s = conv_bellscalar_to_zksync_scalar(BellmanScalar::random(&mut rng));
    let mut prover = ProvingAssignment {
        a_aux_density: zksync_bellman::source::DensityTracker::new(),
        b_input_density: zksync_bellman::source::DensityTracker::new(),
        b_aux_density: zksync_bellman::source::DensityTracker::new(),
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
    let prepared = zksync_bellman::groth16::PreparedProver { assignment: prover.into() };
    let proof = prepared.create_proof(params, r, s).unwrap();
    Ok(conv_proof_zksync(proof))
}

fn conv_zksync_g1aff(gaff: <zksync_bellman::bls12_381::Bls12 as zksync_bellman::Engine>::G1Affine) -> <Bls12 as Engine>::G1Affine {
    type G1Aff = <Bls12 as Engine>::G1Affine;
    let mut bytes = [0u8; 96];
    bytes.copy_from_slice(gaff.into_uncompressed().as_ref());
    G1Aff::from_uncompressed_unchecked(&bytes).unwrap()
}

fn conv_zksync_g2aff(gaff: <zksync_bellman::bls12_381::Bls12 as zksync_bellman::Engine>::G2Affine) -> <Bls12 as Engine>::G2Affine {
    use zksync_bellman::bls12_381::G2Uncompressed;
    type G2Aff = <Bls12 as Engine>::G2Affine;
    let gaff = G2Uncompressed::from_affine(gaff);
    let mut bytes = [0u8; 192];
    bytes.copy_from_slice(gaff.as_ref());
    G2Aff::from_uncompressed_unchecked(&bytes).unwrap()
}
fn conv_proof_zksync(
    proof: zksync_bellman::groth16::Proof<zksync_bellman::bls12_381::Bls12>
) -> Proof<Bls12> {
    use zksync_bellman::pairing::RawEncodable;
    type G1Aff = <Bls12 as Engine>::G1Affine;
    Proof {
        a: conv_zksync_g1aff(proof.a),
        b: conv_zksync_g2aff(proof.b),
        c: conv_zksync_g1aff(proof.c),
    }
}

fn conv_bellscalar_to_zksync_scalar(sc: BellmanScalar) -> <zksync_bellman::bls12_381::Bls12 as ScalarEngine>::Fr {
    let bytes = sc.to_bytes();
    let mut fr = [0u64; 4];
    let mut scalar_bytes = [0u8; 8];
    scalar_bytes.copy_from_slice(&bytes[0..8]);
    fr[0] = u64::from_le_bytes(scalar_bytes);
    scalar_bytes.copy_from_slice(&bytes[8..16]);
    fr[1] = u64::from_le_bytes(scalar_bytes);
    scalar_bytes.copy_from_slice(&bytes[16..24]);
    fr[2] = u64::from_le_bytes(scalar_bytes);
    scalar_bytes.copy_from_slice(&bytes[24..32]);
    fr[3] = u64::from_le_bytes(scalar_bytes);
    let fr = zksync_bellman::bls12_381::FrRepr(fr);
    <<zksync_bellman::bls12_381::Bls12 as ScalarEngine>::Fr as zksync_bellman::PrimeField>::from_raw_repr(fr).unwrap()
}
impl From<ProvingAssignment<BellmanScalar>> for zksync_bellman::groth16::prover::ProvingAssignment<zksync_bellman::bls12_381::Bls12> {
    fn from(value: ProvingAssignment<BellmanScalar>) -> Self {
        zksync_bellman::groth16::prover::ProvingAssignment {
            a_aux_density: value.a_aux_density,
            b_input_density: value.b_input_density,
            b_aux_density: value.b_aux_density,
            a: value.a.into_iter().map(|x|{
                zksync_bellman::domain::Scalar(conv_bellscalar_to_zksync_scalar(x.0))
            }).collect(),
            b: value.b.into_iter().map(|x|{
                zksync_bellman::domain::Scalar(conv_bellscalar_to_zksync_scalar(x.0))
            }).collect(),
            c: value.c.into_iter().map(|x|{
                zksync_bellman::domain::Scalar(conv_bellscalar_to_zksync_scalar(x.0))
            }).collect(),
            input_assignment: value.input_assignment.into_iter().map(|x| {
                conv_bellscalar_to_zksync_scalar(x)
            }).collect(),
            aux_assignment: value.aux_assignment.into_iter().map(|x| {
                conv_bellscalar_to_zksync_scalar(x)
            }).collect(),
        }
    }
}

pub fn conv_zksync_params(params: bellman::groth16::Parameters<Bls12>) -> zksync_bellman::groth16::Parameters<zksync_bellman::bls12_381::Bls12> {
    let mut bytes = vec![];
    params.write(&mut bytes).unwrap();
    zksync_bellman::groth16::Parameters::read(bytes.as_slice(), false).unwrap()

}
