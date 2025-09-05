//! An egregious set of ill-advised hacks made in an attempt to benchmark the
//! speed of building groth16 proofs relative to bellman with as little code
//! changes as possible.

use std::io;
use std::ops::{AddAssign, Mul};

use ark_bls12_381::{Bls12_381, Fq as ArkG1};
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{BigInt, Fp2, PrimeField as ArkPrimeField, Zero};
use ark_groth16::ProvingKey;
use ark_groth16::r1cs_to_qap::{LibsnarkReduction, R1CSToQAP};
use ark_poly::GeneralEvaluationDomain;
use ark_relations::r1cs::ConstraintSystemRef;
use bellman::domain::Scalar;
use bellman::groth16::{ParameterSource, Proof};
use bellman::multiexp::DensityTracker;
use bellman::{Circuit, ConstraintSystem, Index, LinearCombination, SynthesisError, Variable};
use bls12_381::Bls12;
use group::ff::Field;

use masp_primitives::ff::{PrimeField, PrimeFieldBits};
use pairing::Engine;
use rand::Rng;
use rand_core::RngCore;
#[cfg(feature = "parallel")]
use rayon::prelude::*;
use zksync_bellman::{CurveAffine, EncodedPoint, RawEncodable, ScalarEngine};
use zksync_bellman::bn256::G2Uncompressed;

pub type BellmanScalar = <Bls12 as Engine>::Fr;
pub type ArkScalar = ark_bls12_381::Fr;
pub struct ArkCS {
    pub inner: ConstraintSystemRef<ArkScalar>,
}

impl Default for ArkCS {
    fn default() -> Self {
        ArkCS {
            inner: ark_relations::r1cs::ConstraintSystem::new_ref(),
        }
    }
}

/// If I've understood all the poorly documented code correctly, there is a
/// small chance that this works
pub fn conv_scalar(bellman_scalar: BellmanScalar) -> ArkScalar {
    let value = bellman_scalar.to_bytes();
    let mut v_bytes = [0u64; 4];
    v_bytes[0] = u64::from_le_bytes(<[u8; 8]>::try_from(&value[0..8]).unwrap());
    v_bytes[1] = u64::from_le_bytes(<[u8; 8]>::try_from(&value[8..16]).unwrap());
    v_bytes[2] = u64::from_le_bytes(<[u8; 8]>::try_from(&value[16..24]).unwrap());
    v_bytes[3] = u64::from_le_bytes(<[u8; 8]>::try_from(&value[24..32]).unwrap());
    ArkScalar::new(BigInt::new(v_bytes))
}

pub fn conv_fp(bytes: [u8; 48]) -> ArkG1 {
    let mut v_bytes = [0u64; 6];
    v_bytes[5] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[0..8]).unwrap());
    v_bytes[4] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[8..16]).unwrap());
    v_bytes[3] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[16..24]).unwrap());
    v_bytes[2] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[24..32]).unwrap());
    v_bytes[1] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[32..40]).unwrap());
    v_bytes[0] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[40..48]).unwrap());
    ArkG1::new(BigInt::new(v_bytes))
}

/// Some clever fuck thought they could keep these fields private from me,
/// but I found a way. ABSTRACTIONS ALWAYS LEAK MOTHERFUCKERS
pub fn conv_g1(bellman_g1: <Bls12 as Engine>::G1Affine) -> <Bls12_381 as Pairing>::G1Affine {
    type G1Aff = <Bls12_381 as Pairing>::G1Affine;

    let b_bytes = bellman_g1.to_uncompressed();
    let is_infinity = ((b_bytes[0] >> 6) & 1) == 1;
    if is_infinity {
        return G1Aff {
            x: ArkG1::zero(),
            y: ArkG1::zero(),
            infinity: true,
        };
    }
    let x = {
        let mut tmp = [0; 48];
        tmp.copy_from_slice(&b_bytes[0..48]);
        // Mask away the flag bits
        tmp[0] &= 0b0001_1111;
        tmp
    };
    let y = {
        let mut tmp = [0; 48];
        tmp.copy_from_slice(&b_bytes[48..96]);
        tmp
    };
    G1Aff {
        x: conv_fp(x),
        y: conv_fp(y),
        infinity: is_infinity,
    }
}

pub fn conv_g2(bellman_g2: <Bls12 as Engine>::G2Affine) -> <Bls12_381 as Pairing>::G2Affine {
    type G2Aff = <Bls12_381 as Pairing>::G2Affine;

    let b_bytes = bellman_g2.to_uncompressed();
    let is_infinity = ((b_bytes[0] >> 6) & 1) == 1;
    if is_infinity {
        return G2Aff {
            x: Fp2::zero(),
            y: Fp2::zero(),
            infinity: true,
        };
    }
    let xc1 = {
        let mut tmp = [0; 48];
        tmp.copy_from_slice(&b_bytes[0..48]);

        // Mask away the flag bits
        tmp[0] &= 0b0001_1111;
        tmp
    };
    let xc0 = {
        let mut tmp = [0; 48];
        tmp.copy_from_slice(&b_bytes[48..96]);
        tmp
    };

    // Attempt to obtain the y-coordinate
    let yc1 = {
        let mut tmp = [0; 48];
        tmp.copy_from_slice(&b_bytes[96..144]);
        tmp
    };
    let yc0 = {
        let mut tmp = [0; 48];
        tmp.copy_from_slice(&b_bytes[144..192]);
        tmp
    };
    G2Aff {
        x: Fp2::new(conv_fp(xc0), conv_fp(xc1)),
        y: Fp2::new(conv_fp(yc0), conv_fp(yc1)),
        infinity: false,
    }
}

pub fn conv_ark_g1(ark_g1: <Bls12_381 as Pairing>::G1Affine) -> <Bls12 as Engine>::G1Affine {
    type G1Aff = <Bls12 as Engine>::G1Affine;

    if ark_g1.infinity {
        return Default::default();
    }
    let bytes = <[u8; 96]>::try_from(
        ark_g1
            .x
            .into_bigint()
            .0
            .map(u64::to_be_bytes)
            .into_iter()
            .rev()
            .flatten()
            .chain(
                ark_g1
                    .y
                    .into_bigint()
                    .0
                    .map(u64::to_be_bytes)
                    .into_iter()
                    .rev()
                    .flatten(),
            )
            .collect::<Vec<_>>(),
    )
    .unwrap();
    G1Aff::from_uncompressed_unchecked(&bytes).unwrap()
}

pub fn conv_ark_g2(ark_g2: <Bls12_381 as Pairing>::G2Affine) -> <Bls12 as Engine>::G2Affine {
    type G2Aff = <Bls12 as Engine>::G2Affine;

    if ark_g2.infinity {
        return G2Aff::identity();
    }
    let bytes = <[u8; 192]>::try_from(
        ark_g2
            .x
            .c1
            .into_bigint()
            .0
            .map(u64::to_be_bytes)
            .into_iter()
            .rev()
            .flatten()
            .chain(
                ark_g2
                    .x
                    .c0
                    .into_bigint()
                    .0
                    .map(u64::to_be_bytes)
                    .into_iter()
                    .rev()
                    .flatten(),
            )
            .chain(
                ark_g2
                    .y
                    .c1
                    .into_bigint()
                    .0
                    .map(u64::to_be_bytes)
                    .into_iter()
                    .rev()
                    .flatten(),
            )
            .chain(
                ark_g2
                    .y
                    .c0
                    .into_bigint()
                    .0
                    .map(u64::to_be_bytes)
                    .into_iter()
                    .rev()
                    .flatten(),
            )
            .collect::<Vec<_>>(),
    )
    .unwrap();

    G2Aff::from_uncompressed_unchecked(&bytes).unwrap()
}

pub fn conv_proof(ark_proof: ark_groth16::data_structures::Proof<Bls12_381>) -> Proof<Bls12> {
    let ark_groth16::data_structures::Proof::<Bls12_381> { a, b, c } = ark_proof;
    Proof::<Bls12> {
        a: conv_ark_g1(a),
        b: conv_ark_g2(b),
        c: conv_ark_g1(c),
    }
}

pub fn conv_error(ark_err: ark_relations::r1cs::SynthesisError) -> SynthesisError {
    match ark_err {
        ark_relations::r1cs::SynthesisError::MissingCS => {
            SynthesisError::IoError(io::Error::other("MissingCS"))
        }
        ark_relations::r1cs::SynthesisError::AssignmentMissing => SynthesisError::AssignmentMissing,
        ark_relations::r1cs::SynthesisError::DivisionByZero => SynthesisError::DivisionByZero,
        ark_relations::r1cs::SynthesisError::Unsatisfiable => SynthesisError::Unsatisfiable,
        ark_relations::r1cs::SynthesisError::PolynomialDegreeTooLarge => {
            SynthesisError::PolynomialDegreeTooLarge
        }
        ark_relations::r1cs::SynthesisError::UnexpectedIdentity => {
            SynthesisError::UnexpectedIdentity
        }
        ark_relations::r1cs::SynthesisError::MalformedVerifyingKey => {
            SynthesisError::IoError(io::Error::other("MalformedVerifyingKey"))
        }
        ark_relations::r1cs::SynthesisError::UnconstrainedVariable => {
            SynthesisError::UnconstrainedVariable
        }
    }
}

pub fn extract_proving_key(
    mut bellman_pk: &bellman::groth16::Parameters<Bls12>,
) -> Result<ProvingKey<Bls12_381>, SynthesisError> {
    let vk = bellman_pk.get_vk(0)?;
    Ok(ProvingKey {
        vk: ark_groth16::data_structures::VerifyingKey {
            alpha_g1: conv_g1(vk.alpha_g1),
            beta_g2: conv_g2(vk.beta_g2),
            gamma_g2: conv_g2(vk.gamma_g2),
            delta_g2: conv_g2(vk.delta_g2),
            gamma_abc_g1: vk.ic.iter().map(|x| conv_g1(*x)).collect(),
        },
        beta_g1: conv_g1(vk.beta_g1),
        delta_g1: conv_g1(vk.delta_g1),
        a_query: bellman_pk.a.iter().map(|x| conv_g1(*x)).collect(),
        b_g1_query: bellman_pk.b_g1.iter().map(|x| conv_g1(*x)).collect(),
        b_g2_query: bellman_pk.b_g2.iter().map(|x| conv_g2(*x)).collect(),
        h_query: bellman_pk.h.iter().map(|x| conv_g1(*x)).collect(),
        l_query: bellman_pk.l.iter().map(|x| conv_g1(*x)).collect(),
    })
}

type D<F> = GeneralEvaluationDomain<F>;

pub fn create_ark_proof_from_bell_circuit<C, R>(
    circuit: C,
    proving_key: &ProvingKey<Bls12_381>,
    mut rng: &mut R,
) -> Result<Proof<Bls12>, SynthesisError>
where
    C: Circuit<BellmanScalar>,
    R: RngCore,
{
    let r = conv_scalar(BellmanScalar::random(&mut rng));
    let s = conv_scalar(BellmanScalar::random(&mut rng));

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

    prover.alloc_input(|| "", || Ok(BellmanScalar::ONE))?;

    circuit.synthesize(&mut prover)?;

    for i in 0..prover.input_assignment.len() {
        prover.enforce(
            || "",
            |lc| lc + Variable::new_unchecked(Index::Input(i)),
            |lc| lc,
            |lc| lc,
        );
    }

    let prover = ArkCS::from(prover);
    let cs = prover.inner;
    let h = LibsnarkReduction::witness_map::<ArkScalar, D<ArkScalar>>(cs.clone())
        .map_err(conv_error)?;

    let prover = cs.borrow().unwrap();
    Ok(conv_proof(create_proof_with_assignment(
        proving_key,
        r,
        s,
        &h,
        &prover.instance_assignment[1..],
        &prover.witness_assignment,
    )))
}

#[inline]
fn create_proof_with_assignment(
    pk: &ProvingKey<Bls12_381>,
    r: ArkScalar,
    s: ArkScalar,
    h: &[ArkScalar],
    input_assignment: &[ArkScalar],
    aux_assignment: &[ArkScalar],
) -> ark_groth16::data_structures::Proof<Bls12_381> {
    // E = Bls12_381
    // E::ScalarField = ArkScalar
    use ark_std::{cfg_into_iter, cfg_iter};
    let h_assignment = cfg_into_iter!(h)
        .map(|s| s.into_bigint())
        .collect::<Vec<_>>();
    let h_acc = <ark_ec::bls12::Bls12<ark_bls12_381::Config> as Pairing>::G1::msm_bigint(
        &pk.h_query,
        &h_assignment,
    );
    drop(h_assignment);

    // Compute C
    let aux_assignment = cfg_iter!(aux_assignment)
        .map(|s| s.into_bigint())
        .collect::<Vec<_>>();
    let l_aux_acc = <ark_ec::bls12::Bls12<ark_bls12_381::Config> as Pairing>::G1::msm_bigint(
        &pk.l_query,
        &aux_assignment,
    );
    let r_s_delta_g1 = pk.delta_g1 * (r * s);

    let input_assignment = input_assignment
        .iter()
        .map(|s| s.into_bigint())
        .collect::<Vec<_>>();
    let assignment = [&input_assignment[..], &aux_assignment[..]].concat();
    drop(aux_assignment);
    // Compute A
    let r_g1 = pk.delta_g1.mul(r);
    let g_a = calculate_coeff(r_g1, &pk.a_query, pk.vk.alpha_g1, &assignment);

    let s_g_a = g_a * s;
    // Compute B in G1 if needed
    let g1_b = if !r.is_zero() {
        let s_g1 = pk.delta_g1.mul(s);
        calculate_coeff(s_g1, &pk.b_g1_query, pk.beta_g1, &assignment)
    } else {
        <ark_ec::bls12::Bls12<ark_bls12_381::Config> as Pairing>::G1::zero()
    };

    // Compute B in G2
    let s_g2 = pk.vk.delta_g2.mul(s);
    let g2_b = calculate_coeff(s_g2, &pk.b_g2_query, pk.vk.beta_g2, &assignment);
    let r_g1_b = g1_b * r;

    drop(assignment);

    let mut g_c = s_g_a;
    g_c += &r_g1_b;
    g_c -= &r_s_delta_g1;
    g_c += &l_aux_acc;
    g_c += &h_acc;

    ark_groth16::data_structures::Proof {
        a: g_a.into_affine(),
        b: g2_b.into_affine(),
        c: g_c.into_affine(),
    }
}

pub fn calculate_coeff<G: AffineRepr>(
    initial: G::Group,
    query: &[G],
    vk_param: G,
    assignment: &[<G::ScalarField as ArkPrimeField>::BigInt],
) -> G::Group
where
    G::Group: VariableBaseMSM<MulBase = G>,
{
    let el = query[0];
    let acc = G::Group::msm_bigint(&query[1..], assignment);

    let mut res = initial;
    res.add_assign(&el);
    res += &acc;
    res.add_assign(&vk_param);

    res
}

fn eval<S: PrimeField>(
    lc: &LinearCombination<S>,
    mut input_density: Option<&mut zksync_bellman::source::DensityTracker>,
    mut aux_density: Option<&mut zksync_bellman::source::DensityTracker>,
    input_assignment: &[S],
    aux_assignment: &[S],
) -> S {
    let mut acc = S::ZERO;

    for &(index, coeff) in lc.as_ref().iter() {
        let mut tmp;

        if !coeff.is_zero_vartime() {
            match index.get_unchecked() {
                Index::Input(i) => {
                    tmp = input_assignment[i];
                    if let Some(ref mut v) = input_density {
                        v.inc(i);
                    }
                }
                Index::Aux(i) => {
                    tmp = aux_assignment[i];
                    if let Some(ref mut v) = aux_density {
                        v.inc(i);
                    }
                }
            }

            if coeff != S::ONE {
                tmp *= coeff;
            }
            acc += tmp;
        }
    }

    acc
}

impl From<ProvingAssignment<BellmanScalar>> for ArkCS {
    fn from(value: ProvingAssignment<BellmanScalar>) -> Self {
        let mut cs = ark_relations::r1cs::ConstraintSystem::default();
        cs.num_instance_variables = value.input_assignment.len();
        cs.num_witness_variables = value.aux_assignment.len();
        cs.instance_assignment = value
            .input_assignment
            .into_iter()
            .map(conv_scalar)
            .collect();
        cs.witness_assignment = value.aux_assignment.into_iter().map(conv_scalar).collect();
        for (a, (b, c)) in value
            .a
            .into_iter()
            .zip(value.b.into_iter().zip(value.c.into_iter()))
        {
            let a = ark_relations::r1cs::LinearCombination::<ArkScalar>(vec![(
                conv_scalar(a.0),
                ark_relations::r1cs::Variable::One,
            )]);
            let b = ark_relations::r1cs::LinearCombination::<ArkScalar>(vec![(
                conv_scalar(b.0),
                ark_relations::r1cs::Variable::One,
            )]);
            let c = ark_relations::r1cs::LinearCombination::<ArkScalar>(vec![(
                conv_scalar(c.0),
                ark_relations::r1cs::Variable::One,
            )]);
            cs.enforce_constraint(a, b, c).unwrap();
        }
        ArkCS {
            inner: ConstraintSystemRef::new(cs),
        }
    }
}
pub struct ProvingAssignment<S: PrimeField> {
    // Density of queries
    pub a_aux_density: zksync_bellman::source::DensityTracker,
    pub b_input_density: zksync_bellman::source::DensityTracker,
    pub b_aux_density: zksync_bellman::source::DensityTracker,

    // Evaluations of A, B, C polynomials
    pub a: Vec<Scalar<S>>,
    pub b: Vec<Scalar<S>>,
    pub c: Vec<Scalar<S>>,

    // Assignments of variables
    pub input_assignment: Vec<S>,
    pub aux_assignment: Vec<S>,
}

impl<S: PrimeField> ConstraintSystem<S> for ProvingAssignment<S> {
    type Root = Self;

    fn alloc<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<S, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.aux_assignment.push(f()?);
        self.a_aux_density.add_element();
        self.b_aux_density.add_element();

        Ok(Variable::new_unchecked(Index::Aux(
            self.aux_assignment.len() - 1,
        )))
    }

    fn alloc_input<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<S, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.input_assignment.push(f()?);
        self.b_input_density.add_element();

        Ok(Variable::new_unchecked(Index::Input(
            self.input_assignment.len() - 1,
        )))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<S>) -> LinearCombination<S>,
        LB: FnOnce(LinearCombination<S>) -> LinearCombination<S>,
        LC: FnOnce(LinearCombination<S>) -> LinearCombination<S>,
    {
        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());

        self.a.push(Scalar(eval(
            &a,
            // Inputs have full density in the A query
            // because there are constraints of the
            // form x * 0 = 0 for each input.
            None,
            Some(&mut self.a_aux_density),
            &self.input_assignment,
            &self.aux_assignment,
        )));
        self.b.push(Scalar(eval(
            &b,
            Some(&mut self.b_input_density),
            Some(&mut self.b_aux_density),
            &self.input_assignment,
            &self.aux_assignment,
        )));
        self.c.push(Scalar(eval(
            &c,
            // There is no C polynomial query,
            // though there is an (beta)A + (alpha)B + C
            // query for all aux variables.
            // However, that query has full density.
            None,
            None,
            &self.input_assignment,
            &self.aux_assignment,
        )));
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self) {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}
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
    use zksync_bellman::pairing::RawEncodable;

    type G1Aff = <Bls12 as Engine>::G1Affine;
    let mut bytes = [0u8; 96];
    bytes.copy_from_slice(gaff.into_uncompressed().as_ref());
    G1Aff::from_uncompressed_unchecked(&bytes).unwrap()
}

fn conv_zksync_g2aff(gaff: <zksync_bellman::bls12_381::Bls12 as zksync_bellman::Engine>::G2Affine) -> <Bls12 as Engine>::G2Affine {
    use zksync_bellman::pairing::RawEncodable;
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

#[cfg(test)]
mod test_translations {
    use super::*;

    #[test]
    fn test_g1_roundtrip() {
        type BellmanG1Aff = <Bls12 as Engine>::G1Affine;
        type ArkG1Aff = <Bls12_381 as Pairing>::G1Affine;

        let g1 = BellmanG1Aff::identity();
        let ark_g1 = conv_g1(g1);
        assert_eq!(ark_g1, ArkG1Aff::identity());
        let res = conv_ark_g1(ark_g1);
        assert_eq!(g1, res);

        let g1 = BellmanG1Aff::generator();
        let res = conv_ark_g1(conv_g1(g1));
        assert_eq!(g1, res);
    }

    #[test]
    fn test_g2_roundtrip() {
        type BellmanG2Aff = <Bls12 as Engine>::G2Affine;
        type ArkG2Aff = <Bls12_381 as Pairing>::G2Affine;

        let g2 = BellmanG2Aff::default();

        let ark_g2 = conv_g2(g2);
        assert!(ark_g2.is_on_curve());
        assert_eq!(ark_g2, ArkG2Aff::identity());
        let res = conv_ark_g2(ark_g2);
        assert_eq!(g2, res);

        let g2 = BellmanG2Aff::generator();
        let ark_g2 = conv_g2(g2);
        assert!(ark_g2.is_on_curve());
        let res = conv_ark_g2(ark_g2);
        assert_eq!(g2, res);
    }

}
