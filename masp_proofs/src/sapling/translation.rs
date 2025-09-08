//! An egregious set of ill-advised hacks made in an attempt to benchmark the
//! speed of building groth16 proofs relative to bellman with as little code
//! changes as possible.

pub mod bellperpson;
pub mod arkworks;

use std::ops::{AddAssign, Mul};

use bellman::domain::Scalar;
use bellman::{ConstraintSystem, Index, LinearCombination, SynthesisError, Variable};
use bellperson::multiexp::DensityTracker;
use bls12_381::Bls12;

use masp_primitives::ff::PrimeField;
use pairing::Engine;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub type BellmanScalar = <Bls12 as Engine>::Fr;


fn eval<S: PrimeField>(
    lc: &LinearCombination<S>,
    mut input_density: Option<&mut DensityTracker>,
    mut aux_density: Option<&mut DensityTracker>,
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

pub struct ProvingAssignment<S: PrimeField> {
    // Density of queries
    pub a_aux_density: DensityTracker,
    pub b_input_density: DensityTracker,
    pub b_aux_density: DensityTracker,

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
