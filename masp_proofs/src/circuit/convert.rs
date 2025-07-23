//! The Convert circuit.

use bellman::{Circuit, ConstraintSystem, SynthesisError};

use masp_primitives::sapling::ValueCommitment;

use super::pedersen_hash;
use crate::circuit::sapling::expose_value_commitment;

use bellman::gadgets::Assignment;
use bellman::gadgets::boolean;
use bellman::gadgets::num;

pub const TREE_DEPTH: usize = masp_primitives::sapling::SAPLING_COMMITMENT_TREE_DEPTH;

/// This is an instance of the `Convert` circuit.
pub struct Convert {
    /// Minting value commitment
    pub value_commitment: Option<ValueCommitment>,

    /// The authentication path of the commitment in the tree
    pub auth_path: Vec<Option<(bls12_381::Scalar, bool)>>,

    /// The anchor of the allowable convert-and-mints; the root of the tree.
    pub anchor: Option<bls12_381::Scalar>,
}

impl Circuit<bls12_381::Scalar> for Convert {
    fn synthesize<CS: ConstraintSystem<bls12_381::Scalar>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        // Handle the value; we'll need it later for the
        // dummy input check.
        let mut value_num = num::Num::zero();

        // Get the value in little-endian bit order
        let (asset_generator_bits, value_bits) =
            expose_value_commitment(cs.namespace(|| "value commitment"), self.value_commitment)?;

        {
            // Compute the note's value as a linear combination
            // of the bits.
            let mut coeff = bls12_381::Scalar::one();
            for bit in &value_bits {
                value_num = value_num.add_bool_with_coeff(CS::one(), bit, coeff);
                coeff = coeff.double();
            }
        }
        assert_eq!(asset_generator_bits.len(), 256);

        // Compute the hash of the note contents
        let cm = pedersen_hash::pedersen_hash(
            cs.namespace(|| "note content hash"),
            pedersen_hash::Personalization::NoteCommitment,
            &asset_generator_bits,
        )?;

        // This is an injective encoding, as cur is a
        // point in the prime order subgroup.
        let mut cur = cm.get_u().clone();

        // Ascend the merkle tree authentication path
        for (i, e) in self.auth_path.into_iter().enumerate() {
            let cs = &mut cs.namespace(|| format!("merkle tree hash {}", i));

            // Determines if the current subtree is the "right" leaf at this
            // depth of the tree.
            let cur_is_right = boolean::Boolean::from(boolean::AllocatedBit::alloc(
                cs.namespace(|| "position bit"),
                e.map(|e| e.1),
            )?);

            // Witness the authentication path element adjacent
            // at this depth.
            let path_element =
                num::AllocatedNum::alloc(cs.namespace(|| "path element"), || Ok(e.get()?.0))?;

            // Swap the two if the current subtree is on the right
            let (ul, ur) = num::AllocatedNum::conditionally_reverse(
                cs.namespace(|| "conditional reversal of preimage"),
                &cur,
                &path_element,
                &cur_is_right,
            )?;

            // We don't need to be strict, because the function is
            // collision-resistant. If the prover witnesses a congruency,
            // they will be unable to find an authentication path in the
            // tree with high probability.
            let mut preimage = vec![];
            preimage.extend(ul.to_bits_le(cs.namespace(|| "ul into bits"))?);
            preimage.extend(ur.to_bits_le(cs.namespace(|| "ur into bits"))?);

            // Compute the new subtree value
            cur = pedersen_hash::pedersen_hash(
                cs.namespace(|| "computation of pedersen hash"),
                pedersen_hash::Personalization::MerkleTree(i),
                &preimage,
            )?
            .get_u()
            .clone(); // Injective encoding
        }

        {
            let real_anchor_value = self.anchor;

            // Allocate the "real" anchor that will be exposed.
            let rt = num::AllocatedNum::alloc(cs.namespace(|| "conditional anchor"), || {
                Ok(*real_anchor_value.get()?)
            })?;

            // (cur - rt) * value = 0
            // if value is zero, cur and rt can be different
            // if value is nonzero, they must be equal
            cs.enforce(
                || "conditionally enforce correct root",
                |lc| lc + cur.get_variable() - rt.get_variable(),
                |lc| lc + &value_num.lc(bls12_381::Scalar::one()),
                |lc| lc,
            );

            // Expose the anchor
            rt.inputize(cs.namespace(|| "anchor"))
        }
    }
}

#[test]
fn test_convert_circuit_with_bls12_381() {
    use bellman::gadgets::test::*;
    use group::{Curve, ff::Field, ff::PrimeField, ff::PrimeFieldBits};
    use masp_primitives::{
        asset_type::AssetType, convert::AllowedConversion, sapling::pedersen_hash,
        transaction::components::ValueSum,
    };
    use rand_core::{RngCore, SeedableRng};
    use rand_xorshift::XorShiftRng;

    let mut rng = XorShiftRng::from_seed([
        0x58, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let tree_depth = 32;

    for _ in 0..10u32 {
        let i = rng.next_u32();
        let spend_asset = AssetType::new(format!("asset {}", i).as_bytes()).unwrap();
        let output_asset = AssetType::new(format!("asset {}", i + 1).as_bytes()).unwrap();
        let mint_asset = AssetType::new(b"reward").unwrap();

        let spend_value = -(i as i128 + 1);
        let output_value = i as i128 + 1;
        let mint_value = i as i128 + 1;

        let allowed_conversion: AllowedConversion = (ValueSum::from_pair(spend_asset, spend_value)
            + ValueSum::from_pair(output_asset, output_value)
            + ValueSum::from_pair(mint_asset, mint_value))
        .into();

        let value = rng.next_u64();

        let value_commitment =
            allowed_conversion.value_commitment(value, jubjub::Fr::random(&mut rng));

        let auth_path =
            vec![Some((bls12_381::Scalar::random(&mut rng), rng.next_u32() % 2 != 0)); tree_depth];

        {
            let expected_value_commitment =
                jubjub::ExtendedPoint::from(value_commitment.commitment()).to_affine();

            let cmu = allowed_conversion.cmu();
            let mut cur = cmu;

            for (i, val) in auth_path.clone().into_iter().enumerate() {
                let (uncle, b) = val.unwrap();

                let mut lhs = cur;
                let mut rhs = uncle;

                if b {
                    ::std::mem::swap(&mut lhs, &mut rhs);
                }

                let lhs = lhs.to_le_bits();
                let rhs = rhs.to_le_bits();

                cur = jubjub::ExtendedPoint::from(pedersen_hash::pedersen_hash(
                    pedersen_hash::Personalization::MerkleTree(i),
                    lhs.iter()
                        .by_vals()
                        .take(bls12_381::Scalar::NUM_BITS as usize)
                        .chain(
                            rhs.iter()
                                .by_vals()
                                .take(bls12_381::Scalar::NUM_BITS as usize),
                        ),
                ))
                .to_affine()
                .get_u();
            }

            let mut cs = TestConstraintSystem::new();

            let instance = Convert {
                value_commitment: Some(value_commitment.clone()),
                auth_path: auth_path.clone(),
                anchor: Some(cur),
            };

            instance.synthesize(&mut cs).unwrap();

            assert!(cs.is_satisfied());

            assert_eq!(cs.num_constraints(), 47358);
            assert_eq!(
                cs.hash(),
                "f74b47ef6e59081548f81f5806bd15b1f4a65d2e57681e6db2b8db7eef2ff814"
            );

            assert_eq!(cs.num_inputs(), 4);
            assert_eq!(cs.get_input(0, "ONE"), bls12_381::Scalar::one());
            assert_eq!(
                cs.get_input(1, "value commitment/commitment point/u/input variable"),
                expected_value_commitment.get_u()
            );
            assert_eq!(
                cs.get_input(2, "value commitment/commitment point/v/input variable"),
                expected_value_commitment.get_v()
            );
            assert_eq!(cs.get_input(3, "anchor/input variable"), cur);
        }
    }
}
