use bellman::gadgets::boolean::{AllocatedBit, Boolean};
use bellman::{ConstraintSystem, SynthesisError};
use group::ff::PrimeFieldBits;
use masp_primitives::ff::PrimeField;

pub fn field_into_boolean_vec_le<Scalar, CS, F>(
    mut cs: CS,
    value: Option<F>,
) -> Result<Vec<Boolean>, SynthesisError>
where
    F: PrimeFieldBits,
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    // Deconstruct in big-endian bit order
    let values = match value {
        Some(ref value) => {
            let field_char = F::char_le_bits();
            let mut field_char = field_char.into_iter().rev();

            let mut tmp = Vec::with_capacity(F::NUM_BITS as usize);

            let mut found_one = false;
            for b in value.to_le_bits().into_iter().rev() {
                // Skip leading bits
                found_one |= field_char.next().unwrap();
                if !found_one {
                    continue;
                }

                tmp.push(Some(b));
            }

            assert_eq!(tmp.len(), F::NUM_BITS as usize);

            tmp
        }
        None => vec![None; F::NUM_BITS as usize],
    };

    // Allocate in little-endian order
    let bits = values
        .into_iter()
        .rev()
        .enumerate()
        .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("bit {}", i)), b))
        .collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(bits.into_iter().map(Boolean::from).collect())
}
