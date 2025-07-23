use blake2b_simd::Hash as Blake2bHash;

use crate::transaction::{
    Authorization, TransactionData, TransparentDigests, TxDigests,
    sighash::{SignableInput, TransparentAuthorizingContext},
    transparent,
    txid::{hash_transparent_txid_data, to_hash},
};

/// Implements [ZIP 244 section S.2](https://zips.z.cash/zip-0244#s-2-transparent-sig-digest).
fn transparent_sig_digest<A: TransparentAuthorizingContext>(
    tx_data: Option<(&transparent::Bundle<A>, &TransparentDigests<Blake2bHash>)>,
    _input: &SignableInput,
) -> Blake2bHash {
    match tx_data {
        // No transparent inputs or outputs.
        None => hash_transparent_txid_data(None),
        // No transparent inputs, or coinbase.
        Some((_bundle, txid_digests)) => hash_transparent_txid_data(Some(txid_digests)),
    }
}

/// Implements the [Signature Digest section of ZIP 244](https://zips.z.cash/zip-0244#signature-digest)
pub fn v5_signature_hash<
    TA: TransparentAuthorizingContext,
    A: Authorization<TransparentAuth = TA>,
>(
    tx: &TransactionData<A>,
    signable_input: &SignableInput,
    txid_parts: &TxDigests<Blake2bHash>,
) -> Blake2bHash {
    // The caller must provide the transparent digests if and only if the transaction has a
    // transparent component.
    assert_eq!(
        tx.transparent_bundle.is_some(),
        txid_parts.transparent_digests.is_some()
    );

    to_hash(
        tx.version,
        tx.consensus_branch_id,
        txid_parts.header_digest,
        transparent_sig_digest(
            tx.transparent_bundle
                .as_ref()
                .zip(txid_parts.transparent_digests.as_ref()),
            signable_input,
        ),
        txid_parts.sapling_digest,
    )
}
