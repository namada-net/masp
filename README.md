![MASP Logo](https://github.com/anoma/masp/blob/main/docs/logo.png)

# MASP Rust crates

This repository contains a set of Rust crates for
working with the Multi Asset Shielded Pool extensions of the Sapling circuits from Zcash.

## MASP Description

Using the original Sapling circuits for user defined assets, each asset or token type must have a separate shielded pool and asset type is transparent for all transactions. 

Using the MASP circuits, MASP notes can have shielded type, multiple assets can share the same shielded pool, and the asset types in a transaction can be shielded (except where there is transparent balance change)

The MASP is based on proposed multi-asset extensions to the Zcash protocol:

* https://github.com/zcash/zips/pull/269
* https://github.com/zcash/zcash/issues/830
* https://github.com/zcash/zcash/issues/2277#issuecomment-321106819 
* https://github.com/str4d/librustzcash/tree/funweek-uda-demo

The MASP attempts to keep most of the security, feature, and performance properties of the original Sapling circuits.

## Additional Components

This Rust repository, by itself, is not a complete implementation of the MASP, as it only includes circuits and some other functionality (transaction balancing, etc) while other functionality (notes, etc) is implemented elsewhere.

## Repository Structure

The `masp_proofs` crate contains the modified Spend and Output circuits to support multiple assets.

Much of the code that supports the original Sapling circuits can be shared and reused with the MASP circuits. Therefore, certain code from `zcash_primitives` and `zcash_proofs` is placed in `masp_primitives` and `masp_proofs`. 

New code related to asset types is included in `masp_primitives`. 

Zcash code that is not relevant to the circuits (e.g. protocol, transaction, consensus, blockchain code) has been removed.

The `masp` crate contains the C language bindings for accessing the circuits.

The `docs` folder includes technical documentation about the circuit changes.

## Asset Identifiers

The major difference between MASP and original Sapling is the use of asset identifiers to identify distinct asset types. An asset identifier is an internal 32 byte string that uniquely identifies each asset in the circuits. 

The asset identifier is independent of a specific token standard. 

There are certain requirements for deriving asset identifiers. The `AssetType` struct in `masp_primitives` (also via the C bindings) gives functions to derive asset identifiers.

## Convert Circuit

In addition to the modified Spend and Output circuits, the MASP includes a Convert circuit that allows shielded conversions between distinct asset types according to a public list of conversion ratios. This is not a fully general exchange mechanism, but can be used to issue shielded rewards or incentives inside a pool. 

The Convert circuit provides a mechanism where burning and minting of asset types can be enabled by adding Convert value commitments in transaction and ensuring the homomorphic sum of Spend, Output and Convert value commitments to be zero.

The Convert value commitment is constructed from AllowedConversion which was published earlier in AllowedConversion Tree. The AllowedConversion defines the allowed conversion assets. The AllowedConversion Tree is a merkle hash tree stored in the ledger.

## Trusted Setup

The Zcash Sapling trusted setup parameters cannot be completely reused for the MASP. Parameter location and hashes must be added to `masp_proofs` following a suitable MPC ceremony.

## New projects

For new projects relying on this library, the `redjubjub` dependency pulls `reddsa` which contains some hardcoded values (personalizations and basepoints). If you need different values consider forking `reddsa`, modifying it to your needs and patching it in the root manifest.

## Security Warnings

These libraries are currently under development and have not been fully-reviewed.

## Audits

The following audits have been done on the MASP protocol:

* [Inference AG](https://github.com/anoma/namada/blob/main/audits/report-anoma-inference.pdf)
* [Least Authority](https://leastauthority.com/static/publications/LeastAuthority_Tezos_Foundation_Multi_Asset_Shielded_Pool_Audit_Report.pdf)

In addition, the original Zcash Sapling protocol was audited without the MASP extensions:

* [Kudelski Security](https://cybermashup.files.wordpress.com/2018/08/zcash-audit.pdf)
* [Least Authority](https://leastauthority.com/static/publications/LeastAuthority-Zcash-Overwinter%2BSapling-Specification-Final-Audit-Report.pdf)
* [NCC Group](https://research.nccgroup.com/wp-content/uploads/2020/07/NCC_Group_Zcash2018_Public_Report_2019-01-30_v1.3.pdf)

## License

All code in this workspace is licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
