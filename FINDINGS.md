# What the work found

Writing the Lean model of BIP 458, proving the theorems and testing the reference code and the C module against the model turned up the points below. Each one names its evidence and a change that would settle it. None of them is a way to forge an aggregate signature or to learn a key.

The BIP text, the test vectors and `halfagg.py` are those of bitcoin/bips at commit [`a7f9132`](https://github.com/bitcoin/bips/tree/a7f91321f25b5be8d93e901775621c21519e80b7/bip-0458), where they are as on its master branch on 2026-11-26. The C module is [bitcoin-core/secp256k1#1566](https://github.com/bitcoin-core/secp256k1/pull/1566) at commit [`c7ed5e0`](https://github.com/bitcoin-core/secp256k1/commit/c7ed5e0a0dbc69f5f75bc00e516ccd5ee1033e25). On 2026-11-26 none of the proposed changes had been submitted.

## The text of BIP 458

| | Finding | Evidence | Proposed change |
|---|---|---|---|
| 1 | The Motivation says more than a verifier learns. It reads "If the verifier can successfully verify the aggregate signature, the verifier can be sure that the individual signatures would have passed verification." An aggregate that verifies can be made from signatures that do not. | `aggregate_accepts_invalid`: moving `δ ≠ 0` between the `s` values of the first two signatures, weighted by `z₁`, makes the second one invalid and leaves the aggregate unchanged. What holds is `halfagg_unforgeable`, the owner of an honest key signed its message, and `halfagg_knowledge`, whoever made the aggregate knew a BIP 340 signature for every item. | Say what the verifier can be sure of, for example that whoever produced the aggregate knew a valid signature for every public key and message. |
| 2 | The Rationale cites a security proof in the random oracle model for half-aggregation. That proof is for the variant in which every randomizer hashes the whole list. BIP 458 derives `zᵢ` from the first `i + 1` items so that signatures can be added later, and for this scheme the cited papers have a proof only in the algebraic group model. | [REVIEW.md](REVIEW.md#questions-to-ask), "Could unforgeability be proven without the algebraic group model?", with the theorem and remark numbers of both papers. `halfagg_unforgeable` is the theorem of the algebraic group model for BIP 458's scheme. | Say in the Rationale which proof is for the scheme of the BIP. |

## The test vectors

| | Finding | Evidence | Proposed change |
|---|---|---|---|
| 3 | No test vector needs the check `s < n` of `VerifyAggregate`. The three vectors with an `s` out of range have one signature each, and a verifier that reduces `s` modulo `n` rejects them as well, because the reduced value fails the equation. The empty aggregate with `s = n` tells the two verifiers apart: `0` passes for the empty list. | `halfagg.py` rejects all three with `s` reduced. `verifyAggregateBytes_unique` is what the check is for: without it the empty aggregate has the encodings `bytes(0)` and `bytes(n)`. `scripts/fuzz.py` generates the input. | A `VerifyAggregate` vector with the empty list and `aggsig = bytes(n)`, expected to fail. |

## The C module

| | Finding | Evidence | Proposed change |
|---|---|---|---|
| 4 | The unit tests pass for a module without the check `s < n` in `aggverify`. | `scripts/mutate_secp256k1.py`: the unit tests notice 19 of 21 one-line changes. The [README](README.md#mutation-test-of-the-c-module) has the details. | A unit test with the empty aggregate and `s = n`, which the vector of 3 gives. |
| 5 | The module has no exhaustive test. One change can only be noticed on a small group: `aggverify` reducing an `r ≥ p` modulo `p`. On secp256k1 nobody can produce a signature whose nonce has an x-coordinate below `2^256 - p`. | `scripts/mutate_secp256k1.py` with the exhaustive tests as a third set. Together the three sets notice all 21 changes. | `patches/secp256k1-halfagg-exhaustive-tests.patch` adds the test. It passes on the groups of order 13 and 199. |
