# Reviewing halfagg-lean

Lean checks the proofs. A reviewer checks that the statements say what they should. Everything under `Halfagg/Proofs/` can stay unread, because a wrong proof does not compile. A wrong definition does.

## What to read

About 900 lines decide whether the results mean anything.

1. `Halfagg/Basic.lean`, the definitions before the first theorem. Compare `incAggregate`, `aggregate` and `verifyWith` with the algorithms in BIP 458.
2. `Halfagg/Security.lean`, all of it. The header lists the modelling choices and the limitations.
3. `Halfagg/Unforgeability.lean`, the four theorem statements.
4. `Halfagg/SecurityROM.lean` and the statements in `Halfagg/UnforgeabilityROM.lean`, for the version with the challenge hash as a random oracle.

taproot-lean supplies the curve interface, `BIP340.sign` and `BIP340.verify`. VCVio supplies the random oracle and the BIP 340 game (`SignatureAlg.unforgeableAdvantage`). agm-lean supplies the algebraic adversary. A full review reads those definitions too.

## Questions to ask

**Is the game the standard one?** `aggExperiment` and `aggWins` never mention representations or the reduction. The adversary picks every public key except the target. It wins with any verifying list that has one item under the target key with a message it never had signed.

**Is the forger class too small?** `AlgForger` is agm-lean's adversary. It must explain every point it sends as a combination of `G`, the target key and the nonce points of the signatures it received. `erase` drops the explanations, so the theorem bounds the forger's advantage in the standard game. The x-coordinates a forger hashes come from points it explained, with one exception. After an item that fails `lift_x`, a randomizer request may contain arbitrary encodings (`rawTail`). `aggWins_lifts` is the reason that is safe.

**Does the reduction cheat?** `reduction` gets a BIP 340 public key and a signing oracle and nothing else. It answers randomizer requests from its own table. `reduction_sign_queries` shows it asks for no signature the forger did not ask for. VCVio's game rejects a forgery on a signed message.

**Do the random-oracle forger and reduction only query the oracle?** `RomForger.main` and `reductionROM` are oracle programs over a challenge-hash oracle, so they cannot read the table. `reductionROM_bound` counts the reduction's queries: the forger's signing requests, and `qH + qS + ℓ + 1` hash queries for a forger with `qH` hash queries, `qS` signing requests and forgeries of at most `ℓ` items. The game samples the whole table first and then answers queries from it. For a finite domain that is the same as lazy sampling (`rom_eq_table`).

**Is the theorem vacuous?** `Halfagg/Examples.lean` has a forger that satisfies the hypotheses and a transcript that satisfies the win predicate. The curve hypothesis `hx0` holds for secp256k1 (`Halfagg/Proofs/Secp256k1.lean`).

**What does the bound say?** `(q + 1)/n`, where `q` counts randomizer requests, as in Chen and Zhao. It is tight up to one query: `grinder_advantage` in `Halfagg/Tightness.lean` proves that a forger who tries `q` second items wins with probability at least `1 - ((n - 1)/n)^q`.

## What the theorem does not say

- Only the step from half-aggregation to BIP 340 is tight. `halfagg_dlog` inherits the forking-lemma loss of BIP 340's own proof, which is quadratic in the forger's success probability.
- The random-oracle version needs a finite message type. BIP 458's 32-byte messages are one.
- No theorem bounds running time. Without that, `halfagg_unforgeable` alone would allow a reduction that breaks BIP 340 by brute force. This one does not, and `reduction` is short enough to check by reading.
- The algebraic group model is a restriction on the forger. A forger that hashes x-coordinates of curve points it cannot explain is outside the theorem.
- The byte encodings have no theorems. `Halfagg/Vectors.lean` runs BIP 458's 53 test vectors against the model. `scripts/fuzz.py` compares the model with the Python reference and with libsecp256k1 on random inputs.

## Machine checks

- `lake build` compiles every proof and fails if the axioms of a main result change (`Halfagg/Summary.lean`).
- `scripts/check.sh` searches the sources for `sorry`, new axioms, unsafe code and stray `native_decide`.
- `lake env leanchecker Halfagg` replays every project module in the kernel, without the elaborator. It rejects a module that adds a false theorem behind the kernel's back, which `#print axioms` does not notice.

Mutating the model is a useful test. Three mutants that weakened the randomizer broke the proof at `badKey_prob` or `extract_or_bad`. Removing the `lifts` check from `rawTail` breaks it at `covered_rawTail`.
