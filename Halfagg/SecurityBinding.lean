import Halfagg.SecurityROM

/-!
# Binding of half-aggregation: definitions

The review surface for `halfagg_binding` (`Halfagg/Binding.lean`).

Unforgeability says that an honest key signed its message. Binding says that an
aggregate signature belongs to one list of `(pk, m)` pairs: nobody can produce
an aggregate that `VerifyAggregate` accepts for two different lists. This is the
game CK-ASBS of Chalkias, Garillot, Kondi and Nikolaenko
(https://eprint.iacr.org/2021/350, Definition 4 and Theorem 6), for BIP458's
scheme. The adversary chooses every key and gets no signing oracle.

Both hashes are random oracles. As in `aggExperimentROM`, the game samples the
whole challenge hash table first and the randomizer hash lazily. BIP458 does not
state this property.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)
variable [SampleableType H] (red : H → ZMod n)

/-- A binding adversary's oracles: uniform sampling, the challenge hash and the
randomizer hash. -/
abbrev BindSpec (n : ℕ) (H X M : Type) := (unifSpec + ChalSpec n X M) + RandSpec H X M

/-- A binding adversary outputs an aggregate signature and two lists of
`(pk, m)` pairs. -/
structure BindAdversary (n : ℕ) (H X M : Type) where
  main : OracleComp (BindSpec n H X M) (AggSig n X × List (X × M) × List (X × M))

/-- Answer challenge-hash queries from the table `g` and pass the rest on. -/
def answerChalB (g : M × (X × X) → ZMod n) :
    QueryImpl (BindSpec n H X M) (OracleComp (unifSpec + RandSpec H X M))
  | .inl (.inl k) => liftM ((unifSpec + RandSpec H X M).query (.inl k))
  | .inl (.inr key) => pure (g key)
  | .inr L => liftM ((unifSpec + RandSpec H X M).query (.inr L))

/-- The adversary wins if the two lists differ and `VerifyAggregate` accepts the
aggregate for both, with the randomizers `zs` and `zs'`. -/
def bindWins (challenge : X → X → M → ZMod n) (agg : AggSig n X) (pm pm' : List (X × M))
    (zs zs' : List (ZMod n)) : Bool :=
  decide (pm ≠ pm') && verifyWith C challenge (fun i => zs.getD i 0) agg pm &&
    verifyWith C challenge (fun i => zs'.getD i 0) agg pm'

/-- The binding game for a fixed challenge hash: run the adversary, draw the
randomizers of both lists from the randomizer hash and check `bindWins`. -/
noncomputable def bindGame (challenge : X → X → M → ZMod n)
    (A : OracleComp (unifSpec + RandSpec H X M) (AggSig n X × List (X × M) × List (X × M))) :
    OracleComp (unifSpec + RandSpec H X M) Bool := do
  let out ← A
  let zs ← (List.range out.1.rs.length).mapM (zQuery red (items out.2.1 out.1.rs))
  let zs' ← (List.range out.1.rs.length).mapM (zQuery red (items out.2.2 out.1.rs))
  return bindWins C challenge out.1 out.2.1 out.2.2 zs zs'

/-- **The binding game** (CK-ASBS of Chalkias, Garillot, Kondi and Nikolaenko,
for BIP458's scheme), with both hashes as random oracles: sample the challenge
hash table, then play `bindGame` with a lazily sampled randomizer hash. -/
noncomputable def bindExperiment [SampleableType (M × (X × X) → ZMod n)]
    (A : BindAdversary n H X M) : ProbComp Bool := do
  let g ← $ᵗ (M × (X × X) → ZMod n)
  (simulateQ (RandSpec H X M).romImpl
    (bindGame C red (hOf g) (simulateQ (answerChalB g) A.main))).run' ∅

/-- The adversary's success probability. -/
noncomputable def bindAdvantage [SampleableType (M × (X × X) → ZMod n)]
    (A : BindAdversary n H X M) : ℝ≥0∞ :=
  Pr{let b ← bindExperiment C red A}[b = true]

/-- Whether an oracle call is a challenge-hash query. -/
def isChalB : (ℕ ⊕ M × (X × X)) ⊕ List (Item X M) → Bool
  | .inl (.inr _) => true
  | _ => false

/-- Whether an oracle call is a randomizer-hash query. -/
def isRandB : (ℕ ⊕ M × (X × X)) ⊕ List (Item X M) → Bool
  | .inr _ => true
  | _ => false

end Halfagg.Security
