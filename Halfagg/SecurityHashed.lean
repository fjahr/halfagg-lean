import Halfagg.SecurityTight
import Halfagg.SecurityBinding

/-!
# The challenge hash as BIP340 computes it: definitions

BIP340 computes a challenge as `int(hash(r ‖ pk ‖ m)) mod n` from a 256-bit
hash. In `Halfagg/SecurityROM.lean` the random oracle for the challenge hash
returns a uniform scalar. Here it returns a uniform element of a type `Hc` of
hash outputs, for BIP340 the 256-bit strings. The adversary sees the outputs
and the game reduces them to scalars with `redc`.

* **Forger and game.** `RomForgerH` and `aggExperimentROMH` are `RomForger` and
  `aggExperimentROM` with that oracle.
* **Back to scalars.** `RomForgerH.viaRep` makes a `RomForger` from a
  `RomForgerH`: it asks the oracle with scalar answers and hands the forger the
  hash output `rep c` for the answer `c`. The theorems of
  `Halfagg/UnforgeabilityHashed.lean` compare the two games and so carry every
  bound for `RomForger` over.
* **Binding.** `BindAdversaryH`, `bindExperimentH` and `BindAdversaryH.viaRep`
  are the same for the game of `Halfagg/SecurityBinding.lean`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security

attribute [local instance] smulVal

-- Uniform nonces, as in `Halfagg/SecurityROM.lean`.
attribute [local instance] NonceGen.uniform

variable {n : ℕ} [Fact n.Prime] {H Hc E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)
variable [SampleableType H] (red : H → ZMod n) (redc : Hc → ZMod n)

/-! ## Unforgeability -/

/-- The challenge hash as an oracle on `(m, (r, pk))` with answers in `Hc`. -/
abbrev ChalSpecH (Hc X M : Type) := (M × (X × X)) →ₒ Hc

/-- A forger's oracles: the challenge hash with answers in `Hc` and the requests
of an `AlgForger`. -/
abbrev RomForgerSpecH (n : ℕ) (H Hc E X M : Type) :=
  ChalSpecH Hc X M + explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)

/-- Answer challenge-hash queries from the table `g` and pass requests on. -/
def answerChalH (g : M × (X × X) → Hc) :
    QueryImpl (RomForgerSpecH n H Hc E X M)
      (OracleComp (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)))
  | .inl key => pure (g key)
  | .inr t => liftM ((explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)).query t)

/-- An algebraic forger with oracle access to the challenge hash, whose answers
are hash outputs in `Hc`. -/
structure RomForgerH (n : ℕ) (H Hc E X M : Type) [AddCommGroup E] where
  main : Message Unit (Pts E) →
    OracleComp (RomForgerSpecH n H Hc E X M) (Explained (ZMod n) (Out n M) (Pts E))
  algebraic : ∀ (g : M × (X × X) → Hc) input,
    IsAlgebraic input.groups (simulateQ (answerChalH g) (main input))

/-- The forger with its challenge queries answered from the table `g`. -/
def RomForgerH.at (F : RomForgerH n H Hc E X M) (g : M × (X × X) → Hc) :
    AlgForger n H E X M where
  main input := simulateQ (answerChalH g) (F.main input)
  algebraic := F.algebraic g

/-- **The game with the challenge hash as BIP340 computes it**: sample the table
of hash outputs, then play the game of `aggExperiment` with the challenge
`redc (g (m, (r, pk)))`. The forger gets the hash outputs. -/
noncomputable def aggExperimentROMH [SampleableType (M × (X × X) → Hc)]
    (F : RomForgerH n H Hc E X M) : ProbComp Bool := do
  let g ← $ᵗ (M × (X × X) → Hc)
  (simulateQ (RandSpec H X M).romImpl
    (aggExperiment C (hOf fun key => redc (g key)) red (erase C (F.at g)))).run' ∅

/-- The forger's success probability. -/
noncomputable def aggAdvantageROMH [SampleableType (M × (X × X) → Hc)]
    (F : RomForgerH n H Hc E X M) : ℝ≥0∞ :=
  Pr{let b ← aggExperimentROMH C red redc F}[b = true]

/-- Ask the oracle with scalar answers and pass the answer `c` on as the hash
output `rep c`. Requests pass through. -/
def repChal (rep : ZMod n → Hc) :
    QueryImpl (RomForgerSpecH n H Hc E X M) (OracleComp (RomForgerSpec n H E X M))
  | .inl key => rep <$> (liftM ((RomForgerSpec n H E X M).query (.inl key)) :
      OracleComp (RomForgerSpec n H E X M) (ZMod n))
  | .inr t => liftM ((RomForgerSpec n H E X M).query (.inr t))

/-- A table of scalars read through `repChal` is the table of the hash outputs
`rep (g key)`. -/
theorem answerChal_repChal (rep : ZMod n → Hc) (g : M × (X × X) → ZMod n) {α : Type}
    (prog : OracleComp (RomForgerSpecH n H Hc E X M) α) :
    simulateQ (answerChal g) (simulateQ (repChal rep) prog) =
      simulateQ (answerChalH fun key => rep (g key)) prog := by
  induction prog using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    rcases t with key | t
    · have h1 : simulateQ (answerChal g) (repChal (H := H) (E := E) rep (.inl key)) =
          pure (rep (g key)) := by
        simp [repChal, answerChal]
      rw [h1]
      simp only [answerChalH, pure_bind]
      exact ih _
    · have h1 : simulateQ (answerChal g) (repChal (H := H) (Hc := Hc) (E := E) rep (.inr t)) =
          liftM ((explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)).query t) := by
        simp [repChal, answerChal]
      rw [h1]
      exact bind_congr fun u => ih u

/-- **The forger for the oracle with scalar answers.** It runs `F` and answers a
challenge query with the hash output `rep c` for the oracle's answer `c`. -/
def RomForgerH.viaRep (rep : ZMod n → Hc) (F : RomForgerH n H Hc E X M) :
    RomForger n H E X M where
  main input := simulateQ (repChal rep) (F.main input)
  algebraic g input := by
    rw [answerChal_repChal]
    exact F.algebraic _ input

/-- **The forger explains the nonce of every challenge-hash query**:
`ExplainsNonces` for a forger whose challenge hash has answers in `Hc`. -/
def ExplainsNoncesH {α : Type} (prog : OracleComp (RomForgerSpecH n H Hc E X M) α) :
    List X → Prop :=
  OracleComp.recOn (motive := fun _ => List X → Prop) prog
    (fun _ _ => True)
    (fun t _ next seen =>
      match t, next with
      | .inl key, next => key.2.1 ∈ seen ∧ ∀ e, next e seen
      | .inr q, next => ∀ rep, next rep
          (if isRand q.value.data then (q.value.groups ()).map C.x ++ seen else seen))

/-! ## Binding -/

/-- A binding adversary's oracles, with challenge hash answers in `Hc`. -/
abbrev BindSpecH (H Hc X M : Type) := (unifSpec + ChalSpecH Hc X M) + RandSpec H X M

/-- A binding adversary whose challenge hash has answers in `Hc`. -/
structure BindAdversaryH (n : ℕ) (H Hc X M : Type) where
  main : OracleComp (BindSpecH H Hc X M) (AggSig n X × List (X × M) × List (X × M))

/-- Answer challenge-hash queries from the table `g` and pass the rest on. -/
def answerChalBH (g : M × (X × X) → Hc) :
    QueryImpl (BindSpecH H Hc X M) (OracleComp (unifSpec + RandSpec H X M))
  | .inl (.inl k) => liftM ((unifSpec + RandSpec H X M).query (.inl k))
  | .inl (.inr key) => pure (g key)
  | .inr L => liftM ((unifSpec + RandSpec H X M).query (.inr L))

/-- **The binding game with the challenge hash as BIP340 computes it**: sample
the table of hash outputs, then play `bindGame` with the challenge
`redc (g (m, (r, pk)))`. The adversary gets the hash outputs. -/
noncomputable def bindExperimentH [SampleableType (M × (X × X) → Hc)]
    (A : BindAdversaryH n H Hc X M) : ProbComp Bool := do
  let g ← $ᵗ (M × (X × X) → Hc)
  (simulateQ (RandSpec H X M).romImpl
    (bindGame C red (hOf fun key => redc (g key)) (simulateQ (answerChalBH g) A.main))).run' ∅

/-- The adversary's success probability. -/
noncomputable def bindAdvantageH [SampleableType (M × (X × X) → Hc)]
    (A : BindAdversaryH n H Hc X M) : ℝ≥0∞ :=
  Pr{let b ← bindExperimentH C red redc A}[b = true]

/-- Ask the oracle with scalar answers and pass the answer `c` on as the hash
output `rep c`. The other queries pass through. -/
def repChalB (rep : ZMod n → Hc) :
    QueryImpl (BindSpecH H Hc X M) (OracleComp (BindSpec n H X M))
  | .inl (.inl k) => liftM ((BindSpec n H X M).query (.inl (.inl k)))
  | .inl (.inr key) => rep <$> (liftM ((BindSpec n H X M).query (.inl (.inr key))) :
      OracleComp (BindSpec n H X M) (ZMod n))
  | .inr L => liftM ((BindSpec n H X M).query (.inr L))

/-- **The binding adversary for the oracle with scalar answers.** -/
def BindAdversaryH.viaRep (rep : ZMod n → Hc) (A : BindAdversaryH n H Hc X M) :
    BindAdversary n H X M where
  main := simulateQ (repChalB rep) A.main

end Halfagg.Security
