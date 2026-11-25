import Halfagg.Proofs.Scheme
import Halfagg.Proofs.LoggedRun

/-!
# The annotated experiment and its bad event

`annExperiment` runs the forger through the reduction's bookkeeping (`coreImpl`)
with real signatures and a random oracle on *annotated* lists, and returns the
transcript `(pk, items, s, zs, signed)`. Because a list's representations are
part of its oracle key, the bad event of Chen and Zhao's proof is a property of
a key and the oracle's answer table (`badKey`), and resampling the answer at
that key makes it hold with probability at most `μ` (`badKey_prob`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security Halfagg.LoggedRun

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)
variable [SampleableType H] {red : H → ZMod n}

/-- `(pk, items, s, zs, signed)`. -/
abbrev Transcript (n : ℕ) (X M : Type) :=
  X × List (AItem n X M) × ZMod n × List (ZMod n) × List M

/-- The verifier's randomizer for annotated items. -/
def zQueryAnn (red : H → ZMod n) (items : List (AItem n X M)) (i : ℕ) :
    OracleComp (unifSpec + AnnSpec n H X M) (ZMod n) :=
  if i = 0 then pure 1
  else red <$> liftM ((unifSpec + AnnSpec n H X M).query (.inr (items.take (i + 1))))

/-- The reduction's bookkeeping with real signatures under `sk` and the
annotated random oracle. -/
noncomputable def annImpl [NonceGen n M] (pk : X) (sk : ZMod n) :
    QueryImpl (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M))
      (StateT (Core n X M) (OracleComp (unifSpec + AnnSpec n H X M))) :=
  coreImpl C challenge pk
    (fun k => liftM ((unifSpec + AnnSpec n H X M).query (.inl k)))
    (fun l => liftM ((unifSpec + AnnSpec n H X M).query (.inr l)))
    (fun msg => (bip340 (M := M) C challenge
      (OracleComp (unifSpec + AnnSpec n H X M))).sign pk sk msg)

/-- Key generation and the forger's run. -/
noncomputable def annPhase1 [NonceGen n M] (F : AlgForger n H E X M) :
    OracleComp (unifSpec + AnnSpec n H X M)
      (X × Explained (ZMod n) (Out n M) (Pts E) × Core n X M) := do
  let ks ← (bip340 (M := M) C challenge (OracleComp (unifSpec + AnnSpec n H X M))).keygen
  let r ← (simulateQ (annImpl (H := H) C challenge ks.1 ks.2)
    (F.main (initial C ((C.liftX ks.1).getD 0)))).run Core.init
  return (ks.1, r.1, r.2)

/-- The annotated experiment. -/
noncomputable def annExperiment [NonceGen n M] (red : H → ZMod n) (F : AlgForger n H E X M) :
    OracleComp (unifSpec + AnnSpec n H X M) (Transcript n X M) := do
  let r ← annPhase1 C challenge F
  let zs ← (List.range (finalItems C r.2.1 r.2.2).length).mapM
    (zQueryAnn red (finalItems C r.2.1 r.2.2))
  return (r.1, finalItems C r.2.1 r.2.2, r.2.1.value.data.s, zs, r.2.2.signed)

/-- The transcript wins the half-aggregation game. -/
def winT (t : Transcript n X M) : Prop :=
  aggWins C challenge t.1 (t.2.1.map strip) t.2.2.1 t.2.2.2.1
    (fun m => t.2.2.2.2.contains m) = true

/-- The reduction's forgery from the transcript is a valid BIP340 forgery. -/
def extractOK [Inhabited M] (t : Transcript n X M) : Prop :=
  BIP340.verify C challenge t.1
      (extractForgery C challenge t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2).1
      (extractForgery C challenge t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2).2 = true ∧
    t.2.2.2.2.contains
      (extractForgery C challenge t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2).1 = false

/-! ## The bad event -/

/-- The randomizer `zᵢ` of the list `t` under the answer table `g`. -/
def zOf (g : List (AItem n X M) → ZMod n) (t : List (AItem n X M)) (i : ℕ) : ZMod n :=
  if i = 0 then 1 else g (t.take (i + 1))

/-- The key `t` is bad for the table `g`: its last coefficient `β*` is nonzero
but the randomized sum `Σ zᵢ⋅β*ᵢ` over `t` vanishes. -/
def badKey (t : List (AItem n X M)) (g : List (AItem n X M) → ZMod n) : Prop :=
  2 ≤ t.length ∧ ∃ b, t.getLast? = some b ∧ (starRep challenge b).2 ≠ 0 ∧
    isum (fun i a => zOf g t i * (starRep challenge a).2) 0 t = 0

/-- At most one answer at the key `t` makes it bad: the answer at `t` is the
randomizer of `t`'s last item only, and its coefficient is nonzero. -/
theorem badKey_value (t : List (AItem n X M)) (g : List (AItem n X M) → ZMod n) :
    ∃ c : ZMod n, ∀ u, badKey challenge t (Function.update g t u) → u = c := by
  by_cases h : 2 ≤ t.length ∧ ∃ b, t.getLast? = some b ∧ (starRep challenge b).2 ≠ 0
  · obtain ⟨hlen, b, hb, hβ⟩ := h
    have ht : t.dropLast ++ [b] = t := List.dropLast_append_getLast? b hb
    have hdl : t.dropLast.length = t.length - 1 := List.length_dropLast
    set S := isum (fun i a => zOf g t i * (starRep challenge a).2) 0 t.dropLast with hS
    refine ⟨-S / (starRep challenge b).2, ?_⟩
    rintro u ⟨-, b', -, -, hsum⟩
    have hsplit : isum (fun i a => zOf (Function.update g t u) t i * (starRep challenge a).2)
        0 t = S + u * (starRep challenge b).2 := by
      conv_lhs => arg 3; rw [← ht]
      rw [isum_append, isum_cons, isum_nil, add_zero, zero_add]
      congr 1
      · refine isum_congr fun i a _ _ hi => ?_
        unfold zOf
        split_ifs
        · rfl
        · rw [Function.update_of_ne]
          intro heq
          have := congrArg List.length heq
          simp only [List.length_take] at this
          omega
      · unfold zOf
        split_ifs with h0
        · omega
        · rw [List.take_of_length_le (by omega), Function.update_self]
    rw [hsplit] at hsum
    rw [eq_div_iff hβ]
    linear_combination hsum
  · exact ⟨0, fun u ⟨hlen, b, hb, hβ, _⟩ => (h ⟨hlen, b, hb, hβ⟩).elim⟩

/-- **Resampling the answer at a key makes it bad with probability at most `μ`**,
if `red` of a uniform hash output hits any given scalar with probability at
most `μ`. -/
theorem badKey_prob {μ : ℝ≥0∞} (hμ : RedBound red μ) (t : List (AItem n X M))
    (g : List (AItem n X M) → H) :
    Pr{let u ← $ᵗ H}[badKey challenge t (fun l => red (Function.update g t u l))] ≤ μ := by
  obtain ⟨c, hc⟩ := badKey_value challenge t (fun l => red (g l))
  refine (prEvent_mono_of_support _ _ _ fun u _ hu => hc (red u) ?_).trans (hμ c)
  have hupd : (fun l => red (Function.update g t u l)) =
      Function.update (fun l => red (g l)) t (red u) := by
    funext l
    by_cases hl : l = t
    · subst hl; simp
    · simp [Function.update_of_ne hl]
  rwa [hupd] at hu

end Halfagg.Security
