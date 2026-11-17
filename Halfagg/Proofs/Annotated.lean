import Halfagg.Proofs.Scheme
import Halfagg.Proofs.LoggedRun

/-!
# The annotated experiment and its bad event

`annExperiment` runs the forger through the reduction's bookkeeping (`coreImpl`)
with real signatures and a random oracle on *annotated* lists, and returns the
transcript `(pk, items, s, zs, signed)`. Because a list's representations are
part of its oracle key, the bad event of Chen and Zhao's proof is a property of
a key and the oracle's answer table (`badKey`), and resampling the answer at
that key makes it hold with probability at most `1/n` (`badKey_prob`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security Halfagg.LoggedRun

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)

/-- `(pk, items, s, zs, signed)`. -/
abbrev Transcript (n : ℕ) (X M : Type) :=
  X × List (AItem n X M) × ZMod n × List (ZMod n) × List M

/-- The verifier's randomizer for annotated items. -/
def zQueryAnn (items : List (AItem n X M)) (i : ℕ) :
    OracleComp (unifSpec + AnnSpec n X M) (ZMod n) :=
  if i = 0 then pure 1
  else liftM ((unifSpec + AnnSpec n X M).query (.inr (items.take (i + 1))))

/-- The reduction's bookkeeping with real signatures under `sk` and the
annotated random oracle. -/
noncomputable def annImpl (pk : X) (sk : ZMod n) :
    QueryImpl (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n X M))
      (StateT (Core n X M) (OracleComp (unifSpec + AnnSpec n X M))) :=
  coreImpl C challenge pk
    (fun k => liftM ((unifSpec + AnnSpec n X M).query (.inl k)))
    (fun l => liftM ((unifSpec + AnnSpec n X M).query (.inr l)))
    (fun msg => (bip340 (M := M) C challenge
      (OracleComp (unifSpec + AnnSpec n X M))).sign pk sk msg)

/-- Key generation and the forger's run. -/
noncomputable def annPhase1 (F : AlgForger n E X M) :
    OracleComp (unifSpec + AnnSpec n X M)
      (X × Explained (ZMod n) (Out n M) (Pts E) × Core n X M) := do
  let ks ← (bip340 (M := M) C challenge (OracleComp (unifSpec + AnnSpec n X M))).keygen
  let r ← (simulateQ (annImpl C challenge ks.1 ks.2)
    (F.main (initial C ((C.liftX ks.1).getD 0)))).run Core.init
  return (ks.1, r.1, r.2)

/-- The forgery's annotated items, after recording its representations. -/
def finalItems (out : Explained (ZMod n) (Out n M) (Pts E)) (st : Core n X M) :
    List (AItem n X M) :=
  annotate C (memoize C st (out.value.groups ()) (out.coefficients ())).memo
    (toItems C out.value.data.ms (out.value.groups ()))

/-- The annotated experiment. -/
noncomputable def annExperiment (F : AlgForger n E X M) :
    OracleComp (unifSpec + AnnSpec n X M) (Transcript n X M) := do
  let r ← annPhase1 C challenge F
  let zs ← (List.range (finalItems C r.2.1 r.2.2).length).mapM
    (zQueryAnn (finalItems C r.2.1 r.2.2))
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

/-- **Resampling the answer at a key makes it bad with probability at most `1/n`**:
the answer at `t` is the randomizer of `t`'s last item only, and its coefficient
is nonzero, so exactly one answer makes the sum vanish. -/
theorem badKey_prob (t : List (AItem n X M)) (g : List (AItem n X M) → ZMod n) :
    Pr{let u ← $ᵗ (ZMod n)}[badKey challenge t (Function.update g t u)] ≤ (n : ℝ≥0∞)⁻¹ := by
  by_cases h : 2 ≤ t.length ∧ ∃ b, t.getLast? = some b ∧ (starRep challenge b).2 ≠ 0
  · obtain ⟨hlen, b, hb, hβ⟩ := h
    have ht : t.dropLast ++ [b] = t := List.dropLast_append_getLast? b hb
    have hdl : t.dropLast.length = t.length - 1 := List.length_dropLast
    set S := isum (fun i a => zOf g t i * (starRep challenge a).2) 0 t.dropLast with hS
    have key : ∀ u, badKey challenge t (Function.update g t u) →
        u = -S / (starRep challenge b).2 := by
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
    calc Pr{let u ← $ᵗ (ZMod n)}[badKey challenge t (Function.update g t u)]
        ≤ Pr{let u ← $ᵗ (ZMod n)}[u = -S / (starRep challenge b).2] :=
          prEvent_mono_of_support _ _ _ fun u _ => key u
      _ = (Fintype.card (ZMod n) : ℝ≥0∞)⁻¹ :=
          SampleableType.prEvent_uniformSample_eq_singleton _
      _ = (n : ℝ≥0∞)⁻¹ := by rw [ZMod.card]
  · rw [prEvent_eq_zero_of_forall_mem_support]
    · exact zero_le
    · rintro u - ⟨hlen, b, hb, hβ, -⟩
      exact h ⟨hlen, b, hb, hβ⟩

end Halfagg.Security
