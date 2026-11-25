import Halfagg.Proofs.Annotated

/-!
# The forgery's items and the forger's phase

Facts about the items of a forgery (`toItems`, `annotate`, `finalItems_ok`) and
`phase1_ok`: after key generation and the forger's run in the annotated
experiment, the reduction's bookkeeping is valid.
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

/-! ## Items of a forgery -/

theorem pairs_mem : ∀ (pts : List E) (RP : E × E), RP ∈ pairs pts → RP.1 ∈ pts ∧ RP.2 ∈ pts
  | [], _, h => by simp [pairs] at h
  | [_], _, h => by simp [pairs] at h
  | R :: P :: rest, RP, h => by
      simp only [pairs, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · obtain ⟨h1, h2⟩ := pairs_mem rest RP h
        simp [h1, h2]

theorem toItems_mem {ms : List M} {pts : List E} {it : Item X M}
    (h : it ∈ toItems C ms pts) : ∃ R ∈ pts, ∃ P ∈ pts, it.1 = C.x R ∧ it.2.1 = C.x P := by
  simp only [toItems, List.mem_map] at h
  obtain ⟨⟨m, R, P⟩, hmem, rfl⟩ := h
  obtain ⟨h1, h2⟩ := pairs_mem _ _ (List.of_mem_zip hmem).2
  exact ⟨R, h1, P, h2, rfl, rfl⟩

theorem toItems_length_le (ms : List M) (pts : List E) :
    (toItems C ms pts : List (Item X M)).length ≤ ms.length := by
  simp only [toItems, List.length_map, List.length_zip]
  omega

theorem map_strip_annotate (memo : X → Option (Rep n)) (its : List (Item X M)) :
    (annotate C memo its).map strip = its := by
  induction its with
  | nil => rfl
  | cons it rest ih =>
    simp only [annotate]
    split_ifs
    · rw [List.map_cons, ih]; rfl
    · simp [strip, Function.comp_def]

theorem annotate_length (memo : X → Option (Rep n)) (its : List (Item X M)) :
    (annotate C memo its).length = its.length := by
  simpa using congrArg List.length (map_strip_annotate C memo its)

/-- On a list whose items all lift, every item gets its recorded representations. -/
theorem annotate_of_lifts (memo : X → Option (Rep n)) {its : List (Item X M)}
    (h : ∀ it ∈ its, lifts C it = true) :
    annotate C memo its =
      its.map fun it => ⟨it.1, it.2.1, it.2.2, (memo it.1).getD 0, (memo it.2.1).getD 0⟩ := by
  induction its with
  | nil => rfl
  | cons it rest ih =>
    simp only [annotate, h it List.mem_cons_self, ↓reduceIte, List.map_cons]
    rw [ih fun a ha => h a (List.mem_cons_of_mem _ ha)]

/-- Annotation commutes with taking a prefix. -/
theorem annotate_take (memo : X → Option (Rep n)) (its : List (Item X M)) (k : ℕ) :
    (annotate C memo its).take k = annotate C memo (its.take k) := by
  induction its generalizing k with
  | nil => simp [annotate]
  | cons it rest ih =>
    cases k with
    | zero => simp [annotate]
    | succ k =>
      simp only [List.take_succ_cons, annotate]
      split_ifs
      · rw [List.take_succ_cons, ih]
      · rw [← List.map_take, List.take_succ_cons]

theorem itemOK_annotate (d : ZMod n) {memo : X → Option (Rep n)} (hm : MemoOK C d memo)
    (its : List (Item X M)) (hl : ∀ it ∈ its, lifts C it = true)
    (hall : ∀ it ∈ its, (memo it.1).isSome ∧ (memo it.2.1).isSome) :
    ∀ a ∈ annotate C memo its, ItemOK C d a := by
  intro a ha
  rw [annotate_of_lifts C memo hl] at ha
  simp only [List.mem_map] at ha
  obtain ⟨it, hit, rfl⟩ := ha
  obtain ⟨h1, h2⟩ := hall it hit
  obtain ⟨ρ₁, hρ₁⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨ρ₂, hρ₂⟩ := Option.isSome_iff_exists.mp h2
  refine ⟨fun Q hQ => ?_, fun Q hQ => ?_⟩
  · simpa [hρ₁] using hm _ _ hρ₁ Q hQ
  · simpa [hρ₂] using hm _ _ hρ₂ Q hQ

/-- The final items of a run with valid bookkeeping have valid representations. -/
theorem finalItems_ok (hx0 : C.liftX (C.x 0) = none) (d : ZMod n) {recv : List E}
    {st : Core n X M} (hst : CoreOK C d recv st)
    {out : Explained (ZMod n) (Out n M) (Pts E)} (hout : out.Valid (fun _ => recv))
    (hl : ∀ it ∈ toItems C out.value.data.ms (out.value.groups ()), lifts C it = true) :
    ∀ a ∈ finalItems C out st, ItemOK C d a := by
  refine itemOK_annotate C d (memoOK_memoize C hx0 d hst.2 hst.1 (hout ())) _ hl fun it hit => ?_
  obtain ⟨R, hR, P, hP, h1, h2⟩ := toItems_mem C hit
  rw [h1, h2]
  exact ⟨memoizeList_isSome C _ _ _ _ hR, memoizeList_isSome C _ _ _ _ hP⟩

/-! ## The forger's phase -/

/-- After key generation and the forger's run, the bookkeeping is valid for the
normalized secret key `d`. -/
theorem phase1_ok [NonceGen n M] (hx0 : C.liftX (C.x 0) = none) (F : AlgForger n H E X M)
    (r : X × Explained (ZMod n) (Out n M) (Pts E) × Core n X M)
    (hr : r ∈ support (annPhase1 C challenge F)) :
    ∃ d : ZMod n, d ≠ 0 ∧ C.hasEvenY (C.mulG d) = true ∧ r.1 = C.x (C.mulG d) ∧
      r.2.1 ∈ support (F.main (initial C (C.mulG d))) ∧
      ∃ recv, CoreOK C d recv r.2.2 ∧ r.2.1.Valid (fun _ => recv) := by
  unfold annPhase1 at hr
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop] at hr
  obtain ⟨⟨pk, sk⟩, hks, r', hr', rfl⟩ := hr
  obtain ⟨hne, hpk⟩ := keygen_support (n := n) C challenge (pk, sk) hks
  simp only at hne hpk
  subst hpk
  have hP : (C.liftX (C.x (C.mulG sk))).getD 0 = C.mulG (C.evenScalar sk) := by
    rw [C.liftX_x_mulG hne]; rfl
  simp only [hP] at hr'
  refine ⟨C.evenScalar sk, C.evenScalar_ne_zero hne, C.hasEvenY_evenScalar hne,
    (C.x_evenScalar sk).symm, ?_, ?_⟩
  · refine support_simulateQ_run'_subset (annImpl (H := H) C challenge (C.x (C.mulG sk)) sk)
      (F.main (initial C (C.mulG (C.evenScalar sk)))) (Core.init : Core n X M) ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨r', hr', rfl⟩
  · exact core_inv C challenge hx0 (C.evenScalar sk) (C.x (C.mulG sk)) _ _ _
      (fun msg sig h => sign_support C challenge hne msg sig h) _ _
      (F.algebraic (initial C (C.mulG (C.evenScalar sk)))) Core.init
      (coreOK_init C (C.evenScalar sk)) r' hr'

end Halfagg.Security
