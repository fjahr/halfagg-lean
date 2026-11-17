import Halfagg.Proofs.Annotated

/-!
# A failed extraction leaves a bad key in the log

`ann_trace`: in a run of `annExperiment` against a fixed answer table `g`, if the
transcript wins but the reduction's extraction fails, then some key the verifier
queried is bad for `g`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security Halfagg.LoggedRun

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)

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

/-! ## Runs against a fixed table -/

theorem fixedTable_pure {α : Type} (x : α) (g : List (AItem n X M) → ZMod n)
    (c : (AnnSpec n X M).QueryCache) :
    fixedTableLoggedRun (pure x : OracleComp (unifSpec + AnnSpec n X M) α) g c =
      pure ((x, []), c) := by
  simp [fixedTableLoggedRun]

/-- One verifier query against the table returns `zOf` and logs its key. -/
theorem zq_fixed (items : List (AItem n X M)) (g : List (AItem n X M) → ZMod n) (i : ℕ)
    (c : (AnnSpec n X M).QueryCache) (hc : Agree c g) :
    ∀ p ∈ support (fixedTableLoggedRun (zQueryAnn items i) g c),
      p.1.1 = zOf g items i ∧ Agree p.2 g ∧
        (i ≠ 0 → items.take (i + 1) ∈ freshKeysOfLog p.1.2) := by
  intro p hp
  unfold zQueryAnn at hp
  unfold zOf
  split_ifs at hp ⊢ with hi
  · rw [fixedTable_pure] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨rfl, hc, fun h => absurd hi h⟩
  · rw [fixedTableLoggedRun_hashQuery, support_map] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    obtain ⟨h1, h2, -⟩ := fixedTable_hash _ g c hc r hr
    exact ⟨h1, h2, fun _ => by simp⟩

/-- The verifier's queries against the table return `zOf` and log their keys. -/
theorem zs_fixed (items : List (AItem n X M)) (g : List (AItem n X M) → ZMod n)
    (is : List ℕ) (c : (AnnSpec n X M).QueryCache) (hc : Agree c g) :
    ∀ w ∈ support (fixedTableLoggedRun (is.mapM (zQueryAnn items)) g c),
      w.1.1 = is.map (zOf g items) ∧ Agree w.2 g ∧
        ∀ i ∈ is, i ≠ 0 → items.take (i + 1) ∈ freshKeysOfLog w.1.2 := by
  induction is generalizing c with
  | nil =>
    intro w hw
    rw [List.mapM_nil, fixedTable_pure] at hw
    simp only [support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨rfl, hc, by simp⟩
  | cons i is ih =>
    intro w hw
    rw [List.mapM_cons, fixedTableLoggedRun_bind, mem_support_bind_iff] at hw
    obtain ⟨p, hp, hw⟩ := hw
    rw [support_map] at hw
    obtain ⟨q, hq, rfl⟩ := hw
    rw [fixedTableLoggedRun_bind, mem_support_bind_iff] at hq
    obtain ⟨p₂, hp₂, hq⟩ := hq
    rw [support_map] at hq
    obtain ⟨q₂, hq₂, rfl⟩ := hq
    rw [fixedTable_pure] at hq₂
    simp only [support_pure, Set.mem_singleton_iff] at hq₂
    subst hq₂
    obtain ⟨h1, h2, h3⟩ := zq_fixed items g i c hc p hp
    obtain ⟨k1, k2, k3⟩ := ih p.2 h2 p₂ hp₂
    refine ⟨by simp [h1, k1], k2, fun j hj hj0 => ?_⟩
    simp only [mem_freshKeysOfLog, List.append_nil, List.mem_append] at h3 k3 ⊢
    rcases List.mem_cons.mp hj with rfl | hj
    · obtain ⟨e, he, hk⟩ := h3 hj0
      exact ⟨e, Or.inl he, hk⟩
    · obtain ⟨e, he, hk⟩ := k3 j hj hj0
      exact ⟨e, Or.inr he, hk⟩

/-! ## The forger's phase -/

/-- After key generation and the forger's run, the bookkeeping is valid for the
normalized secret key `d`. -/
theorem phase1_ok (hx0 : C.liftX (C.x 0) = none) (F : AlgForger n E X M)
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
  · refine support_simulateQ_run'_subset (annImpl C challenge (C.x (C.mulG sk)) sk)
      (F.main (initial C (C.mulG (C.evenScalar sk)))) (Core.init : Core n X M) ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨r', hr', rfl⟩
  · exact core_inv C challenge hx0 (C.evenScalar sk) (C.x (C.mulG sk)) _ _ _
      (fun msg sig h => sign_support C challenge hne msg sig h) _ _
      (F.algebraic (initial C (C.mulG (C.evenScalar sk)))) Core.init
      (coreOK_init C (C.evenScalar sk)) r' hr'

/-! ## The trace -/

/-- **A failed extraction leaves a bad key in the log.** -/
theorem ann_trace [Inhabited M] (hx0 : C.liftX (C.x 0) = none) (F : AlgForger n E X M)
    (g : List (AItem n X M) → ZMod n)
    (z : (Transcript n X M × QueryLog (AnnSpec n X M)) × (AnnSpec n X M).QueryCache)
    (hz : z ∈ support (fixedTableLoggedRun (annExperiment C challenge F) g ∅))
    (hwin : winT C challenge z.1.1) (hno : ¬ extractOK C challenge z.1.1) :
    ∃ t ∈ freshKeysOfLog z.1.2, badKey challenge t g := by
  unfold annExperiment at hz
  rw [fixedTableLoggedRun_bind, mem_support_bind_iff] at hz
  obtain ⟨p, hp, hz⟩ := hz
  rw [support_map] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  rw [fixedTableLoggedRun_bind, mem_support_bind_iff] at hq
  obtain ⟨w, hw, hq⟩ := hq
  rw [support_map] at hq
  obtain ⟨q₂, hq₂, rfl⟩ := hq
  rw [fixedTable_pure] at hq₂
  simp only [support_pure, Set.mem_singleton_iff] at hq₂
  subst hq₂
  obtain ⟨hp1, hpag⟩ := fixedTable_support _ g ∅ (agree_empty g) p hp
  obtain ⟨d, hd, heven, hpk, -, recv, hcore, hval⟩ := phase1_ok C challenge hx0 F p.1.1 hp1
  set items := finalItems C p.1.1.2.1 p.1.1.2.2 with hitems
  obtain ⟨hzs, -, hkeys⟩ := zs_fixed items g (List.range items.length) p.2 hpag w hw
  simp only [winT, extractOK, hpk] at hwin hno
  have hl : ∀ it ∈ toItems C p.1.1.2.1.value.data.ms (p.1.1.2.1.value.groups ()),
      lifts C it = true := by
    have h := hwin
    simp only [aggWins, verifyWith, Bool.and_eq_true, List.all_eq_true] at h
    have h2 := h.1.1.2
    rw [items_map, hitems, finalItems, map_strip_annotate] at h2
    exact h2
  have hok := finalItems_ok C hx0 d hcore hval hl
  have hpos : 0 < items.length := by
    rcases hi : items with _ | ⟨a, l⟩
    · rw [hi] at hwin; simp [aggWins] at hwin
    · simp
  have hget : ∀ i < items.length, w.1.1.getD i 0 = zOf g items i := by
    intro i hi
    simp [hzs, List.getD_eq_getElem?_getD, hi]
  have hz0 : w.1.1.getD 0 0 = 1 := by rw [hget 0 hpos]; simp [zOf]
  rcases extract_or_bad C challenge d hd heven items _ _ _ hz0 hok hwin with
    hex | ⟨j, hj1, hjlen, hβ, hsum⟩
  · exact (hno hex).elim
  · refine ⟨items.take (j + 1), ?_, ?_⟩
    · have := hkeys j (List.mem_range.mpr hjlen) (by omega)
      simp only [mem_freshKeysOfLog, List.append_nil, List.mem_append] at this ⊢
      obtain ⟨e, he, hk⟩ := this
      exact ⟨e, Or.inr he, hk⟩
    · have hlen : (items.take (j + 1)).length = j + 1 := by
        rw [List.length_take]; omega
      refine ⟨by omega, items[j], ?_, hβ, ?_⟩
      · rw [List.getLast?_eq_getElem?, hlen]
        simp [hjlen]
      · rw [← hsum]
        refine isum_congr fun i a _ _ hi => ?_
        rw [hlen] at hi
        rw [hget i (by omega)]
        congr 1
        unfold zOf
        split_ifs
        · rfl
        · rw [List.take_take, min_eq_left (by omega)]

end Halfagg.Security
