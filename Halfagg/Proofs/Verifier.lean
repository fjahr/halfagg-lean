import Halfagg.Proofs.BridgeReduction

/-!
# The verifier's randomizers: a weighted sum hits a target with probability `1/n`

The verifier draws the randomizers `z₁, z₂, …` of the forgery's prefixes from the
lazily sampled oracle. For weights `w`, the sum `Σ zᵢ⋅wᵢ` over the drawn
randomizers hits a fixed target with probability at most `1/n` as soon as one
prefix with a nonzero weight is not yet in the oracle's cache (`seq_bound`). If
every prefix with a nonzero weight is cached, the sum is determined by the cache
(`seq_det`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open scoped ENNReal

namespace Halfagg.Security

variable {n : ℕ} [Fact n.Prime] {X M : Type} [DecidableEq X] [DecidableEq M]

/-- Two indexed sums agree if their summands agree at every position. -/
theorem isum_congr_idx {α β : Type*} [AddCommMonoid β] {f g : ℕ → α → β} {k : ℕ} {l : List α}
    (h : ∀ idx (hi : idx < l.length), f (k + idx) l[idx] = g (k + idx) l[idx]) :
    isum f k l = isum g k l := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    simp only [isum_cons]
    have h0 := h 0 (by simp)
    simp only [add_zero, List.getElem_cons_zero] at h0
    rw [h0]
    congr 1
    refine ih fun idx hi => ?_
    have := h (idx + 1) (by simp only [List.length_cons]; omega)
    simpa [Nat.add_assoc, Nat.add_comm 1 idx] using this

section Step

variable (items : List (AItem n X M)) {i : ℕ} (hi : i ≠ 0) (c : (AnnSpec n X M).QueryCache)

include hi in
theorem jZ_run_none (h : c (items.take (i + 1)) = none) :
    (jZ items i).run c = (do
      let u ← $ᵗ (ZMod n)
      pure (u, c.cacheQuery (items.take (i + 1)) u)) := by
  unfold jZ
  simp only [hi, ↓reduceIte]
  rw [randomOracle.run_eq, h]

include hi in
theorem jZ_run_some {u : ZMod n} (h : c (items.take (i + 1)) = some u) :
    (jZ items i).run c = pure (u, c) := by
  unfold jZ
  simp only [hi, ↓reduceIte]
  rw [randomOracle.run_eq, h]

include hi in
/-- One draw keeps every cached answer, changes the cache at most at its own
key, and returns the cached answer if there is one. -/
theorem jZ_support : ∀ p ∈ support ((jZ items i).run c),
    (∀ K u, c K = some u → p.2 K = some u) ∧
    (∀ K, K ≠ items.take (i + 1) → p.2 K = c K) ∧
    (∀ u, c (items.take (i + 1)) = some u → p.1 = u) := by
  intro p hp
  rcases h : c (items.take (i + 1)) with _ | u
  · rw [jZ_run_none items hi c h] at hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
    obtain ⟨u, -, rfl⟩ := hp
    refine ⟨fun K v hK => ?_, fun K hK => QueryCache.cacheQuery_of_ne _ _ hK,
      fun u hu => by cases hu⟩
    rw [QueryCache.cacheQuery_of_ne _ _ (fun hKe => by rw [hKe, h] at hK; cases hK)]
    exact hK
  · rw [jZ_run_some items hi c h] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨fun K v hK => hK, fun K _ => rfl, fun v hv => by rw [Option.some.injEq] at hv; exact hv⟩

end Step

/-- The cached answer at a key, or `0`. -/
def cval (c : (AnnSpec n X M).QueryCache) (K : List (AItem n X M)) : ZMod n :=
  match c K with
  | some u => u
  | none => 0

theorem cval_some {c : (AnnSpec n X M).QueryCache} {K : List (AItem n X M)} {u : ZMod n}
    (h : c K = some u) : cval c K = u := by
  simp [cval, h]

theorem cval_congr {c c' : (AnnSpec n X M).QueryCache} {K : List (AItem n X M)}
    (h : c' K = c K) : cval c' K = cval c K := by
  simp [cval, h]

section Seq

variable (items : List (AItem n X M)) (w : AItem n X M → ZMod n)

theorem take_ne {i j : ℕ} (hij : i ≠ j) (hi : i < items.length) (hj : j < items.length) :
    items.take (i + 1) ≠ items.take (j + 1) := by
  intro h
  have := congrArg List.length h
  simp only [List.length_take] at this
  omega

theorem mapM_range'_succ (k m : ℕ) (c : (AnnSpec n X M).QueryCache) :
    ((List.range' k (m + 1)).mapM (jZ items)).run c =
      ((jZ items k).run c >>= fun p =>
        ((List.range' (k + 1) m).mapM (jZ items)).run p.2 >>= fun q =>
          pure (p.1 :: q.1, q.2)) := by
  rw [List.range'_succ, List.mapM_cons]
  simp [StateT.run_bind]

/-- The sum over a list whose first randomizer is `z`. -/
theorem isum_cons_getD (z : ZMod n) (zs : List (ZMod n)) (k : ℕ) (b : AItem n X M)
    (rest : List (AItem n X M)) :
    isum (fun i a => (z :: zs).getD (i - k) 0 * w a) k (b :: rest) =
      z * w b + isum (fun i a => zs.getD (i - (k + 1)) 0 * w a) (k + 1) rest := by
  simp only [isum_cons, Nat.sub_self, List.getD_cons_zero]
  refine congrArg₂ (· + ·) rfl ?_
  refine isum_congr fun i a _ hi _ => ?_
  rw [show i - k = (i - (k + 1)) + 1 by omega, List.getD_cons_succ]

/-- If every prefix with a nonzero weight is cached, the drawn sum is the cached
sum. -/
theorem seq_det (its : List (AItem n X M)) (k : ℕ) (hk : 1 ≤ k)
    (hlen : k + its.length ≤ items.length) (c : (AnnSpec n X M).QueryCache)
    (hall : ∀ idx (h : idx < its.length),
      w its[idx] = 0 ∨ c (items.take (k + idx + 1)) ≠ none) :
    ∀ y ∈ support (((List.range' k its.length).mapM (jZ items)).run c),
      isum (fun i b => y.1.getD (i - k) 0 * w b) k its =
        isum (fun i b => cval c (items.take (i + 1)) * w b) k its := by
  induction its generalizing k c with
  | nil => intro y _; rfl
  | cons b rest ih =>
    intro y hy
    rw [List.length_cons, mapM_range'_succ, mem_support_bind_iff] at hy
    obtain ⟨p, hp, hy⟩ := hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨q, hq, hy⟩ := hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨hext, hother, hval⟩ := jZ_support items (by omega : k ≠ 0) c p hp
    simp only [List.length_cons] at hlen
    have hall' : ∀ idx (h : idx < rest.length),
        w rest[idx] = 0 ∨ p.2 (items.take (k + 1 + idx + 1)) ≠ none := by
      intro idx h
      rcases hall (idx + 1) (by simp only [List.length_cons]; omega) with h0 | hc
      · exact Or.inl (by simpa using h0)
      · right
        obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hc
        rw [show k + 1 + idx + 1 = k + (idx + 1) + 1 by omega, hext _ u hu]
        exact Option.some_ne_none u
    have hrec := ih (k + 1) (by omega) (by omega) p.2 hall' q hq
    rw [isum_cons_getD, hrec, isum_cons]
    refine congrArg₂ (· + ·) ?_ ?_
    · rcases hall 0 (by simp) with h0 | hc
      · simp only [List.getElem_cons_zero] at h0
        rw [h0, mul_zero, mul_zero]
      · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hc
        have hu' : c (items.take (k + 1)) = some u := hu
        rw [hval u hu', cval_some hu']
    · refine isum_congr_idx fun idx hi => ?_
      rcases hall (idx + 1) (by simp only [List.length_cons]; omega) with h0 | hc
      · have h0' : w rest[idx] = 0 := by simpa using h0
        rw [h0', mul_zero, mul_zero]
      · rw [cval_congr (hother _ (take_ne items (by omega) (by omega) (by omega)))]

/-- If some prefix with a nonzero weight is not cached, the drawn sum hits a
target with probability at most `1/n`. -/
theorem seq_bound (its : List (AItem n X M)) (k : ℕ) (hk : 1 ≤ k)
    (hlen : k + its.length ≤ items.length) (c : (AnnSpec n X M).QueryCache) (τ : ZMod n)
    (hex : ∃ idx, ∃ h : idx < its.length,
      w its[idx] ≠ 0 ∧ c (items.take (k + idx + 1)) = none) :
    Pr{let y ← ((List.range' k its.length).mapM (jZ items)).run c}[
      isum (fun i b => y.1.getD (i - k) 0 * w b) k its = τ] ≤ (n : ℝ≥0∞)⁻¹ := by
  induction its generalizing k c τ with
  | nil => obtain ⟨idx, h, -⟩ := hex; simp at h
  | cons b rest ih =>
    simp only [List.length_cons] at hlen
    rw [List.length_cons, mapM_range'_succ]
    have hk0 : k ≠ 0 := by omega
    by_cases hA : ∃ idx, ∃ h : idx < rest.length,
        w rest[idx] ≠ 0 ∧ c (items.take (k + 1 + idx + 1)) = none
    · -- a later prefix is still fresh after the first draw
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp => ?_
      obtain ⟨-, hother, -⟩ := jZ_support items hk0 c p hp
      rw [bind_pure_comp, prEvent_map]
      have hiff : ∀ q : List (ZMod n) × (AnnSpec n X M).QueryCache,
          isum (fun i a => (p.1 :: q.1).getD (i - k) 0 * w a) k (b :: rest) = τ ↔
            isum (fun i a => q.1.getD (i - (k + 1)) 0 * w a) (k + 1) rest = τ - p.1 * w b := by
        intro q
        rw [isum_cons_getD, eq_sub_iff_add_eq']
      refine (prEvent_congr_of_support _ _ _ fun q _ => hiff q).le.trans ?_
      refine ih (k + 1) (by omega) (by omega) p.2 _ ?_
      obtain ⟨idx, h, hw, hc⟩ := hA
      refine ⟨idx, h, hw, ?_⟩
      rw [hother _ (take_ne items (by omega) (by omega) (by omega))]
      exact hc
    · -- the first prefix is the last fresh one with a nonzero weight
      obtain ⟨idx, h, hw, hc⟩ := hex
      have h0 : idx = 0 := by
        by_contra hne
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
        have hj : j < rest.length := by simpa using h
        refine hA ⟨j, hj, by simpa using hw, ?_⟩
        rwa [show k + 1 + j + 1 = k + (j + 1) + 1 by omega]
      subst h0
      have hw' : w b ≠ 0 := by simpa using hw
      have hc' : c (items.take (k + 1)) = none := hc
      have hall : ∀ u idx (h : idx < rest.length), w rest[idx] = 0 ∨
          (c.cacheQuery (items.take (k + 1)) u) (items.take (k + 1 + idx + 1)) ≠ none := by
        intro u idx h
        by_cases hwi : w rest[idx] = 0
        · exact Or.inl hwi
        · right
          rw [QueryCache.cacheQuery_of_ne _ _ (take_ne items (by omega) (by omega) (by omega))]
          exact fun hcn => hA ⟨idx, h, hwi, hcn⟩
      rw [jZ_run_none items hk0 c hc', bind_assoc]
      simp only [pure_bind]
      refine (prEvent_bind_le_prEvent_mul_of_forall_le _ _
        (fun u => u = (τ - isum (fun i a => cval c (items.take (i + 1)) * w a) (k + 1) rest) / w b)
        _ (ε := 1) (fun u _ => prEvent_le_one _) (fun u hu => ?_)).trans ?_
      · refine prEvent_eq_zero_of_forall_mem_support _ _ fun y hy hsum => hu ?_
        rw [mem_support_bind_iff] at hy
        obtain ⟨q, hq, hy⟩ := hy
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        have hdet := seq_det items w rest (k + 1) (by omega) (by omega) _ (hall u) q hq
        have hS : isum (fun i a => cval (c.cacheQuery (items.take (k + 1)) u)
            (items.take (i + 1)) * w a) (k + 1) rest =
            isum (fun i a => cval c (items.take (i + 1)) * w a) (k + 1) rest := by
          refine isum_congr_idx fun idx hi => ?_
          rw [cval_congr (QueryCache.cacheQuery_of_ne _ _
            (take_ne items (by omega) (by omega) (by omega)))]
        rw [isum_cons_getD, hdet, hS] at hsum
        rw [eq_div_iff hw']
        linear_combination hsum
      · rw [mul_one, SampleableType.prEvent_uniformSample_eq_singleton, ZMod.card]

theorem cval_eq (c : (AnnSpec n X M).QueryCache) (K : List (AItem n X M)) :
    cval c K = (c K : Option (ZMod n)).getD 0 := by
  unfold cval
  rcases c K with _ | u <;> rfl

/-- **A completed bad configuration.** Some weight is nonzero, every prefix with
a nonzero weight has an answer in `v`, and the weighted sum of these answers
(with `z₀ = 1`) vanishes. -/
def Dcfg (v : List (AItem n X M) → Option (ZMod n)) : Prop :=
  (∃ b ∈ items, w b ≠ 0) ∧
  (∀ idx (h : idx < items.length), 1 ≤ idx → w items[idx] ≠ 0 →
    v (items.take (idx + 1)) ≠ none) ∧
  isum (fun i b => (if i = 0 then 1 else (v (items.take (i + 1))).getD 0) * w b) 0 items = 0

/-- **The verifier's draws.** Unless the cache already holds a completed bad
configuration, the weighted sum of the verifier's randomizers vanishes with
probability at most `1/n`. -/
theorem verifier_bound (c : (AnnSpec n X M).QueryCache)
    (hD : ¬ Dcfg items w (fun K => c K)) :
    Pr{let q ← ((List.range items.length).mapM (jZ items)).run c}[
      (∃ b ∈ items, w b ≠ 0) ∧ isum (fun i b => q.1.getD i 0 * w b) 0 items = 0] ≤
      (n : ℝ≥0∞)⁻¹ := by
  by_cases hne : ∃ b ∈ items, w b ≠ 0
  swap
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun q _ h => hne h.1]
    exact zero_le
  rcases hitems : items with _ | ⟨b0, its⟩
  · rw [hitems] at hne
    obtain ⟨b, hb, -⟩ := hne
    cases hb
  have hrun : ((List.range (b0 :: its).length).mapM (jZ (b0 :: its))).run c =
      (((List.range' 1 its.length).mapM (jZ (b0 :: its))).run c >>= fun q =>
        pure (1 :: q.1, q.2)) := by
    rw [List.length_cons, List.range_eq_range', List.range'_succ, List.mapM_cons]
    simp [jZ]
  have hsum : ∀ zs : List (ZMod n),
      isum (fun i b => (1 :: zs).getD i 0 * w b) 0 (b0 :: its) =
        w b0 + isum (fun i a => zs.getD (i - 1) 0 * w a) 1 its := by
    intro zs
    have h := isum_cons_getD w 1 zs 0 b0 its
    simpa using h
  rw [hrun, bind_pure_comp, prEvent_map]
  by_cases hunc : ∃ idx, ∃ h : idx < its.length,
      w its[idx] ≠ 0 ∧ c ((b0 :: its).take (1 + idx + 1)) = none
  · refine (prEvent_mono_of_support _ _
      (fun q => isum (fun i a => q.1.getD (i - 1) 0 * w a) 1 its = -w b0) fun q _ hq => ?_).trans
      (seq_bound (b0 :: its) w its 1 le_rfl (by simp only [List.length_cons]; omega) c _ hunc)
    have h := hq.2
    rw [hsum] at h
    linear_combination h
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun q hq h => ?_]
    · exact zero_le
    have hall : ∀ idx (h : idx < its.length),
        w its[idx] = 0 ∨ c ((b0 :: its).take (1 + idx + 1)) ≠ none := by
      intro idx h
      by_cases hwi : w its[idx] = 0
      · exact Or.inl hwi
      · exact Or.inr fun hcn => hunc ⟨idx, h, hwi, hcn⟩
    have hdet := seq_det (b0 :: its) w its 1 le_rfl (by simp only [List.length_cons]; omega) c
      hall q hq
    have h2 := h.2
    rw [hsum, hdet] at h2
    refine hD ?_
    rw [hitems]
    refine ⟨hitems ▸ hne, fun idx hidx h1 hwi => ?_, ?_⟩
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : idx ≠ 0)
      have hj : j < its.length := by simpa using hidx
      rcases hall j hj with h0 | hc
      · exact absurd (by simpa using h0) hwi
      · rwa [show j + 1 + 1 = 1 + j + 1 by omega]
    · refine Eq.trans ?_ h2
      rw [isum_cons]
      simp only [↓reduceIte, one_mul]
      refine congrArg₂ (· + ·) rfl (isum_congr fun i a _ hi _ => ?_)
      have hi0 : i ≠ 0 := by omega
      simp only [hi0, ↓reduceIte, cval_eq]

end Seq

end Halfagg.Security
