import Halfagg.SecurityBinding
import Halfagg.Proofs.Explained

/-!
# Binding: two lists with the same randomized sum

The randomizer side of `halfagg_binding`, for a fixed challenge hash.

`VerifyAggregate` accepts an aggregate for two lists only if their randomized
sums `Σ zᵢ⋅(Rᵢ + eᵢ⋅Pᵢ)` are equal. `pair_term`: for a game with at most `Q`
randomizer-hash queries, that happens with probability at most `Q²⋅μ`, unless
the challenge hash is degenerate on the output (`badC`).

* `Ssum` is the sum of a list with the randomizers read off the oracle's cache,
  and `Ssum_update_prefix` says how a fresh answer changes it.
* `logImpl` is the lazily sampled oracle that also records its fresh keys, so
  that two recorded lists can be named by their positions.
* `log_step`: a pair of recorded lists gets its last separating randomizer at
  one step, and that answer makes the sums equal with probability at most `μ`.
  `pair_potential` turns this into a bound for a whole run.
* `win_pair`: a winning run has such a pair among its first `Q` records.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Halfagg.LoggedRun

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)
variable [SampleableType H] (red : H → ZMod n)

/-! ## Scalars on a point of prime order -/

/-- On a nonzero point, scalar multiplication is injective if every point has
order dividing the prime `n`. -/
theorem smul_val_inj (hord : PrimeOrder n E) {P : E} (hP : P ≠ 0) {a b : ZMod n}
    (h : a.val • P = b.val • P) : a = b := by
  have ho : addOrderOf P = n := addOrderOf_eq_prime (hord P) hP
  have hmod := nsmul_eq_nsmul_iff_modEq.mp h
  rw [ho] at hmod
  exact ZMod.val_injective n (Nat.ModEq.eq_of_lt_of_lt hmod (ZMod.val_lt a) (ZMod.val_lt b))

/-- A fresh hash output puts `A + red v ⋅ T` on a target with probability at
most `μ`, for a nonzero `T`. -/
theorem fresh_hit_prob {μ : ℝ≥0∞} (hμ : RedBound red μ) (hord : PrimeOrder n E) {T : E}
    (hT : T ≠ 0) (A B : E) : Pr{let v ← $ᵗ H}[A + (red v).val • T = B] ≤ μ := by
  by_cases h : ∃ x : ZMod n, A + x.val • T = B
  · obtain ⟨x, hx⟩ := h
    refine (prEvent_mono_of_support _ _ _ fun v _ hv => ?_).trans (hμ x)
    exact smul_val_inj hord hT (add_left_cancel (hv.trans hx.symm))
  · rw [prEvent_eq_zero_of_forall_mem_support]
    · exact zero_le
    · exact fun v _ hv => h ⟨red v, hv⟩

/-! ## The randomized sum of a list, from the oracle's cache -/

section Sum

variable (tm : Item X M → E)

/-- The randomizer of the last item of `L`: `1` for a list of at most one item,
otherwise the cached hash of `L` as a scalar, and `0` if `L` is not cached. -/
def zL (c : (RandSpec H X M).QueryCache) (L : List (Item X M)) : ZMod n :=
  if L.length ≤ 1 then 1 else ((c L).map red).getD 0

/-- `Σ zᵢ⋅tm(itemᵢ)` with the randomizers from the cache. -/
def Ssum (c : (RandSpec H X M).QueryCache) (L : List (Item X M)) : E :=
  isum (fun i it => (zL red c (L.take (i + 1))).val • tm it) 0 L

theorem Ssum_append (c : (RandSpec H X M).QueryCache) (L : List (Item X M)) (a : Item X M) :
    Ssum red tm c (L ++ [a]) = Ssum red tm c L + (zL red c (L ++ [a])).val • tm a := by
  unfold Ssum
  rw [isum_append, isum_cons, isum_nil, add_zero, zero_add]
  congr 1
  · refine isum_congr fun i it _ _ hi => ?_
    rw [List.take_append_of_le_length (by omega)]
  · rw [List.take_of_length_le (by simp)]

theorem zL_update_ne {c : (RandSpec H X M).QueryCache} {K L : List (Item X M)} (v : H)
    (h : L ≠ K) : zL red (c.cacheQuery K v) L = zL red c L := by
  unfold zL
  rw [QueryCache.cacheQuery_of_ne _ _ h]

theorem zL_update_short {c : (RandSpec H X M).QueryCache} {K : List (Item X M)} (v : H)
    (hK : K.length ≤ 1) (L : List (Item X M)) : zL red (c.cacheQuery K v) L = zL red c L := by
  by_cases h : L = K
  · subst h
    simp [zL, hK]
  · exact zL_update_ne red v h

/-- An answer at a key of at most one item changes no sum. -/
theorem Ssum_update_short {c : (RandSpec H X M).QueryCache} {K : List (Item X M)} (v : H)
    (hK : K.length ≤ 1) (L : List (Item X M)) :
    Ssum red tm (c.cacheQuery K v) L = Ssum red tm c L := by
  unfold Ssum
  exact isum_congr fun i it _ _ _ => by rw [zL_update_short red v hK]

/-- An answer at a key that is not a prefix of `L` does not change the sum of `L`. -/
theorem Ssum_update_not_prefix {c : (RandSpec H X M).QueryCache} {K : List (Item X M)} (v : H)
    (L : List (Item X M)) (hK : ¬ K <+: L) :
    Ssum red tm (c.cacheQuery K v) L = Ssum red tm c L := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L a ih =>
    rw [Ssum_append, Ssum_append, ih fun h => hK (h.trans (List.prefix_append L [a])),
      zL_update_ne red v fun h => hK (by subst h; exact List.prefix_refl _)]

/-- A fresh answer `v` at a prefix `K` of `L` with at least two items adds
`red v` times the term of `K`'s last item to the sum of `L`. -/
theorem Ssum_update_prefix {c : (RandSpec H X M).QueryCache} {K : List (Item X M)} (v : H)
    (hc : c K = none) (hK2 : 2 ≤ K.length) {a₀ : Item X M} (hlast : K.getLast? = some a₀)
    (L : List (Item X M)) (hK : K <+: L) :
    Ssum red tm (c.cacheQuery K v) L = Ssum red tm c L + (red v).val • tm a₀ := by
  induction L using List.reverseRecOn with
  | nil =>
    have := List.prefix_nil.mp hK
    subst this
    simp at hK2
  | append_singleton L a ih =>
    rw [Ssum_append, Ssum_append]
    rcases List.prefix_concat_iff.mp hK with hEq | hpre
    · subst hEq
      have hnp : ¬ (L ++ [a]) <+: L := fun h => by
        have := h.length_le
        simp at this
      rw [Ssum_update_not_prefix red tm v L hnp]
      have h1 : zL red (c.cacheQuery (L ++ [a]) v) (L ++ [a]) = red v := by
        have hlen : ¬ (L ++ [a]).length ≤ 1 := by omega
        simp only [zL, hlen, ↓reduceIte, QueryCache.cacheQuery_self, Option.map_some,
          Option.getD_some]
      have h0 : zL red c (L ++ [a]) = 0 := by
        have hlen : ¬ (L ++ [a]).length ≤ 1 := by omega
        simp only [zL, hlen, ↓reduceIte, hc, Option.map_none, Option.getD_none]
      have ha : a₀ = a := by simpa using hlast.symm
      rw [h1, h0, ha, ZMod.val_zero, zero_nsmul, add_zero]
    · have hne : L ++ [a] ≠ K := fun h => by
        have := hpre.length_le
        rw [← h] at this
        simp at this
      rw [ih hpre, zL_update_ne red v hne]
      abel

end Sum

/-! ## A lazily sampled oracle that records its fresh keys -/

/-- The oracle's cache and the keys it has sampled, in order. -/
abbrev LState (H X M : Type) := (RandSpec H X M).QueryCache × List (List (Item X M))

/-- The lazily sampled randomizer hash, recording each fresh key. -/
noncomputable def logImpl : QueryImpl (unifSpec + RandSpec H X M) (StateT (LState H X M) ProbComp)
  | .inl k => fun σ => (fun u => (u, σ)) <$> (liftM (unifSpec.query k) : ProbComp _)
  | .inr K => fun σ =>
      match σ.1 K with
      | some v => pure (v, σ)
      | none => do
          let v ← $ᵗ H
          pure (v, (σ.1.cacheQuery K v, σ.2 ++ [K]))

theorem logImpl_unif (k : ℕ) (σ : LState H X M) :
    (logImpl (.inl k)).run σ = (fun u => (u, σ)) <$> (liftM (unifSpec.query k) : ProbComp _) :=
  rfl

theorem logImpl_hit {K : List (Item X M)} {σ : LState H X M} {v : H} (h : σ.1 K = some v) :
    (logImpl (.inr K)).run σ = pure (v, σ) := by
  change (match σ.1 K with
    | some v => pure (v, σ)
    | none => ($ᵗ H) >>= fun v => pure (v, (σ.1.cacheQuery K v, σ.2 ++ [K]))) = _
  rw [h]

theorem logImpl_miss {K : List (Item X M)} {σ : LState H X M} (h : σ.1 K = none) :
    (logImpl (.inr K)).run σ =
      (($ᵗ H) >>= fun v => pure (v, (σ.1.cacheQuery K v, σ.2 ++ [K]))) := by
  change (match σ.1 K with
    | some v => pure (v, σ)
    | none => ($ᵗ H) >>= fun v => pure (v, (σ.1.cacheQuery K v, σ.2 ++ [K]))) = _
  rw [h]

/-- Without its record, the recording oracle is the lazily sampled oracle. -/
theorem log_project {α : Type} (oa : OracleComp (unifSpec + RandSpec H X M) α)
    (σ : LState H X M) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ logImpl oa).run σ =
      (simulateQ (RandSpec H X M).romImpl oa).run σ.1 := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure a => simp
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases t with k | K
    · have h2 : ((RandSpec H X M).romImpl (.inl k)).run σ.1 =
          (fun u => (u, σ.1)) <$> (liftM (unifSpec.query k) : ProbComp _) :=
        roSim.run_apply_inl (hashSpec := RandSpec H X M) (RandSpec H X M).randomOracle k σ.1
      rw [logImpl_unif, h2, bind_map_left, bind_map_left]
      exact bind_congr fun u => ih u σ
    · have h2 : ((RandSpec H X M).romImpl (.inr K)).run σ.1 =
          ((RandSpec H X M).randomOracle K).run σ.1 := rfl
      rw [h2, randomOracle.run_eq]
      rcases hc : σ.1 K with _ | v
      · rw [logImpl_miss hc]
        simp only [bind_assoc, pure_bind]
        exact bind_congr fun v => ih v _
      · rw [logImpl_hit hc]
        simp only [pure_bind]
        exact ih v σ

/-! ## An event that a pair of states can trigger once -/

/-- If an invariant can break only at the one step that makes a state `done`,
and then with probability at most `μ`, it breaks with probability at most `μ`
in a whole run. -/
theorem pair_potential {ι : Type} {spec : OracleSpec ι} {σT α : Type}
    (impl : QueryImpl spec (StateT σT ProbComp)) (Inv done : σT → Prop) (μ : ℝ≥0∞)
    (hstep : ∀ t s, Inv s →
      (done s → ∀ y ∈ support ((impl t).run s), done y.2 ∧ Inv y.2) ∧
      (¬ done s → (∀ y ∈ support ((impl t).run s), Inv y.2) ∨
        ((∀ y ∈ support ((impl t).run s), done y.2) ∧
          Pr{let y ← (impl t).run s}[¬ Inv y.2] ≤ μ)))
    (oa : OracleComp spec α) (s : σT) (hs : Inv s) :
    Pr{let z ← (simulateQ impl oa).run s}[¬ Inv z.2] ≤ μ := by
  classical
  suffices h : ∀ (oa : OracleComp spec α) (s : σT), Inv s →
      (done s → Pr{let z ← (simulateQ impl oa).run s}[¬ Inv z.2] ≤ 0) ∧
        Pr{let z ← (simulateQ impl oa).run s}[¬ Inv z.2] ≤ μ from (h oa s hs).2
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s hs
    have h0 : Pr{let z ← (simulateQ impl (pure a : OracleComp spec α)).run s}[¬ Inv z.2] = 0 := by
      refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => not_not.mpr ?_
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs
    exact ⟨fun _ => h0.le, h0.le.trans zero_le⟩
  | query_bind t next ih =>
    intro s hs
    obtain ⟨hd, hnd⟩ := hstep t s hs
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hdone : done s → Pr{let z ← (impl t).run s >>= fun y =>
        (simulateQ impl (next y.1)).run y.2}[¬ Inv z.2] ≤ 0 := fun h =>
      prEvent_bind_le_of_forall _ _ _ _ fun y hy =>
        (ih y.1 y.2 (hd h y hy).2).1 (hd h y hy).1
    refine ⟨hdone, ?_⟩
    by_cases h : done s
    · exact (hdone h).trans zero_le
    · rcases hnd h with hA | ⟨hB1, hB2⟩
      · exact prEvent_bind_le_of_forall _ _ _ _ fun y hy => (ih y.1 y.2 (hA y hy)).2
      · refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun y => ¬ Inv y.2) _ (ε := 0)
          fun y hy hI => (ih y.1 y.2 (not_not.mp hI)).1 (hB1 y hy)).trans ?_
        rw [add_zero]
        exact hB2

/-! ## A pair of recorded lists -/

section Pair

variable (tm : Item X M → E)

/-- A pair of lists the adversary could win with: different, of the same length
of at least two, and with nonzero terms. -/
def Cond (L L' : List (Item X M)) : Prop :=
  L ≠ L' ∧ L.length = L'.length ∧ 2 ≤ L.length ∧ (∀ it ∈ L, tm it ≠ 0) ∧ ∀ it ∈ L', tm it ≠ 0

/-- `K` is a prefix of at least two items of exactly one of the two lists, so
its hash is a randomizer of exactly one of them. -/
def Sep (K L L' : List (Item X M)) : Prop :=
  2 ≤ K.length ∧ ((K <+: L ∧ ¬ K <+: L') ∨ (K <+: L' ∧ ¬ K <+: L))

/-- Every key that separates the pair is cached. -/
def Complete (c : (RandSpec H X M).QueryCache) (L L' : List (Item X M)) : Prop :=
  ∀ K, Sep K L L' → c K ≠ none

/-- The lists recorded at positions `a` and `b` form a pair with every
separating key cached. -/
def doneP (a b : ℕ) (σ : LState H X M) : Prop :=
  ∃ L L', σ.2[a]? = some L ∧ σ.2[b]? = some L' ∧ Cond tm L L' ∧ Complete σ.1 L L'

/-- Such a pair at positions `a` and `b` has different randomized sums. -/
def InvP (a b : ℕ) (σ : LState H X M) : Prop :=
  ∀ L L', σ.2[a]? = some L → σ.2[b]? = some L' → Cond tm L L' → Complete σ.1 L L' →
    Ssum red tm σ.1 L ≠ Ssum red tm σ.1 L'

/-- **One oracle step and one pair of positions.** A pair that is complete stays
complete with different sums. A pair becomes complete only by a fresh answer at
a separating key, and then its sums are equal with probability at most `μ`. -/
theorem log_step {μ : ℝ≥0∞} (hμ : RedBound red μ) (hord : PrimeOrder n E) (a b : ℕ)
    (t : (unifSpec + RandSpec H X M).Domain) (σ : LState H X M) (hI : InvP red tm a b σ) :
    (doneP tm a b σ → ∀ y ∈ support ((logImpl t).run σ),
        doneP tm a b y.2 ∧ InvP red tm a b y.2) ∧
    (¬ doneP tm a b σ → (∀ y ∈ support ((logImpl t).run σ), InvP red tm a b y.2) ∨
      ((∀ y ∈ support ((logImpl t).run σ), doneP tm a b y.2) ∧
        Pr{let y ← (logImpl t).run σ}[¬ InvP red tm a b y.2] ≤ μ)) := by
  have hunch : (∀ y ∈ support ((logImpl t).run σ), y.2 = σ) →
      (doneP tm a b σ → ∀ y ∈ support ((logImpl t).run σ),
          doneP tm a b y.2 ∧ InvP red tm a b y.2) ∧
      (¬ doneP tm a b σ → (∀ y ∈ support ((logImpl t).run σ), InvP red tm a b y.2) ∨
        ((∀ y ∈ support ((logImpl t).run σ), doneP tm a b y.2) ∧
          Pr{let y ← (logImpl t).run σ}[¬ InvP red tm a b y.2] ≤ μ)) := fun h =>
    ⟨fun hd y hy => by rw [h y hy]; exact ⟨hd, hI⟩,
      fun _ => Or.inl fun y hy => by rw [h y hy]; exact hI⟩
  rcases t with k | K
  · refine hunch fun y hy => ?_
    rw [logImpl_unif, support_map] at hy
    obtain ⟨u, -, rfl⟩ := hy
    rfl
  obtain ⟨c, l⟩ := σ
  rcases hc : c K with _ | v0
  swap
  · refine hunch fun y hy => ?_
    rw [logImpl_hit (σ := (c, l)) hc] at hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    rfl
  rw [logImpl_miss (σ := (c, l)) hc]
  have hsupp : ∀ y ∈ support (($ᵗ H) >>= fun v =>
      (pure (v, (c.cacheQuery K v, l ++ [K])) : ProbComp (H × LState H X M))),
      ∃ v, y = (v, (c.cacheQuery K v, l ++ [K])) := by
    intro y hy
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
    obtain ⟨v, -, rfl⟩ := hy
    exact ⟨v, rfl⟩
  have hmono : ∀ (v : H) K₀, c K₀ ≠ none → (c.cacheQuery K v) K₀ ≠ none := by
    intro v K₀ h
    by_cases hk : K₀ = K
    · subst hk
      exact absurd hc h
    · rwa [QueryCache.cacheQuery_of_ne _ _ hk]
  have hcomp : ∀ (v : H) L L', Complete (c.cacheQuery K v) L L' ↔
      ∀ K₀, Sep K₀ L L' → c K₀ ≠ none ∨ K₀ = K := by
    intro v L L'
    constructor
    · intro h K₀ hs
      by_cases hk : K₀ = K
      · exact Or.inr hk
      · left
        have := h K₀ hs
        rwa [QueryCache.cacheQuery_of_ne _ _ hk] at this
    · intro h K₀ hs
      rcases h K₀ hs with h1 | rfl
      · exact hmono v K₀ h1
      · simp
  have hget : ∀ {i : ℕ} {L : List (Item X M)}, l[i]? = some L → (l ++ [K])[i]? = some L := by
    intro i L h
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
    exact h
  have hsumeq : ∀ (v : H) L L', ¬ Sep K L L' →
      (Ssum red tm (c.cacheQuery K v) L = Ssum red tm (c.cacheQuery K v) L' ↔
        Ssum red tm c L = Ssum red tm c L') := by
    intro v L L' hns
    by_cases hK2 : 2 ≤ K.length
    · have hiff : K <+: L ↔ K <+: L' := by
        constructor
        · intro h
          by_contra h'
          exact hns ⟨hK2, Or.inl ⟨h, h'⟩⟩
        · intro h
          by_contra h'
          exact hns ⟨hK2, Or.inr ⟨h, h'⟩⟩
      by_cases hp : K <+: L
      · rcases hl : K.getLast? with _ | a₀
        · rw [List.getLast?_eq_none_iff] at hl
          subst hl
          simp at hK2
        · rw [Ssum_update_prefix red tm v hc hK2 hl L hp,
            Ssum_update_prefix red tm v hc hK2 hl L' (hiff.mp hp), add_left_inj]
      · rw [Ssum_update_not_prefix red tm v L hp,
          Ssum_update_not_prefix red tm v L' fun h => hp (hiff.mpr h)]
    · rw [Ssum_update_short red tm v (by omega), Ssum_update_short red tm v (by omega)]
  refine ⟨fun hd y hy => ?_, fun hnd => ?_⟩
  · obtain ⟨v, rfl⟩ := hsupp y hy
    obtain ⟨L, L', ha, hb, hC, hComp⟩ := hd
    have hns : ¬ Sep K L L' := fun hs => hComp K hs hc
    refine ⟨⟨L, L', hget ha, hget hb, hC, fun K₀ hs => hmono v K₀ (hComp K₀ hs)⟩, ?_⟩
    intro L₂ L₂' ha₂ hb₂ _ _
    have e1 : L₂ = L := by
      have h := hget ha
      change (l ++ [K])[a]? = some L₂ at ha₂
      rw [h] at ha₂
      exact (Option.some.inj ha₂).symm
    have e2 : L₂' = L' := by
      have h := hget hb
      change (l ++ [K])[b]? = some L₂' at hb₂
      rw [h] at hb₂
      exact (Option.some.inj hb₂).symm
    subst e1 e2
    exact fun heq => hI L₂ L₂' ha hb hC hComp ((hsumeq v L₂ L₂' hns).mp heq)
  · by_cases hex : ∃ L L', (l ++ [K])[a]? = some L ∧ (l ++ [K])[b]? = some L' ∧ Cond tm L L' ∧
        ∀ K₀, Sep K₀ L L' → c K₀ ≠ none ∨ K₀ = K
    swap
    · left
      intro y hy
      obtain ⟨v, rfl⟩ := hsupp y hy
      intro L L' ha hb hC hComp
      exact absurd ⟨L, L', ha, hb, hC, (hcomp v L L').mp hComp⟩ hex
    right
    obtain ⟨L, L', ha, hb, hC, hCK⟩ := hex
    refine ⟨fun y hy => ?_, ?_⟩
    · obtain ⟨v, rfl⟩ := hsupp y hy
      exact ⟨L, L', ha, hb, hC, (hcomp v L L').mpr hCK⟩
    have hpos : ∀ {i : ℕ} {L₀ : List (Item X M)}, (l ++ [K])[i]? = some L₀ →
        l[i]? = some L₀ ∨ L₀ = K := by
      intro i L₀ h
      rcases Nat.lt_or_ge i l.length with hi | hi
      · left
        rwa [List.getElem?_append_left hi] at h
      · right
        rw [List.getElem?_append_right hi] at h
        rcases hidx : i - l.length with _ | m
        · rw [hidx] at h
          simpa using h.symm
        · rw [hidx] at h
          simp at h
    have hsep : Sep K L L' := by
      by_contra hns
      have hComp : Complete c L L' := fun K₀ hs =>
        (hCK K₀ hs).resolve_right fun h => hns (h ▸ hs)
      have ha' : l[a]? = some L := by
        rcases hpos ha with h | h
        · exact h
        · subst h
          exact absurd ⟨hC.2.2.1, Or.inl ⟨List.prefix_refl _,
            fun hp => hC.1 (hp.eq_of_length hC.2.1)⟩⟩ hns
      have hb' : l[b]? = some L' := by
        rcases hpos hb with h | h
        · exact h
        · subst h
          exact absurd ⟨hC.2.1 ▸ hC.2.2.1, Or.inr ⟨List.prefix_refl _,
            fun hp => hC.1 (hp.eq_of_length hC.2.1.symm).symm⟩⟩ hns
      exact hnd ⟨L, L', ha', hb', hC, hComp⟩
    obtain ⟨hK2, hside⟩ := hsep
    have hK0 : ∃ a₀, K.getLast? = some a₀ := by
      rcases hl : K.getLast? with _ | a₀
      · rw [List.getLast?_eq_none_iff] at hl
        subst hl
        simp at hK2
      · exact ⟨a₀, rfl⟩
    obtain ⟨a₀, ha₀⟩ := hK0
    have hmem : a₀ ∈ K := by
      obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp ha₀
      simp
    have huniq : ∀ {L₂ L₂' : List (Item X M)}, (l ++ [K])[a]? = some L₂ →
        (l ++ [K])[b]? = some L₂' → L₂ = L ∧ L₂' = L' := by
      intro L₂ L₂' h1 h2
      rw [ha] at h1
      rw [hb] at h2
      exact ⟨(Option.some.inj h1).symm, (Option.some.inj h2).symm⟩
    rw [bind_pure_comp, prEvent_map]
    rcases hside with ⟨hp, hnp⟩ | ⟨hp, hnp⟩
    · have hT : tm a₀ ≠ 0 := hC.2.2.2.1 a₀ (hp.subset hmem)
      refine (prEvent_mono_of_support _ _
        (fun v => Ssum red tm c L + (red v).val • tm a₀ = Ssum red tm c L')
        fun v _ hv => ?_).trans (fresh_hit_prob red hμ hord hT _ _)
      by_contra hne
      apply hv
      intro L₂ L₂' ha₂ hb₂ _ _
      obtain ⟨e1, e2⟩ := huniq ha₂ hb₂
      subst e1 e2
      change Ssum red tm (c.cacheQuery K v) L₂ ≠ Ssum red tm (c.cacheQuery K v) L₂'
      rw [Ssum_update_prefix red tm v hc hK2 ha₀ L₂ hp,
        Ssum_update_not_prefix red tm v L₂' hnp]
      exact hne
    · have hT : tm a₀ ≠ 0 := hC.2.2.2.2 a₀ (hp.subset hmem)
      refine (prEvent_mono_of_support _ _
        (fun v => Ssum red tm c L' + (red v).val • tm a₀ = Ssum red tm c L)
        fun v _ hv => ?_).trans (fresh_hit_prob red hμ hord hT _ _)
      by_contra hne
      apply hv
      intro L₂ L₂' ha₂ hb₂ _ _
      obtain ⟨e1, e2⟩ := huniq ha₂ hb₂
      subst e1 e2
      change Ssum red tm (c.cacheQuery K v) L₂ ≠ Ssum red tm (c.cacheQuery K v) L₂'
      rw [Ssum_update_not_prefix red tm v L₂ hnp,
        Ssum_update_prefix red tm v hc hK2 ha₀ L₂' hp]
      exact fun h => hne h.symm

end Pair

/-! ## Runs of the recording oracle -/

theorem logImpl_hash_support (K : List (Item X M)) (σ : LState H X M) :
    ∀ p ∈ support ((logImpl (.inr K)).run σ),
      p.2.1 K = some p.1 ∧ (∀ K₀ v, σ.1 K₀ = some v → p.2.1 K₀ = some v) ∧
        p.2.2.length ≤ σ.2.length + 1 ∧ (∀ K₀, K₀ ∈ σ.2 → K₀ ∈ p.2.2) ∧
        (σ.1 K = none → K ∈ p.2.2) := by
  intro p hp
  rcases hc : σ.1 K with _ | v
  · rw [logImpl_miss hc] at hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
    obtain ⟨v, -, rfl⟩ := hp
    refine ⟨by simp, fun K₀ v₀ h => ?_, by simp, fun K₀ h => List.mem_append_left _ h,
      fun _ => by simp⟩
    rw [QueryCache.cacheQuery_of_ne _ _ (fun hk => by rw [hk, hc] at h; cases h)]
    exact h
  · rw [logImpl_hit hc] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨hc, fun _ _ h => h, by simp, fun _ h => h, fun h => by cases h⟩

/-- Every cached key is recorded. -/
def LogWF (σ : LState H X M) : Prop := ∀ K, σ.1 K ≠ none → K ∈ σ.2

theorem log_wf {α : Type} (oa : OracleComp (unifSpec + RandSpec H X M) α) (σ : LState H X M)
    (hσ : LogWF σ) : ∀ z ∈ support ((simulateQ logImpl oa).run σ), LogWF z.2 := by
  refine OracleComp.simulateQ_run_preservesInv logImpl LogWF ?_ oa σ hσ
  intro t σ0 h0 z hz
  rcases t with k | K
  · rw [logImpl_unif, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact h0
  · obtain ⟨h1, h2, -, h4, h5⟩ := logImpl_hash_support K σ0 z hz
    intro K₀ hK₀
    by_cases hk : K₀ = K
    · subst hk
      rcases hc : σ0.1 K₀ with _ | v
      · exact h5 hc
      · exact h4 _ (h0 _ (by rw [hc]; exact Option.some_ne_none v))
    · rcases hc : σ0.1 K₀ with _ | v
      · -- a key other than `K` is cached after the step only if it was before
        exfalso
        rcases hcK : σ0.1 K with _ | w
        · rw [logImpl_miss hcK] at hz
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
          obtain ⟨w, -, rfl⟩ := hz
          exact hK₀ (by rw [QueryCache.cacheQuery_of_ne _ _ hk]; exact hc)
        · rw [logImpl_hit hcK] at hz
          simp only [support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact hK₀ hc
      · exact h4 _ (h0 _ (by rw [hc]; exact Option.some_ne_none v))

/-- A computation with at most `Q` hash queries records at most `Q` keys. -/
theorem log_length {α : Type} (oa : OracleComp (unifSpec + RandSpec H X M) α) (Q : ℕ)
    (h : oa.IsQueryBoundP isHash Q) (σ : LState H X M) :
    ∀ z ∈ support ((simulateQ logImpl oa).run σ), z.2.2.length ≤ σ.2.length + Q := by
  induction oa using OracleComp.inductionOn generalizing Q σ with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Nat.le_add_right _ _
  | query_bind t mx ih =>
    intro z hz
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    rcases t with k | K
    · rw [logImpl_unif, support_map] at hp
      obtain ⟨u, -, rfl⟩ := hp
      exact ih u Q (by simpa [isHash] using h.2 u) σ z hz
    · have hQ : 0 < Q := by simpa [isHash] using h.1
      have h3 := (logImpl_hash_support K σ p hp).2.2.1
      have := ih p.1 (Q - 1) (by simpa [isHash] using h.2 p.1) p.2 z hz
      omega

theorem log_hasQuery (K : List (Item X M)) :
    simulateQ (logImpl (H := H) (X := X) (M := M))
      (HasQuery.query (spec := RandSpec H X M) K : OracleComp (unifSpec + RandSpec H X M) H) =
      logImpl (.inr K) := by
  change simulateQ logImpl (liftM ((unifSpec + RandSpec H X M).query (.inr K))) = _
  rw [simulateQ_spec_query]

/-- The randomizer `zᵢ` of the list `L` from a cache. -/
def zAt (c : (RandSpec H X M).QueryCache) (L : List (Item X M)) (i : ℕ) : ZMod n :=
  if i = 0 then 1 else ((c (L.take (i + 1))).map red).getD 0

/-- The verifier's randomizers are read off the final cache, which holds every
prefix it asked for. -/
theorem zs_log (L : List (Item X M)) (is : List ℕ) (σ : LState H X M) :
    ∀ y ∈ support ((simulateQ logImpl (is.mapM (zQuery red (n := n) L))).run σ),
      (∀ K v, σ.1 K = some v → y.2.1 K = some v) ∧
      (∀ i ∈ is, i ≠ 0 → y.2.1 (L.take (i + 1)) ≠ none) ∧
      y.1 = is.map (zAt red y.2.1 L) := by
  induction is generalizing σ with
  | nil =>
    intro y hy
    simp only [List.mapM_nil, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨fun _ _ h => h, by simp, rfl⟩
  | cons i is ih =>
    intro y hy
    rw [List.mapM_cons] at hy
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨p, hp, hy⟩ := hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨q, hq, hy⟩ := hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨hext2, hall2, hval2⟩ := ih p.2 q hq
    -- the first draw
    have hfirst : (∀ K v, σ.1 K = some v → p.2.1 K = some v) ∧
        (i ≠ 0 → ∃ v, p.2.1 (L.take (i + 1)) = some v ∧ p.1 = red v) ∧ (i = 0 → p.1 = 1) := by
      unfold zQuery at hp
      by_cases hi : i = 0
      · simp only [hi, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hp
        subst hp
        exact ⟨fun _ _ h => h, fun h => absurd hi h, fun _ => rfl⟩
      · simp only [hi, ↓reduceIte, simulateQ_map, StateT.run_map, support_map,
          log_hasQuery] at hp
        obtain ⟨r, hr, rfl⟩ := hp
        have hr' : r ∈ support ((logImpl (.inr (L.take (i + 1)))).run σ) := hr
        obtain ⟨h1, h2, -⟩ := logImpl_hash_support (L.take (i + 1)) σ r hr'
        exact ⟨h2, fun _ => ⟨r.1, h1, rfl⟩, fun h => absurd h hi⟩
    obtain ⟨hext1, hne1, hz1⟩ := hfirst
    refine ⟨fun K v h => hext2 K v (hext1 K v h), ?_, ?_⟩
    · intro j hj hj0
      rcases List.mem_cons.mp hj with rfl | hj
      · obtain ⟨v, hv, -⟩ := hne1 hj0
        rw [hext2 _ v hv]
        exact Option.some_ne_none v
      · exact hall2 j hj hj0
    · rw [List.map_cons, hval2]
      unfold zAt
      by_cases hi : i = 0
      · simp [hi, hz1 hi]
      · obtain ⟨v, hv, hpv⟩ := hne1 hi
        simp [hi, hext2 _ v hv, hpv]

/-! ## A winning run has a recorded pair with equal sums -/

/-- The binding game, returning the adversary's output and the randomizers. -/
noncomputable def bindGameX
    (A : OracleComp (unifSpec + RandSpec H X M) (AggSig n X × List (X × M) × List (X × M))) :
    OracleComp (unifSpec + RandSpec H X M)
      ((AggSig n X × List (X × M) × List (X × M)) × List (ZMod n) × List (ZMod n)) := do
  let out ← A
  let zs ← (List.range out.1.rs.length).mapM (zQuery red (items out.2.1 out.1.rs))
  let zs' ← (List.range out.1.rs.length).mapM (zQuery red (items out.2.2 out.1.rs))
  return (out, zs, zs')

theorem bindGame_eq (ch : X → X → M → ZMod n)
    (A : OracleComp (unifSpec + RandSpec H X M) (AggSig n X × List (X × M) × List (X × M))) :
    bindGame C red ch A =
      (fun x => bindWins C ch x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2) <$> bindGameX red A := by
  simp only [bindGame, bindGameX, map_bind, map_pure]

/-- The challenge hash is degenerate on the adversary's output: an item's term
`R + e⋅P` vanishes, or the lists are two different single items with the same
term. -/
def badC (ch : X → X → M → ZMod n) (agg : AggSig n X) (pm pm' : List (X × M)) : Prop :=
  (∃ it ∈ items pm agg.rs ++ items pm' agg.rs, lifts C it = true ∧ term C ch it = 0) ∨
    ∃ it it', items pm agg.rs = [it] ∧ items pm' agg.rs = [it'] ∧ it ≠ it' ∧
      lifts C it = true ∧ lifts C it' = true ∧ term C ch it = term C ch it'

theorem items_inj : ∀ (rs : List X) (pm pm' : List (X × M)), rs.length = pm.length →
    rs.length = pm'.length → items pm rs = items pm' rs → pm = pm'
  | [], pm, pm', h, h', _ => by
      rw [List.length_nil] at h h'
      rw [List.length_eq_zero_iff.mp h.symm, List.length_eq_zero_iff.mp h'.symm]
  | r :: rs, [], _, h, _, _ => by simp at h
  | r :: rs, _ :: _, [], _, h', _ => by simp at h'
  | r :: rs, p :: ps, p' :: ps', h, h', he => by
      simp only [items, List.zipWith_cons_cons, List.cons.injEq, Prod.mk.injEq, true_and] at he
      have ht := items_inj rs ps ps' (by simpa using h) (by simpa using h') he.2
      rw [ht, Prod.ext he.1.1 he.1.2]

theorem items_length {rs : List X} {pm : List (X × M)} (h : rs.length = pm.length) :
    (items pm rs).length = rs.length := by
  simp [items, List.length_zipWith, h]

/-- The verifier's sum, with the randomizers read off a cache, is the sum of the
list from any later cache. -/
theorem sum_of_zs (tm : Item X M → E) (c c' : (RandSpec H X M).QueryCache)
    (L : List (Item X M)) (hext : ∀ K v, c K = some v → c' K = some v)
    (hall : ∀ i ∈ List.range L.length, i ≠ 0 → c (L.take (i + 1)) ≠ none) :
    isum (fun i it => (((List.range L.length).map (zAt red c L)).getD i 0).val • tm it) 0 L =
      Ssum red tm c' L := by
  unfold Ssum
  refine isum_congr fun i it _ _ hi => ?_
  have hi' : i < L.length := by omega
  have hget : ((List.range L.length).map (zAt red c L)).getD i 0 = zAt red c L i := by
    simp [List.getD_eq_getElem?_getD, hi']
  rw [hget]
  congr 2
  unfold zAt zL
  by_cases h0 : i = 0
  · subst h0
    have h1 : (L.take (0 + 1)).length ≤ 1 := by
      rw [List.length_take]
      omega
    simp only [↓reduceIte, h1]
  · have hlen : ¬ (L.take (i + 1)).length ≤ 1 := by
      rw [List.length_take]
      omega
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hall i (List.mem_range.mpr hi') h0)
    simp only [h0, hlen, ↓reduceIte, hv, hext _ v hv]

/-- **A winning run records a pair with equal sums**, unless the challenge hash
is degenerate on the output. -/
theorem win_pair (ch : X → X → M → ZMod n)
    (A : OracleComp (unifSpec + RandSpec H X M) (AggSig n X × List (X × M) × List (X × M)))
    (Q : ℕ) (hQ : (bindGameX red A).IsQueryBoundP isHash Q) :
    ∀ z ∈ support ((simulateQ logImpl (bindGameX red A)).run ((∅, []) : LState H X M)),
      bindWins C ch z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2.1 z.1.2.2 = true →
      ¬ badC C ch z.1.1.1 z.1.1.2.1 z.1.1.2.2 →
      ∃ ab ∈ Finset.range Q ×ˢ Finset.range Q, ¬ InvP red (term C ch) ab.1 ab.2 z.2 := by
  intro z hz hwin hbad
  have hwf := log_wf (bindGameX red A) ((∅, []) : LState H X M)
    (fun K h => absurd rfl h) z hz
  have hlen := log_length (bindGameX red A) Q hQ ((∅, []) : LState H X M) z hz
  unfold bindGameX at hz
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨p1, -, hz⟩ := hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨p2, hp2, hz⟩ := hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨p3, hp3, hz⟩ := hz
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  obtain ⟨⟨agg, pm, pm'⟩, σ1⟩ := p1
  obtain ⟨zs, σ2⟩ := p2
  obtain ⟨zs', ⟨c, l⟩⟩ := p3
  simp only [bindWins, Bool.and_eq_true, decide_eq_true_eq] at hwin
  obtain ⟨⟨hne, hv⟩, hv'⟩ := hwin
  simp only [verifyWith, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv hv'
  obtain ⟨⟨hlenpm, hlifts⟩, heq⟩ := hv
  obtain ⟨⟨hlenpm', hlifts'⟩, heq'⟩ := hv'
  have hL := items_length (pm := pm) hlenpm
  have hL' := items_length (pm := pm') hlenpm'
  obtain ⟨hext2, hall2, hval2⟩ := zs_log red (items pm agg.rs) (List.range agg.rs.length) σ1
    (zs, σ2) hp2
  obtain ⟨hext3, hall3, hval3⟩ := zs_log red (items pm' agg.rs) (List.range agg.rs.length) σ2
    (zs', (c, l)) hp3
  simp only at hext2 hall2 hval2 hext3 hall3 hval3 hlen hwf
  rw [← hL] at hall2 hval2
  rw [← hL'] at hall3 hval3
  have hS : isum (fun i it => (zs.getD i 0).val • term C ch it) 0 (items pm agg.rs) =
      Ssum red (term C ch) c (items pm agg.rs) := by
    rw [hval2]
    exact sum_of_zs red (term C ch) σ2.1 c _ hext3 hall2
  have hS' : isum (fun i it => (zs'.getD i 0).val • term C ch it) 0 (items pm' agg.rs) =
      Ssum red (term C ch) c (items pm' agg.rs) := by
    rw [hval3]
    exact sum_of_zs red (term C ch) c c _ (fun _ _ h => h) hall3
  have hsum : Ssum red (term C ch) c (items pm agg.rs) =
      Ssum red (term C ch) c (items pm' agg.rs) := by
    rw [← hS, ← hS', ← heq, ← heq']
  have hneL : items pm agg.rs ≠ items pm' agg.rs :=
    fun h => hne (items_inj agg.rs pm pm' hlenpm hlenpm' h)
  have hnz : ∀ it ∈ items pm agg.rs, term C ch it ≠ 0 := fun it hit h0 =>
    hbad (Or.inl ⟨it, List.mem_append_left _ hit, hlifts it hit, h0⟩)
  have hnz' : ∀ it ∈ items pm' agg.rs, term C ch it ≠ 0 := fun it hit h0 =>
    hbad (Or.inl ⟨it, List.mem_append_right _ hit, hlifts' it hit, h0⟩)
  have h2 : 2 ≤ (items pm agg.rs).length := by
    by_contra hlt
    have hle : (items pm agg.rs).length ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · have e1 := List.length_eq_zero_iff.mp h0
      have e2 := List.length_eq_zero_iff.mp (by rw [hL', ← hL]; exact h0 :
        (items pm' agg.rs).length = 0)
      exact hneL (e1.trans e2.symm)
    · obtain ⟨it, hit⟩ := List.length_eq_one_iff.mp h1
      obtain ⟨it', hit'⟩ := List.length_eq_one_iff.mp (by rw [hL', ← hL]; exact h1 :
        (items pm' agg.rs).length = 1)
      have hone : (1 : ZMod n).val = 1 := by
        have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
        exact ZMod.val_one n
      have hterm : term C ch it = term C ch it' := by
        have := hsum
        rw [hit, hit'] at this
        simpa [Ssum, zL, hone] using this
      exact hbad (Or.inr ⟨it, it', hit, hit', fun h => hneL (by rw [hit, hit', h]),
        hlifts it (by rw [hit]; simp), hlifts' it' (by rw [hit']; simp), hterm⟩)
  have hcond : Cond (term C ch) (items pm agg.rs) (items pm' agg.rs) :=
    ⟨hneL, by rw [hL, hL'], h2, hnz, hnz'⟩
  have hcached : ∀ K, K <+: items pm agg.rs → 2 ≤ K.length → c K ≠ none := by
    intro K hK hK2
    have hle := hK.length_le
    have htake := List.prefix_iff_eq_take.mp hK
    have := hall2 (K.length - 1) (List.mem_range.mpr (by omega)) (by omega)
    rw [show K.length - 1 + 1 = K.length by omega, ← htake] at this
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp this
    rw [hext3 _ v hv]
    exact Option.some_ne_none v
  have hcached' : ∀ K, K <+: items pm' agg.rs → 2 ≤ K.length → c K ≠ none := by
    intro K hK hK2
    have hle := hK.length_le
    have htake := List.prefix_iff_eq_take.mp hK
    have := hall3 (K.length - 1) (List.mem_range.mpr (by omega)) (by omega)
    rwa [show K.length - 1 + 1 = K.length by omega, ← htake] at this
  have hcomp : Complete c (items pm agg.rs) (items pm' agg.rs) := by
    rintro K ⟨hK2, ⟨hp, -⟩ | ⟨hp, -⟩⟩
    · exact hcached K hp hK2
    · exact hcached' K hp hK2
  obtain ⟨a, ha⟩ := List.getElem?_of_mem (hwf _ (hcached _ (List.prefix_refl _) h2))
  obtain ⟨b, hb⟩ := List.getElem?_of_mem
    (hwf _ (hcached' _ (List.prefix_refl _) (by rw [hL', ← hL]; exact h2)))
  have ha' : a < l.length := (List.getElem?_eq_some_iff.mp ha).1
  have hb' : b < l.length := (List.getElem?_eq_some_iff.mp hb).1
  simp only [List.length_nil, zero_add] at hlen
  refine ⟨(a, b), ?_, fun hInv => hInv _ _ ha hb hcond hcomp hsum⟩
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
  exact ⟨by omega, by omega⟩

/-- **A run wins with a nondegenerate challenge hash with probability at most
`Q²⋅μ`**, for a game with at most `Q` randomizer-hash queries. -/
theorem pair_term {μ : ℝ≥0∞} (hμ : RedBound red μ) (hord : PrimeOrder n E)
    (ch : X → X → M → ZMod n)
    (A : OracleComp (unifSpec + RandSpec H X M) (AggSig n X × List (X × M) × List (X × M)))
    (Q : ℕ) (hQ : (bindGameX red A).IsQueryBoundP isHash Q) :
    Pr{let x ← (simulateQ (RandSpec H X M).romImpl (bindGameX red A)).run' ∅}[
      bindWins C ch x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2 = true ∧
        ¬ badC C ch x.1.1 x.1.2.1 x.1.2.2] ≤ ((Q * Q : ℕ) : ℝ≥0∞) * μ := by
  have hproj := log_project (bindGameX red A) ((∅, []) : LState H X M)
  rw [StateT.run'_eq, ← hproj, Functor.map_map, prEvent_map]
  refine (prEvent_mono_of_support _ _
    (fun z => ∃ ab ∈ Finset.range Q ×ˢ Finset.range Q,
      ¬ InvP red (term C ch) ab.1 ab.2 z.2)
    fun z hz h => win_pair C red ch A Q hQ z hz h.1 h.2).trans ?_
  refine (prEvent_exists_finset_le _ _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ μ fun ab _ =>
    pair_potential logImpl (InvP red (term C ch) ab.1 ab.2) (doneP (term C ch) ab.1 ab.2) μ
      (fun t s hI => log_step red (term C ch) hμ hord ab.1 ab.2 t s hI) _ _
      (fun L L' ha => by simp at ha)).trans ?_
  rw [Finset.card_product, Finset.card_range, nsmul_eq_mul]

end Halfagg.Security
