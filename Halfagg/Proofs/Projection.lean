import Halfagg.Proofs.Trace

/-!
# Projecting the annotated oracle's cache to the plain oracle's

The reduction's random oracle is keyed by annotated lists, the game's by plain
lists. `plainOf memo cA` reads a plain list's answer from the annotated cache
`cA` through the recorded representations `memo`. Under the invariant
`CacheInv` (every cached key is the annotation of its plain list under `memo`):

* growing the memo does not change the projection (`plainOf_ext`);
* caching an answer at `annotate memo L` projects to caching it at `L`
  (`plainOf_cacheQuery`);
* so one lazily sampled query at `annotate memo L` projects to one at `L`
  (`ro_step`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp

namespace Halfagg.Security

variable {n : ℕ} [Fact n.Prime] {X M : Type} [DecidableEq X] [DecidableEq M]

/-- Every x-coordinate of `L` has a recorded representation. -/
def covered (memo : X → Option (Rep n)) (L : List (Item X M)) : Prop :=
  ∀ it ∈ L, (memo it.1).isSome ∧ (memo it.2.1).isSome

instance (memo : X → Option (Rep n)) (L : List (Item X M)) : Decidable (covered memo L) := by
  unfold covered; infer_instance

/-- `memo'` keeps every representation recorded in `memo`. -/
def MemoExt (memo memo' : X → Option (Rep n)) : Prop := ∀ v ρ, memo v = some ρ → memo' v = some ρ

theorem MemoExt.refl (memo : X → Option (Rep n)) : MemoExt memo memo := fun _ _ h => h

theorem covered_ext {memo memo' : X → Option (Rep n)} (h : MemoExt memo memo')
    {L : List (Item X M)} (hc : covered memo L) : covered memo' L := by
  intro it hit
  obtain ⟨h1, h2⟩ := hc it hit
  obtain ⟨ρ₁, hρ₁⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨ρ₂, hρ₂⟩ := Option.isSome_iff_exists.mp h2
  rw [h _ _ hρ₁, h _ _ hρ₂]
  exact ⟨rfl, rfl⟩

theorem annotate_ext {memo memo' : X → Option (Rep n)} (h : MemoExt memo memo')
    {L : List (Item X M)} (hc : covered memo L) : annotate memo' L = annotate memo L := by
  unfold annotate
  refine List.map_congr_left fun it hit => ?_
  obtain ⟨h1, h2⟩ := hc it hit
  obtain ⟨ρ₁, hρ₁⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨ρ₂, hρ₂⟩ := Option.isSome_iff_exists.mp h2
  rw [h _ _ hρ₁, h _ _ hρ₂, hρ₁, hρ₂]

theorem annotate_inj (memo : X → Option (Rep n)) {L L' : List (Item X M)}
    (h : annotate memo L = annotate memo L') : L = L' := by
  have := congrArg (List.map strip) h
  rwa [map_strip_annotate, map_strip_annotate] at this

/-- The plain cache read from the annotated cache through `memo`. -/
def plainOf (memo : X → Option (Rep n)) (cA : (AnnSpec n X M).QueryCache) :
    (RandSpec n X M).QueryCache :=
  QueryCache.ofFn fun L => if covered memo L then cA (annotate memo L) else none

theorem plainOf_apply (memo : X → Option (Rep n)) (cA : (AnnSpec n X M).QueryCache)
    (L : List (Item X M)) :
    plainOf memo cA L = if covered memo L then cA (annotate memo L) else none := rfl

theorem plainOf_empty (memo : X → Option (Rep n)) :
    plainOf memo (∅ : (AnnSpec n X M).QueryCache) = ∅ := by
  apply QueryCache.ext; intro L; simp [plainOf_apply]

/-- Every cached key is the annotation of its plain list. -/
def CacheInv (memo : X → Option (Rep n)) (cA : (AnnSpec n X M).QueryCache) : Prop :=
  ∀ K z, cA K = some z → covered memo (K.map strip) ∧ annotate memo (K.map strip) = K

theorem cacheInv_empty (memo : X → Option (Rep n)) :
    CacheInv memo (∅ : (AnnSpec n X M).QueryCache) := by
  intro K z h; simp at h

theorem cacheInv_ext {memo memo' : X → Option (Rep n)} {cA : (AnnSpec n X M).QueryCache}
    (hinv : CacheInv memo cA) (h : MemoExt memo memo') : CacheInv memo' cA := by
  intro K z hK
  obtain ⟨hc, ha⟩ := hinv K z hK
  exact ⟨covered_ext h hc, (annotate_ext h hc).trans ha⟩

theorem plainOf_ext {memo memo' : X → Option (Rep n)} {cA : (AnnSpec n X M).QueryCache}
    (hinv : CacheInv memo cA) (h : MemoExt memo memo') : plainOf memo' cA = plainOf memo cA := by
  apply QueryCache.ext
  intro L
  rw [plainOf_apply, plainOf_apply]
  by_cases hc : covered memo L
  · simp only [hc, covered_ext h hc, ↓reduceIte]
    rw [annotate_ext h hc]
  · simp only [hc, ↓reduceIte]
    split_ifs with hc'
    · rcases hK : cA (annotate memo' L) with _ | z
      · rfl
      · obtain ⟨hcov, -⟩ := hinv _ z hK
        rw [map_strip_annotate] at hcov
        exact absurd hcov hc
    · rfl

theorem plainOf_cacheQuery {memo : X → Option (Rep n)} (cA : (AnnSpec n X M).QueryCache)
    {L : List (Item X M)} (hc : covered memo L) (u : ZMod n) :
    plainOf memo (cA.cacheQuery (annotate memo L) u) = (plainOf memo cA).cacheQuery L u := by
  apply QueryCache.ext
  intro L'
  by_cases hL : L' = L
  · subst hL
    rw [QueryCache.cacheQuery_self, plainOf_apply]
    simp only [hc, ↓reduceIte]
    rw [QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ hL, plainOf_apply, plainOf_apply]
    split_ifs
    · rw [QueryCache.cacheQuery_of_ne _ _ fun h => hL (annotate_inj memo h)]
    · rfl

theorem cacheInv_cacheQuery {memo : X → Option (Rep n)} {cA : (AnnSpec n X M).QueryCache}
    (hinv : CacheInv memo cA) {L : List (Item X M)} (hc : covered memo L) (u : ZMod n) :
    CacheInv memo (cA.cacheQuery (annotate memo L) u) := by
  intro K z hK
  by_cases hKL : K = annotate memo L
  · subst hKL
    rw [map_strip_annotate]
    exact ⟨hc, rfl⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ hKL] at hK
    exact hinv K z hK

/-- **One lazily sampled query projects**: a query at `annotate memo L` on the
annotated cache projects to a query at `L` on the projected cache. -/
theorem ro_step {memo : X → Option (Rep n)} (cA : (AnnSpec n X M).QueryCache)
    {L : List (Item X M)} (hc : covered memo L) :
    ((RandSpec n X M).randomOracle L).run (plainOf memo cA) =
      (fun p => (p.1, plainOf memo p.2)) <$>
        ((AnnSpec n X M).randomOracle (annotate memo L)).run cA := by
  rw [randomOracle.run_eq, randomOracle.run_eq, plainOf_apply]
  simp only [hc, ↓reduceIte]
  rcases cA (annotate memo L) with _ | z
  · simp [plainOf_cacheQuery cA hc]
  · simp

theorem ro_step_inv {memo : X → Option (Rep n)} {cA : (AnnSpec n X M).QueryCache}
    (hinv : CacheInv memo cA) {L : List (Item X M)} (hc : covered memo L) :
    ∀ p ∈ support (((AnnSpec n X M).randomOracle (annotate memo L)).run cA),
      CacheInv memo p.2 := by
  intro p hp
  rw [randomOracle.run_eq] at hp
  rcases h : cA (annotate memo L) with _ | z
  · rw [h] at hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
    obtain ⟨u, -, rfl⟩ := hp
    exact cacheInv_cacheQuery hinv hc u
  · rw [h] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact hinv

end Halfagg.Security
