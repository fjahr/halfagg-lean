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

open Taproot

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)

/-- Every item of `L` before the first one that fails `lift_x` has recorded
representations. -/
def covered (memo : X → Option (Rep n)) : List (Item X M) → Prop
  | [] => True
  | it :: rest =>
    lifts C it = true → ((memo it.1).isSome ∧ (memo it.2.1).isSome) ∧ covered memo rest

instance covered.dec (memo : X → Option (Rep n)) : ∀ L : List (Item X M),
    Decidable (covered C memo L)
  | [] => isTrue trivial
  | it :: rest => by
    have := covered.dec memo rest
    unfold covered
    infer_instance

/-- `memo'` keeps every representation recorded in `memo`. -/
def MemoExt (memo memo' : X → Option (Rep n)) : Prop := ∀ v ρ, memo v = some ρ → memo' v = some ρ

theorem MemoExt.refl (memo : X → Option (Rep n)) : MemoExt memo memo := fun _ _ h => h

theorem covered_ext {memo memo' : X → Option (Rep n)} (h : MemoExt memo memo')
    {L : List (Item X M)} (hc : covered C memo L) : covered C memo' L := by
  induction L with
  | nil => trivial
  | cons it rest ih =>
    simp only [covered] at hc ⊢
    intro hl
    obtain ⟨⟨h1, h2⟩, hr⟩ := hc hl
    obtain ⟨ρ₁, hρ₁⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨ρ₂, hρ₂⟩ := Option.isSome_iff_exists.mp h2
    rw [h _ _ hρ₁, h _ _ hρ₂]
    exact ⟨⟨rfl, rfl⟩, ih hr⟩

theorem annotate_ext {memo memo' : X → Option (Rep n)} (h : MemoExt memo memo')
    {L : List (Item X M)} (hc : covered C memo L) : annotate C memo' L = annotate C memo L := by
  induction L with
  | nil => rfl
  | cons it rest ih =>
    simp only [covered] at hc
    simp only [annotate]
    split_ifs with hl
    · obtain ⟨⟨h1, h2⟩, hr⟩ := hc hl
      obtain ⟨ρ₁, hρ₁⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨ρ₂, hρ₂⟩ := Option.isSome_iff_exists.mp h2
      rw [h _ _ hρ₁, h _ _ hρ₂, hρ₁, hρ₂, ih hr]
    · rfl

theorem covered_take {memo : X → Option (Rep n)} {L : List (Item X M)}
    (hc : covered C memo L) (k : ℕ) : covered C memo (L.take k) := by
  induction L generalizing k with
  | nil => simpa using hc
  | cons it rest ih =>
    cases k with
    | zero => simp [covered]
    | succ k =>
      simp only [List.take_succ_cons, covered] at hc ⊢
      exact fun hl => ⟨(hc hl).1, ih (hc hl).2 k⟩

theorem covered_rawTail (memo : X → Option (Rep n)) (tail : List (Item X M)) :
    covered C memo (rawTail C tail) := by
  rcases tail with _ | ⟨it, rest⟩
  · simp [rawTail, covered]
  · simp only [rawTail]
    split_ifs with hl
    · simp [covered]
    · simp only [covered]
      exact fun h => absurd h hl

theorem covered_append {memo : X → Option (Rep n)} {L T : List (Item X M)}
    (hL : ∀ it ∈ L, (memo it.1).isSome ∧ (memo it.2.1).isSome) (hT : covered C memo T) :
    covered C memo (L ++ T) := by
  induction L with
  | nil => exact hT
  | cons it rest ih =>
    simp only [List.cons_append, covered]
    exact fun _ => ⟨hL it List.mem_cons_self, ih fun a ha => hL a (List.mem_cons_of_mem _ ha)⟩

theorem annotate_inj (memo : X → Option (Rep n)) {L L' : List (Item X M)}
    (h : annotate C memo L = annotate C memo L') : L = L' := by
  have := congrArg (List.map strip) h
  rwa [map_strip_annotate C, map_strip_annotate C] at this

/-- The plain cache read from the annotated cache through `memo`. -/
def plainOf (memo : X → Option (Rep n)) (cA : (AnnSpec n X M).QueryCache) :
    (RandSpec n X M).QueryCache :=
  QueryCache.ofFn fun L => if covered C memo L then cA (annotate C memo L) else none

theorem plainOf_apply (memo : X → Option (Rep n)) (cA : (AnnSpec n X M).QueryCache)
    (L : List (Item X M)) :
    plainOf C memo cA L = if covered C memo L then cA (annotate C memo L) else none := rfl

theorem plainOf_empty (memo : X → Option (Rep n)) :
    plainOf C memo (∅ : (AnnSpec n X M).QueryCache) = ∅ := by
  apply QueryCache.ext; intro L; simp [plainOf_apply]

/-- Every cached key is the annotation of its plain list. -/
def CacheInv (memo : X → Option (Rep n)) (cA : (AnnSpec n X M).QueryCache) : Prop :=
  ∀ K z, cA K = some z → covered C memo (K.map strip) ∧ annotate C memo (K.map strip) = K

theorem cacheInv_empty (memo : X → Option (Rep n)) :
    CacheInv C memo (∅ : (AnnSpec n X M).QueryCache) := by
  intro K z h; simp at h

theorem cacheInv_ext {memo memo' : X → Option (Rep n)} {cA : (AnnSpec n X M).QueryCache}
    (hinv : CacheInv C memo cA) (h : MemoExt memo memo') : CacheInv C memo' cA := by
  intro K z hK
  obtain ⟨hc, ha⟩ := hinv K z hK
  exact ⟨covered_ext C h hc, (annotate_ext C h hc).trans ha⟩

theorem plainOf_ext {memo memo' : X → Option (Rep n)} {cA : (AnnSpec n X M).QueryCache}
    (hinv : CacheInv C memo cA) (h : MemoExt memo memo') :
    plainOf C memo' cA = plainOf C memo cA := by
  apply QueryCache.ext
  intro L
  rw [plainOf_apply, plainOf_apply]
  by_cases hc : covered C memo L
  · simp only [hc, covered_ext C h hc, ↓reduceIte]
    rw [annotate_ext C h hc]
  · simp only [hc, ↓reduceIte]
    split_ifs with hc'
    · rcases hK : cA (annotate C memo' L) with _ | z
      · rfl
      · obtain ⟨hcov, -⟩ := hinv _ z hK
        rw [map_strip_annotate C] at hcov
        exact absurd hcov hc
    · rfl

theorem plainOf_cacheQuery {memo : X → Option (Rep n)} (cA : (AnnSpec n X M).QueryCache)
    {L : List (Item X M)} (hc : covered C memo L) (u : ZMod n) :
    plainOf C memo (cA.cacheQuery (annotate C memo L) u) = (plainOf C memo cA).cacheQuery L u := by
  apply QueryCache.ext
  intro L'
  by_cases hL : L' = L
  · subst hL
    rw [QueryCache.cacheQuery_self, plainOf_apply]
    simp only [hc, ↓reduceIte]
    rw [QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ hL, plainOf_apply, plainOf_apply]
    split_ifs
    · rw [QueryCache.cacheQuery_of_ne _ _ fun h => hL (annotate_inj C memo h)]
    · rfl

theorem cacheInv_cacheQuery {memo : X → Option (Rep n)} {cA : (AnnSpec n X M).QueryCache}
    (hinv : CacheInv C memo cA) {L : List (Item X M)} (hc : covered C memo L) (u : ZMod n) :
    CacheInv C memo (cA.cacheQuery (annotate C memo L) u) := by
  intro K z hK
  by_cases hKL : K = annotate C memo L
  · subst hKL
    rw [map_strip_annotate C]
    exact ⟨hc, rfl⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ hKL] at hK
    exact hinv K z hK

/-- **One lazily sampled query projects**: a query at `annotate C memo L` on the
annotated cache projects to a query at `L` on the projected cache. -/
theorem ro_step {memo : X → Option (Rep n)} (cA : (AnnSpec n X M).QueryCache)
    {L : List (Item X M)} (hc : covered C memo L) :
    ((RandSpec n X M).randomOracle L).run (plainOf C memo cA) =
      (fun p => (p.1, plainOf C memo p.2)) <$>
        ((AnnSpec n X M).randomOracle (annotate C memo L)).run cA := by
  rw [randomOracle.run_eq, randomOracle.run_eq, plainOf_apply]
  simp only [hc, ↓reduceIte]
  rcases cA (annotate C memo L) with _ | z
  · simp [plainOf_cacheQuery C cA hc]
  · simp

theorem ro_step_inv {memo : X → Option (Rep n)} {cA : (AnnSpec n X M).QueryCache}
    (hinv : CacheInv C memo cA) {L : List (Item X M)} (hc : covered C memo L) :
    ∀ p ∈ support (((AnnSpec n X M).randomOracle (annotate C memo L)).run cA),
      CacheInv C memo p.2 := by
  intro p hp
  rw [randomOracle.run_eq] at hp
  rcases h : cA (annotate C memo L) with _ | z
  · rw [h] at hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
    obtain ⟨u, -, rfl⟩ := hp
    exact cacheInv_cacheQuery C hinv hc u
  · rw [h] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact hinv

end Halfagg.Security
