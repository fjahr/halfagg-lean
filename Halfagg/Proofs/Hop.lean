import Halfagg.Proofs.Eager

/-!
# The cost of reducing a hash output

A hash function returns a value of a type `Hc`, for BIP340 a 256-bit string, and
the scheme reduces it to a scalar of a type `S` with `redc`. The oracle of the
random-oracle theorems returns a uniform scalar.

`table_hop` compares the two for any computation with at most `Q` hash queries.
Fix one hash output `rep s` for every scalar `s`. A uniform hash output is one
of them with probability `1 - gap`, and then it is `rep` of a uniform scalar. So
an event has at most the probability it has when every answer is `rep` of a
uniform scalar, plus `Q⋅gap`.
-/

open OracleSpec OracleComp
open scoped ENNReal

namespace Halfagg.Hop

open Halfagg.LoggedRun

variable {D α Hc S : Type}

/-- Answer every hash query with `rep` of the answer of an oracle with range `S`. -/
def viaRep (rep : S → Hc) : QueryImpl (unifSpec + (D →ₒ Hc)) (OracleComp (unifSpec + (D →ₒ S)))
  | .inl k => liftM ((unifSpec + (D →ₒ S)).query (.inl k))
  | .inr d => rep <$> (liftM ((unifSpec + (D →ₒ S)).query (.inr d)) :
      OracleComp (unifSpec + (D →ₒ S)) S)

/-- A table with range `S`, read through `rep`, is the table `rep ∘ g`. -/
theorem table_viaRep (rep : S → Hc) (g : D → S) (oa : OracleComp (unifSpec + (D →ₒ Hc)) α) :
    simulateQ (tableImpl (R := fun _ => S) g) (simulateQ (viaRep rep) oa) =
      simulateQ (tableImpl (R := fun _ => Hc) fun d => rep (g d)) oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    rcases t with k | d
    · have h1 : simulateQ (tableImpl (R := fun _ => S) g) (viaRep (D := D) rep (.inl k)) =
          tableImpl (R := fun _ => Hc) (fun d => rep (g d)) (.inl k) := by
        simp [viaRep, tableImpl]
      rw [h1]
      exact bind_congr fun u => ih u
    · have h1 : simulateQ (tableImpl (R := fun _ => S) g) (viaRep (D := D) rep (.inr d)) =
          pure (rep (g d)) := by
        simp [viaRep, tableImpl]
        rfl
      rw [h1, tableImpl_inr, pure_bind, pure_bind]
      exact ih _

/-- **One sample.** If the continuation after `rep s` is bounded by the
continuation after `s` plus `δ`, then a uniform hash output is bounded by a
uniform scalar plus `δ` and the probability that the hash output is not the
chosen one for its scalar. -/
theorem sample_hop [SampleableType Hc] [SampleableType S] [Finite Hc] [Finite S]
    (redc : Hc → S) (rep : S → Hc) (hrep : ∀ s, redc (rep s) = s) {β γ : Type}
    (L : Hc → ProbComp β) (R : S → ProbComp γ) (p : β → Prop) (q : γ → Prop) (δ : ℝ≥0∞)
    (h : ∀ s, Pr{let y ← L (rep s)}[p y] ≤ Pr{let y ← R s}[q y] + δ) :
    Pr{let y ← ($ᵗ Hc) >>= L}[p y] ≤
      Pr{let y ← ($ᵗ S) >>= R}[q y] + δ + Pr{let h ← $ᵗ Hc}[rep (redc h) ≠ h] := by
  classical
  let _ := Fintype.ofFinite Hc
  let _ := Fintype.ofFinite S
  have hinj : Function.Injective rep := fun a b hab => by
    rw [← hrep a, ← hrep b, hab]
  have hcard : (Fintype.card S : ℝ≥0∞) ≤ Fintype.card Hc := by
    exact_mod_cast Fintype.card_le_of_injective rep hinj
  rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum, tsum_fintype, tsum_fintype,
    SampleableType.prEvent_uniformSample]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton]
  have hgood : (Finset.univ.filter fun h : Hc => ¬ rep (redc h) ≠ h) = Finset.univ.image rep := by
    ext h
    simp only [ne_eq, not_not, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨fun hh => ⟨redc h, hh⟩, fun ⟨s, hs⟩ => by rw [← hs, hrep]⟩
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun h : Hc => rep (redc h) ≠ h)]
  rw [hgood, Finset.sum_image (fun a _ b _ hab => hinj hab), add_comm]
  refine add_le_add ?_ ?_
  · calc ∑ s, (Fintype.card Hc : ℝ≥0∞)⁻¹ * Pr{let y ← L (rep s)}[p y]
        ≤ ∑ s, ((Fintype.card S : ℝ≥0∞)⁻¹ * Pr{let y ← R s}[q y] +
            (Fintype.card Hc : ℝ≥0∞)⁻¹ * δ) := by
          refine Finset.sum_le_sum fun s _ => ?_
          calc (Fintype.card Hc : ℝ≥0∞)⁻¹ * Pr{let y ← L (rep s)}[p y]
              ≤ (Fintype.card Hc : ℝ≥0∞)⁻¹ * (Pr{let y ← R s}[q y] + δ) := by
                gcongr
                exact h s
            _ = (Fintype.card Hc : ℝ≥0∞)⁻¹ * Pr{let y ← R s}[q y] +
                (Fintype.card Hc : ℝ≥0∞)⁻¹ * δ := mul_add _ _ _
            _ ≤ _ := by
                gcongr
      _ = ∑ s, (Fintype.card S : ℝ≥0∞)⁻¹ * Pr{let y ← R s}[q y] +
            (Fintype.card S : ℝ≥0∞) * ((Fintype.card Hc : ℝ≥0∞)⁻¹ * δ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := by
          gcongr
          rw [← mul_assoc]
          refine mul_le_of_le_one_left' ?_
          rw [← div_eq_mul_inv]
          exact ENNReal.div_le_of_le_mul (by rwa [one_mul])
  · calc ∑ h ∈ Finset.univ.filter (fun h : Hc => rep (redc h) ≠ h),
          (Fintype.card Hc : ℝ≥0∞)⁻¹ * Pr{let y ← L h}[p y]
        ≤ ∑ _h ∈ Finset.univ.filter (fun h : Hc => rep (redc h) ≠ h),
          (Fintype.card Hc : ℝ≥0∞)⁻¹ := by
          refine Finset.sum_le_sum fun h _ => mul_le_of_le_one_right' (prEvent_le_one _)
      _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- A cache with range `S`, read through `rep`. -/
def mapCache (rep : S → Hc) (c : (D →ₒ S).QueryCache) : (D →ₒ Hc).QueryCache :=
  QueryCache.ofFn fun d => (c d).map rep

theorem mapCache_apply (rep : S → Hc) (c : (D →ₒ S).QueryCache) (d : D) :
    mapCache rep c d = (c d).map rep := rfl

theorem mapCache_empty (rep : S → Hc) : mapCache (D := D) rep ∅ = ∅ := rfl

theorem mapCache_cacheQuery [DecidableEq D] (rep : S → Hc) (c : (D →ₒ S).QueryCache) (d : D)
    (s : S) :
    mapCache rep (c.cacheQuery d s) = (mapCache rep c).cacheQuery d (rep s) := by
  refine QueryCache.ext fun d' => ?_
  by_cases hd : d' = d
  · subst hd
    simp [mapCache_apply]
  · have h1 : (c.cacheQuery d s) d' = c d' := QueryCache.cacheQuery_of_ne c s hd
    have h2 : ((mapCache rep c).cacheQuery d (rep s)) d' = mapCache rep c d' :=
      QueryCache.cacheQuery_of_ne (mapCache rep c) (rep s) hd
    rw [h2, mapCache_apply, h1, mapCache_apply]

/-- **Lazy sampling.** A computation with at most `Q` hash queries, run with a
lazily sampled oracle with range `Hc`, against the same computation with every
answer `rep` of the answer of a lazily sampled oracle with range `S`. -/
theorem lazy_hop [DecidableEq D] [SampleableType Hc] [SampleableType S] [Finite Hc] [Finite S]
    (redc : Hc → S) (rep : S → Hc) (hrep : ∀ s, redc (rep s) = s)
    (oa : OracleComp (unifSpec + (D →ₒ Hc)) α) (p : α → Prop) (Q : ℕ)
    (hQ : oa.IsQueryBoundP isHash Q) (c : (D →ₒ S).QueryCache) :
    Pr{let z ← (simulateQ (D →ₒ Hc).romImpl oa).run (mapCache rep c)}[p z.1] ≤
      Pr{let z ← (simulateQ (D →ₒ S).romImpl (simulateQ (viaRep rep) oa)).run c}[p z.1] +
        Q * Pr{let h ← $ᵗ Hc}[rep (redc h) ≠ h] := by
  induction oa using OracleComp.inductionOn generalizing Q c with
  | pure x => simp
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hQ
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with k | d
    · have hL : ((D →ₒ Hc).romImpl (.inl k)).run (mapCache rep c) =
          (fun u => (u, mapCache rep c)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
        simpa using roSim.run_apply_inl (hashSpec := D →ₒ Hc) (D →ₒ Hc).randomOracle k
          (mapCache rep c)
      have hR : (simulateQ (D →ₒ S).romImpl (viaRep (D := D) rep (.inl k))).run c =
          (fun u => (u, c)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
        simpa [viaRep] using roSim.run_apply_inl (hashSpec := D →ₒ S) (D →ₒ S).randomOracle k c
      rw [hL, hR, bind_map_left, bind_map_left]
      refine prEvent_bind_le_add_const _ _ _ _ _ _ fun u => ?_
      exact ih u Q (by simpa [isHash] using hQ.2 u) c
    · have hQ0 : 0 < Q := by simpa [isHash] using hQ.1
      obtain ⟨Q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hQ0)
      have hstep : ∀ (h : Hc) (c' : (D →ₒ S).QueryCache),
          Pr{let z ← (simulateQ (D →ₒ Hc).romImpl (mx h)).run (mapCache rep c')}[p z.1] ≤
            Pr{let z ← (simulateQ (D →ₒ S).romImpl (simulateQ (viaRep rep) (mx h))).run c'}[p z.1] +
              Q' * Pr{let h ← $ᵗ Hc}[rep (redc h) ≠ h] := fun h c' =>
        ih h Q' (by simpa [isHash] using hQ.2 h) c'
      have hL : ((D →ₒ Hc).romImpl (.inr d)).run (mapCache rep c) =
          ((D →ₒ Hc).randomOracle d).run (mapCache rep c) := rfl
      have hR : (simulateQ (D →ₒ S).romImpl (viaRep (D := D) rep (.inr d))).run c =
          (fun z => (rep z.1, z.2)) <$> ((D →ₒ S).randomOracle d).run c := by
        simp [viaRep]
      rw [hL, hR, bind_map_left, randomOracle.run_eq, randomOracle.run_eq]
      rcases hc : c d with _ | s
      · have hc' : mapCache rep c d = none := by rw [mapCache_apply, hc]; rfl
        simp only [hc', bind_assoc, pure_bind]
        have := sample_hop redc rep hrep
          (fun h => (simulateQ (D →ₒ Hc).romImpl (mx h)).run ((mapCache rep c).cacheQuery d h))
          (fun s => (simulateQ (D →ₒ S).romImpl (simulateQ (viaRep rep) (mx (rep s)))).run
            (c.cacheQuery d s))
          (fun z => p z.1) (fun z => p z.1) (Q' * Pr{let h ← $ᵗ Hc}[rep (redc h) ≠ h])
          (fun s => by
            rw [← mapCache_cacheQuery]
            exact hstep (rep s) (c.cacheQuery d s))
        refine this.trans (le_of_eq ?_)
        push_cast
        ring
      · have hc' : mapCache rep c d = some (rep s) := by rw [mapCache_apply, hc]; rfl
        simp only [hc', pure_bind]
        refine (hstep (rep s) c).trans ?_
        gcongr
        exact_mod_cast Nat.le_succ Q'

/-- **Sampled tables.** A computation with at most `Q` hash queries wins with a
uniform table with range `Hc` at most as often as with the table `rep ∘ g` for a
uniform table `g` with range `S`, plus `Q` times the probability that a uniform
hash output is not the chosen one for its scalar. -/
theorem table_hop [DecidableEq D] [Finite D] [SampleableType Hc] [SampleableType S]
    [Finite Hc] [Finite S] [SampleableType (D → Hc)] [SampleableType (D → S)]
    (redc : Hc → S) (rep : S → Hc) (hrep : ∀ s, redc (rep s) = s)
    (oa : OracleComp (unifSpec + (D →ₒ Hc)) α) (p : α → Prop) (Q : ℕ)
    (hQ : oa.IsQueryBoundP isHash Q) :
    Pr{let x ← (($ᵗ (D → Hc)) >>= fun g => simulateQ (tableImpl (R := fun _ => Hc) g) oa)}[p x] ≤
      Pr{let x ← (($ᵗ (D → S)) >>= fun g =>
        simulateQ (tableImpl (R := fun _ => Hc) fun d => rep (g d)) oa)}[p x] +
        Q * Pr{let h ← $ᵗ Hc}[rep (redc h) ≠ h] := by
  have hR : (($ᵗ (D → S)) >>= fun g =>
      simulateQ (tableImpl (R := fun _ => Hc) fun d => rep (g d)) oa) =
      (($ᵗ (D → S)) >>= fun g =>
        simulateQ (tableImpl (R := fun _ => S) g) (simulateQ (viaRep rep) oa)) :=
    bind_congr fun g => (table_viaRep rep g oa).symm
  rw [hR, ← rom_eq_table (R := fun _ => Hc), ← rom_eq_table (R := fun _ => S),
    StateT.run'_eq, StateT.run'_eq, prEvent_map, prEvent_map]
  have := lazy_hop redc rep hrep oa p Q hQ ∅
  simpa [mapCache_empty] using this

end Halfagg.Hop
