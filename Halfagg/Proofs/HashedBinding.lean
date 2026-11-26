import Halfagg.Proofs.HashedGame
import Halfagg.Proofs.Binding

/-!
# The binding game with hash outputs as an oracle machine

The same steps as `Halfagg/Proofs/HashedGame.lean` for the game of
`bindExperimentH`. `bindM` queries the challenge hash for the adversary and once
for every item of the two lists.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Halfagg.LoggedRun Halfagg.Hop

variable {n : ℕ} [Fact n.Prime] {H Hc E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)
variable [SampleableType H] (red : H → ZMod n) (redc : Hc → ZMod n)

/-- The adversary's oracles as computations with only the challenge hash as an
oracle: the randomizer hash is sampled lazily inside, with its cache as state. -/
noncomputable def bindInnerH : QueryImpl (BindSpecH H Hc X M)
    (StateT (RandSpec H X M).QueryCache (OracleComp (MSpec Hc X M)))
  | .inl (.inl k) => fun cH => do
      let u ← (liftM (liftM (unifSpec.query k) : ProbComp _) : OracleComp (MSpec Hc X M) _)
      pure (u, cH)
  | .inl (.inr key) => fun cH => do
      let h ← chalQ key
      pure (h, cH)
  | .inr L => fun cH => liftM (((RandSpec H X M).randomOracle L).run cH)

section Runs

variable (cH : (RandSpec H X M).QueryCache)

theorem bh_run_unif (k : ℕ) :
    (bindInnerH (H := H) (Hc := Hc) (X := X) (M := M) (.inl (.inl k))).run cH =
      ((liftM (liftM (unifSpec.query k) : ProbComp _) : OracleComp (MSpec Hc X M) _) >>=
        fun u => pure (u, cH)) := rfl

theorem bh_run_chal (key : M × (X × X)) :
    (bindInnerH (H := H) (Hc := Hc) (.inl (.inr key))).run cH =
      (chalQ key >>= fun h => pure (h, cH)) := rfl

theorem bh_run_rand (L : List (Item X M)) :
    (bindInnerH (H := H) (Hc := Hc) (.inr L)).run cH =
      (liftM (((RandSpec H X M).randomOracle L).run cH) : OracleComp (MSpec Hc X M) _) := rfl

end Runs

section Table

variable (g : M × (X × X) → Hc)

/-- With the challenge hash answered from a table, the adversary with the
randomizer hash inside is the adversary under the lazily sampled randomizer
hash. -/
theorem innerH_table {α : Type} (prog : OracleComp (BindSpecH H Hc X M) α)
    (cH : (RandSpec H X M).QueryCache) :
    simulateQ (tableImpl (R := fun _ => Hc) g) ((simulateQ bindInnerH prog).run cH) =
      (simulateQ (RandSpec H X M).romImpl (simulateQ (answerChalBH g) prog)).run cH := by
  induction prog using OracleComp.inductionOn generalizing cH with
  | pure a => simp
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with (k | key) | L
    · have h2 : (simulateQ (RandSpec H X M).romImpl
          (answerChalBH (H := H) g (.inl (.inl k)))).run cH =
          (fun u => (u, cH)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
        simpa [answerChalBH] using roSim.run_apply_inl (hashSpec := RandSpec H X M)
          (RandSpec H X M).randomOracle k cH
      rw [bh_run_unif, h2]
      simp only [simulateQ_bind, simulateQ_pure, tbl_lift, bind_assoc, pure_bind, bind_map_left]
      exact bind_congr fun u => ih u cH
    · rw [bh_run_chal]
      simp only [simulateQ_bind, simulateQ_pure, tbl_chal, pure_bind, answerChalBH,
        StateT.run_pure]
      exact ih (g key) cH
    · have h2 : (simulateQ (RandSpec H X M).romImpl
          (answerChalBH (H := H) g (.inr L))).run cH =
          ((RandSpec H X M).randomOracle L).run cH := by
        simp [answerChalBH]
      rw [bh_run_rand, h2, tbl_lift]
      exact bind_congr fun p => ih p.1 p.2

end Table

/-! ## The whole game -/

/-- **The binding game as an oracle machine.** It queries the challenge hash for
the adversary and once for every item of the two lists. -/
noncomputable def bindM (A : BindAdversaryH n H Hc X M) : OracleComp (MSpec Hc X M) Bool := do
  let w ← (simulateQ (bindInnerH (H := H)) A.main).run ∅
  let zs ← (liftM ((simulateQ (RandSpec H X M).romImpl
    ((List.range w.1.1.rs.length).mapM (zQuery red (n := n) (items w.1.2.1 w.1.1.rs)))).run
      w.2) : OracleComp (MSpec Hc X M) _)
  let zs' ← (liftM ((simulateQ (RandSpec H X M).romImpl
    ((List.range w.1.1.rs.length).mapM (zQuery red (n := n) (items w.1.2.2 w.1.1.rs)))).run
      zs.2) : OracleComp (MSpec Hc X M) _)
  let es ← chalsM redc (items w.1.2.1 w.1.1.rs ++ items w.1.2.2 w.1.1.rs)
  pure (bindWins C (knownChal ((items w.1.2.1 w.1.1.rs ++ items w.1.2.2 w.1.1.rs).map toA) es)
    w.1.1 w.1.2.1 w.1.2.2 zs.1 zs'.1)

/-- `VerifyAggregate` reads the challenge hash only at the items. -/
theorem verifyWith_congr {ch ch' : X → X → M → ZMod n} (zf : ℕ → ZMod n) (agg : AggSig n X)
    (pm : List (X × M))
    (h : ∀ it ∈ items pm agg.rs, ch it.1 it.2.1 it.2.2 = ch' it.1 it.2.1 it.2.2) :
    verifyWith C ch zf agg pm = verifyWith C ch' zf agg pm := by
  have hs : isum (fun i it => (zf i).val • term C ch it) 0 (items pm agg.rs) =
      isum (fun i it => (zf i).val • term C ch' it) 0 (items pm agg.rs) :=
    isum_congr fun i it hit _ _ => by simp only [term, h it hit]
  unfold verifyWith
  simp only [hs]

theorem knownChal_toA (gs : M × (X × X) → ZMod n) (its : List (Item X M)) {it : Item X M}
    (hit : it ∈ its) :
    knownChal (its.map toA) (its.map fun it => gs (it.2.2, (it.1, it.2.1))) it.1 it.2.1 it.2.2 =
      hOf gs it.1 it.2.1 it.2.2 := by
  have h := knownChal_eq gs (its.map toA) (a := toA it) (List.mem_map.mpr ⟨it, hit, rfl⟩)
  simpa [toA, Function.comp_def] using h

/-- The win check with the challenges of the items of both lists is the win
check with the challenge function. -/
theorem bindWins_known (gs : M × (X × X) → ZMod n) (agg : AggSig n X) (pm pm' : List (X × M))
    (zs zs' : List (ZMod n)) :
    bindWins C (knownChal ((items pm agg.rs ++ items pm' agg.rs).map toA)
        ((items pm agg.rs ++ items pm' agg.rs).map fun it => gs (it.2.2, (it.1, it.2.1))))
        agg pm pm' zs zs' = bindWins C (hOf gs) agg pm pm' zs zs' := by
  unfold bindWins
  rw [verifyWith_congr C _ agg pm (fun it hit =>
      knownChal_toA gs _ (List.mem_append_left _ hit)),
    verifyWith_congr C _ agg pm' (fun it hit =>
      knownChal_toA gs _ (List.mem_append_right _ hit))]

/-- **The machine with its queries answered from a table is the game for that
table.** -/
theorem bindM_table (g : M × (X × X) → Hc) (A : BindAdversaryH n H Hc X M) :
    simulateQ (tableImpl (R := fun _ => Hc) g) (bindM C red redc A) =
      (simulateQ (RandSpec H X M).romImpl
        (bindGame C red (hOf fun key => redc (g key))
          (simulateQ (answerChalBH g) A.main))).run' ∅ := by
  unfold bindM bindGame
  simp only [simulateQ_bind, simulateQ_pure, tbl_lift, tbl_chals, innerH_table, StateT.run'_eq,
    StateT.run_bind, StateT.run_pure, map_bind, map_pure, pure_bind,
    bindWins_known C (fun key => redc (g key))]

/-! ## The machine's queries -/

theorem innerH_bound {α : Type} (prog : OracleComp (BindSpecH H Hc X M) α) (a : ℕ)
    (ha : prog.IsQueryBoundP (fun t => isChalB t) a) (cH : (RandSpec H X M).QueryCache) :
    ((simulateQ (bindInnerH (H := H)) prog).run cH).IsQueryBoundP isHash a := by
  induction prog using OracleComp.inductionOn generalizing a cH with
  | pure x => simp
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at ha
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with (k | key) | L
    · rw [bh_run_unif]
      refine (isQueryBoundP_bind (n := 0) (isQueryBoundP_bind (n := 0) (m := 0) (mLift_bound _)
        fun _ _ => isQueryBoundP_pure _ _ _) fun y _ => ih y.1 a (ha.2 y.1)
          y.2).mono (by omega)
    · have ha0 : 0 < a := by simpa [isChalB] using ha.1
      rw [bh_run_chal]
      refine (isQueryBoundP_bind (n := 1) (isQueryBoundP_bind (n := 1) (m := 0) (chalQ_bound _)
        fun _ _ => isQueryBoundP_pure _ _ _) fun y _ => ih y.1 (a - 1)
          (ha.2 y.1) y.2).mono (by omega)
    · rw [bh_run_rand]
      refine (isQueryBoundP_bind (n := 0) (mLift_bound _) fun y _ => ih y.1 a
        (ha.2 y.1) y.2).mono (by omega)

/-- Every output of the adversary's run under `bindInnerH` is an output of the
adversary. -/
theorem innerH_support {α : Type} (prog : OracleComp (BindSpecH H Hc X M) α)
    (cH : (RandSpec H X M).QueryCache) :
    ∀ z ∈ support ((simulateQ (bindInnerH (H := H)) prog).run cH), z.1 ∈ support prog := by
  induction prog using OracleComp.inductionOn generalizing cH with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp
  | query_bind t next ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨y, -, hz⟩ := hz
    exact (mem_support_bind_iff _ _ _).mpr ⟨y.1, mem_support_query _ y.1, ih _ _ z hz⟩

/-- **The machine's queries**: at most `qC + 2⋅ℓ` for an adversary with at most
`qC` challenge queries and aggregates of at most `ℓ` signatures. -/
theorem bindM_bound (A : BindAdversaryH n H Hc X M) (qC ℓ : ℕ)
    (hC : A.main.IsQueryBoundP (fun t => isChalB t) qC)
    (hL : ∀ out ∈ support A.main, out.1.rs.length ≤ ℓ) :
    (bindM C red redc A).IsQueryBoundP isHash (qC + 2 * ℓ) := by
  unfold bindM
  refine isQueryBoundP_bind (innerH_bound _ qC hC _) fun w hw => ?_
  have hlen : (items w.1.2.1 w.1.1.rs ++ items w.1.2.2 w.1.1.rs).length ≤ 2 * ℓ := by
    have h1 := items_length_le w.1.2.1 w.1.1.rs
    have h2 := items_length_le w.1.2.2 w.1.1.rs
    have h3 := hL _ (innerH_support _ _ w hw)
    rw [List.length_append]
    omega
  exact (isQueryBoundP_bind (n := 0) (mLift_bound _) fun zs _ =>
    isQueryBoundP_bind (n := 0) (mLift_bound _) fun zs' _ =>
      isQueryBoundP_bind (m := 0) (chalsM_bound redc _)
        fun es _ => isQueryBoundP_pure _ _ _).mono (by omega)

/-! ## The comparison -/

/-- A table of scalars read through `repChalB` is the table of the hash outputs
`rep (g key)`. -/
theorem answerChalB_repChalB (rep : ZMod n → Hc) (g : M × (X × X) → ZMod n) {α : Type}
    (prog : OracleComp (BindSpecH H Hc X M) α) :
    simulateQ (answerChalB g) (simulateQ (repChalB rep) prog) =
      simulateQ (answerChalBH fun key => rep (g key)) prog := by
  induction prog using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    rcases t with (k | key) | L
    · have h1 : simulateQ (answerChalB g) (repChalB (H := H) (Hc := Hc) rep (.inl (.inl k))) =
          liftM ((unifSpec + RandSpec H X M).query (.inl k)) := by
        simp [repChalB, answerChalB]
      rw [h1]
      exact bind_congr fun u => ih u
    · have h1 : simulateQ (answerChalB g) (repChalB (H := H) rep (.inl (.inr key))) =
          pure (rep (g key)) := by
        simp [repChalB, answerChalB]
      rw [h1]
      simp only [answerChalBH, pure_bind]
      exact ih _
    · have h1 : simulateQ (answerChalB g) (repChalB (n := n) (H := H) (Hc := Hc) rep (.inr L)) =
          liftM ((unifSpec + RandSpec H X M).query (.inr L)) := by
        simp [repChalB, answerChalB]
      rw [h1]
      exact bind_congr fun u => ih u

/-- **The binding game with hash outputs against the game with scalars.** -/
theorem bindAdvantageH_le_viaRep [Finite M] [Finite X] [Finite Hc] [SampleableType Hc]
    [SampleableType (M × (X × X) → Hc)] [SampleableType (M × (X × X) → ZMod n)]
    (rep : ZMod n → Hc) (hrep : ∀ c, redc (rep c) = c) (A : BindAdversaryH n H Hc X M)
    (qC ℓ : ℕ) (hC : A.main.IsQueryBoundP (fun t => isChalB t) qC)
    (hL : ∀ out ∈ support A.main, out.1.rs.length ≤ ℓ) :
    bindAdvantageH C red redc A ≤ bindAdvantage C red (A.viaRep rep) +
      ((qC + 2 * ℓ : ℕ) : ℝ≥0∞) * Pr{let h ← $ᵗ Hc}[rep (redc h) ≠ h] := by
  have h := table_hop (D := M × (X × X)) redc rep hrep (bindM C red redc A) (fun b => b = true)
    (qC + 2 * ℓ) (bindM_bound C red redc A qC ℓ hC hL)
  simp only [bindM_table] at h
  have hg : ∀ g : M × (X × X) → ZMod n, (fun key => redc (rep (g key))) = g := fun g =>
    funext fun key => hrep (g key)
  simp only [hg, ← answerChalB_repChalB] at h
  exact h

/-- `A.viaRep rep` makes the oracle calls of `A`. -/
theorem viaRepB_queries (rep : ZMod n → Hc) (A : BindAdversaryH n H Hc X M)
    (p : (ℕ ⊕ M × (X × X)) ⊕ List (Item X M) → Bool) (q : ℕ)
    (h : A.main.IsQueryBoundP (fun t => p t) q) :
    (A.viaRep rep).main.IsQueryBoundP (fun t => p t) q := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with (k | key) | L
    · simp only [repChalB]
      rw [isQueryBoundP_query_iff]
      exact fun _ => Nat.one_pos
    · simp only [repChalB]
      rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      exact fun _ => Nat.one_pos
    · simp only [repChalB]
      rw [isQueryBoundP_query_iff]
      exact fun _ => Nat.one_pos
  · rcases t with (k | key) | L
    · simp only [repChalB]
      rw [isQueryBoundP_query_iff]
      exact fun h' => absurd h' ht
    · simp only [repChalB]
      rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      exact fun h' => absurd h' ht
    · simp only [repChalB]
      rw [isQueryBoundP_query_iff]
      exact fun h' => absurd h' ht

/-- Every output of `A.viaRep rep` is an output of `A`. -/
theorem viaRepB_support (rep : ZMod n → Hc) {α : Type}
    (prog : OracleComp (BindSpecH H Hc X M) α) :
    ∀ z ∈ support (simulateQ (repChalB (n := n) rep) prog), z ∈ support prog := by
  induction prog using OracleComp.inductionOn with
  | pure x =>
    intro z hz
    simpa using hz
  | query_bind t next ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_spec_query] at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨y, -, hz⟩ := hz
    exact (mem_support_bind_iff _ _ _).mpr ⟨y, mem_support_query _ y, ih y z hz⟩

end Halfagg.Security
