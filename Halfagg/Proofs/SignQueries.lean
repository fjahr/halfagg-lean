import Halfagg.Proofs.BridgeReduction

/-!
# The reduction's signing queries

`reduction_sign_bound`: for every set of messages `p`, the reduction makes at
most as many signing queries for messages in `p` as the forger makes signing
requests for them.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)
variable [SampleableType H] {red : H → ZMod n}

/-- Lifted sampling makes no signing queries. -/
theorem lift_sign_zero (p : M → Bool) {β : Type} (oa : ProbComp β) :
    (liftM oa : OracleComp (unifSpec + SignSpec n X M) β).IsQueryBoundP
      (fun t => isSignQuery p t) 0 := by
  rw [← liftComp_eq_liftM, liftComp_def]
  refine IsQueryBoundP.simulateQ_of_step (p := fun _ : ℕ => False)
    (impl := fun t => (liftM (unifSpec.query t) :
      OracleComp (unifSpec + SignSpec n X M) (unifSpec.Range t)))
    (isQueryBoundP_false oa 0) (fun _ h => h.elim) ?_
  intro t _
  change (liftM ((unifSpec + SignSpec n X M).query (Sum.inl t)) :
      OracleComp (unifSpec + SignSpec n X M) _).IsQueryBoundP _ 0
  rw [isQueryBoundP_query_iff]
  simp [isSignQuery]

theorem unif_sign_zero (p : M → Bool) (k : ℕ) :
    (liftM (unifSpec.query k) : OracleComp (unifSpec + SignSpec n X M) _).IsQueryBoundP
      (fun t => isSignQuery p t) 0 := by
  change (liftM ((unifSpec + SignSpec n X M).query (Sum.inl k)) :
      OracleComp (unifSpec + SignSpec n X M) _).IsQueryBoundP _ 0
  rw [isQueryBoundP_query_iff]
  simp [isSignQuery]

theorem signQuery_bound (p : M → Bool) (msg : M) :
    (liftM ((SignSpec n X M).query msg) : OracleComp (unifSpec + SignSpec n X M) _).IsQueryBoundP
      (fun t => isSignQuery p t) (if p msg = true then 1 else 0) := by
  change (liftM ((unifSpec + SignSpec n X M).query (Sum.inr msg)) :
      OracleComp (unifSpec + SignSpec n X M) _).IsQueryBoundP _ _
  rw [isQueryBoundP_query_iff]
  simp only [isSignQuery]
  intro h
  simp [h]

/-- One request costs one signing query if it is a signing request, else none. -/
theorem red_step_sign (p : M → Bool) (pk : X)
    (t : Explained (ZMod n) (Request X M) (Pts E)) (st : Core n X M)
    (c : (AnnSpec n H X M).QueryCache) :
    (((redImpl (H := H) C challenge pk t).run st).run c).IsQueryBoundP (fun t => isSignQuery p t)
      (if isSign p t.value.data = true then 1 else 0) := by
  obtain ⟨⟨data, groups⟩, coeffs⟩ := t
  cases data with
  | random k =>
    unfold redImpl
    rw [coreImpl_run_random]
    simp only [StateT.run_bind, lift_unif_run, bind_map_left]
    exact (isQueryBoundP_bind (n := 0) (m := 0) (unif_sign_zero p k)
      fun _ _ => isQueryBoundP_pure _ _ _).mono (by simp)
  | rand ms tail =>
    unfold redImpl
    rw [coreImpl_run_rand]
    simp only [StateT.run_bind, tableRO_run]
    exact (isQueryBoundP_bind (n := 0) (m := 0) (lift_sign_zero p _)
      fun _ _ => isQueryBoundP_pure _ _ _).mono (by simp)
  | sign msg =>
    unfold redImpl
    rw [coreImpl_run_sign]
    simp only [StateT.run_bind, lift_sign_run, bind_map_left]
    exact isQueryBoundP_bind (m := 0) (signQuery_bound p msg)
      fun _ _ => isQueryBoundP_pure _ _ _

theorem red_stack_sign (p : M → Bool) (pk : X) {Result : Type}
    (prog : OracleComp (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)) Result)
    (q : ℕ) (h : prog.IsQueryBoundP (fun r => isSign p r.value.data) q)
    (st : Core n X M) (c : (AnnSpec n H X M).QueryCache) :
    (((simulateQ (redImpl (H := H) C challenge pk) prog).run st).run c).IsQueryBoundP
      (fun t => isSignQuery p t) q := by
  induction prog using OracleComp.inductionOn generalizing q st c with
  | pure x => simp
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hstep := red_step_sign C challenge p pk t st c
    by_cases hp : isSign p t.value.data = true
    · have hq : 0 < q := h.1.resolve_left (not_not.mpr hp)
      simp only [hp, ↓reduceIte] at hstep
      refine (isQueryBoundP_bind (n := 1) (m := q - 1) hstep fun y _ =>
        ih y.1.1 (q - 1) (by simpa [hp] using h.2 y.1.1) y.1.2 y.2).mono (by omega)
    · simp only [hp] at hstep
      refine (isQueryBoundP_bind (n := 0) (m := q) hstep fun y _ =>
        ih y.1.1 q (by simpa [hp] using h.2 y.1.1) y.1.2 y.2).mono (by omega)

/-- Drawing the verifier's randomizers makes no signing queries. -/
theorem tableZs_sign (p : M → Bool) (items : List (AItem n X M)) (is : List ℕ)
    (c : (AnnSpec n H X M).QueryCache) :
    ((is.mapM fun i => if i = 0 then pure 1 else red <$> tableRO (items.take (i + 1)) :
      StateT (AnnSpec n H X M).QueryCache (OracleComp (unifSpec + SignSpec n X M)) _).run
        c).IsQueryBoundP (fun t => isSignQuery p t) 0 := by
  induction is generalizing c with
  | nil => simp
  | cons i is ih =>
    rw [List.mapM_cons]
    simp only [StateT.run_bind, StateT.run_pure]
    refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun y _ =>
      isQueryBoundP_bind (n := 0) (m := 0) (ih y.2) fun _ _ => isQueryBoundP_pure _ _ _
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · rw [StateT.run_map, tableRO_run, isQueryBoundP_map_iff]
      exact lift_sign_zero p _

theorem reduction_sign_bound [NonceGen n M] [Inhabited M] (F : AlgForger n H E X M) (p : M → Bool)
    (q : ℕ)
    (h : ∀ input, (F.main input).IsQueryBoundP (fun r => isSign p r.value.data) q) (pk : X) :
    ((reduction C challenge red F).main pk).IsQueryBoundP (fun t => isSignQuery p t) q := by
  rw [red_main_eq]
  refine (isQueryBoundP_bind (n := q) (m := 0)
    (red_stack_sign C challenge p pk _ q (h _) Core.init ∅) fun y _ =>
      isQueryBoundP_bind (n := 0) (m := 0) ?_ fun _ _ => isQueryBoundP_pure _ _ _).mono
        (by omega)
  exact tableZs_sign p _ _ y.2

end Halfagg.Security
