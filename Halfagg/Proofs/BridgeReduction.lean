import Halfagg.Proofs.Natural
import Halfagg.Proofs.Bridges

/-!
# Bridge B: the reduction's BIP340 game is the annotated experiment plus extraction

`red_advantage_eq`: the reduction's advantage in VCVio's BIP340 EUF-CMA game equals
the probability that the annotated experiment's extraction succeeds. Both are
rewritten to the joint experiment `jExp` in `ProbComp`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security Halfagg.LoggedRun

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)

/-- The joint handler: bookkeeping with real signatures and the lazily sampled
annotated oracle, in `StateT cache ProbComp`. It is `annImpl` under `romImpl`. -/
noncomputable def jImpl (pk : X) (sk : ZMod n) :
    QueryImpl (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n X M))
      (StateT (Core n X M) (StateT (AnnSpec n X M).QueryCache ProbComp)) :=
  coreImpl C challenge pk
    (fun k => simulateQ (AnnSpec n X M).romImpl
      (liftM ((unifSpec + AnnSpec n X M).query (.inl k))))
    (fun l => simulateQ (AnnSpec n X M).romImpl
      (liftM ((unifSpec + AnnSpec n X M).query (.inr l))))
    (fun msg => simulateQ (AnnSpec n X M).romImpl
      ((bip340 (M := M) C challenge (OracleComp (unifSpec + AnnSpec n X M))).sign pk sk msg))

/-- The reduction's handler. -/
noncomputable def redImpl (pk : X) :
    QueryImpl (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n X M))
      (StateT (Core n X M) (StateT (AnnSpec n X M).QueryCache
        (OracleComp (unifSpec + SignSpec n X M)))) :=
  coreImpl (E := E) C challenge pk (fun k => liftM (unifSpec.query k)) tableRO
    (fun msg => liftM ((SignSpec n X M).query msg))

/-- The BIP340 game's oracles for the reduction, with the signing log kept as a
list of signed messages. -/
noncomputable def appImpl (pk : X) (sk : ZMod n) :
    QueryImpl (unifSpec + SignSpec n X M) (StateT (List M) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget (StateT (List M) ProbComp) +
    QueryImpl.appendInputLog ((bip340 (M := M) C challenge ProbComp).sign pk sk)

/-! ## Components of the reduction's run inside the BIP340 game -/

theorem app_unif (pk : X) (sk : ZMod n) (k : ℕ) (l : List M) :
    (simulateQ (appImpl C challenge pk sk)
      (liftM (unifSpec.query k) : OracleComp (unifSpec + SignSpec n X M) _)).run l =
      (fun u => (u, l)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
  unfold appImpl
  rw [QueryImpl.simulateQ_add_liftM_query_left]
  simp

theorem app_lift (pk : X) (sk : ZMod n) {α : Type} (x : ProbComp α) (l : List M) :
    (simulateQ (appImpl C challenge pk sk)
      (liftM x : OracleComp (unifSpec + SignSpec n X M) α)).run l = (fun a => (a, l)) <$> x := by
  unfold appImpl
  rw [QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget, HasQuery.toQueryImpl_eq_id',
    simulateQ_id']
  simp

theorem app_sign (pk : X) (sk : ZMod n) (msg : M) (l : List M) :
    (simulateQ (appImpl C challenge pk sk)
      (liftM ((SignSpec n X M).query msg) : OracleComp (unifSpec + SignSpec n X M) _)).run l =
      (fun sig => (sig, l ++ [msg])) <$> (bip340 (M := M) C challenge ProbComp).sign pk sk msg := by
  unfold appImpl
  rw [QueryImpl.simulateQ_add_liftM_query_right, QueryImpl.run_appendInputLog_apply]
  simp [map_eq_bind_pure_comp]

/-! ## Components of the joint handler -/

theorem rom_unif (k : ℕ) (c : (AnnSpec n X M).QueryCache) :
    (simulateQ (AnnSpec n X M).romImpl
      (liftM ((unifSpec + AnnSpec n X M).query (.inl k)))).run c =
      (fun u => (u, c)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
  simpa using roSim.run_apply_inl (hashSpec := AnnSpec n X M) (AnnSpec n X M).randomOracle k c

theorem rom_ro (l : List (AItem n X M)) (c : (AnnSpec n X M).QueryCache) :
    (simulateQ (AnnSpec n X M).romImpl
      (liftM ((unifSpec + AnnSpec n X M).query (.inr l)))).run c =
      ((AnnSpec n X M).randomOracle l).run c := by
  simp

theorem rom_sign (pk : X) (sk : ZMod n) (msg : M) (c : (AnnSpec n X M).QueryCache) :
    (simulateQ (AnnSpec n X M).romImpl
      ((bip340 (M := M) C challenge (OracleComp (unifSpec + AnnSpec n X M))).sign pk sk
        msg)).run c =
      (fun sig => (sig, c)) <$> (bip340 (M := M) C challenge ProbComp).sign pk sk msg := by
  simp only [bip340]
  rw [show ∀ (x : ProbComp (X × ZMod n)), (monadLift x : OracleComp (unifSpec + AnnSpec n X M) _) =
    liftM x from fun _ => rfl, OracleSpec.simulateQ_romImpl_liftM_run]
  rfl

/-! ## One request -/

theorem tableRO_run (K : List (AItem n X M)) (c : (AnnSpec n X M).QueryCache) :
    (tableRO K).run c =
      (liftM (((AnnSpec n X M).randomOracle K).run c) :
        OracleComp (unifSpec + SignSpec n X M) _) := rfl

theorem lift_unif_run (k : ℕ) (c : (AnnSpec n X M).QueryCache) :
    (liftM (unifSpec.query k) :
        StateT (AnnSpec n X M).QueryCache (OracleComp (unifSpec + SignSpec n X M)) _).run c =
      (fun u => (u, c)) <$>
        (liftM (unifSpec.query k) : OracleComp (unifSpec + SignSpec n X M) _) := by
  rw [map_eq_bind_pure_comp]; rfl

theorem lift_sign_run (msg : M) (c : (AnnSpec n X M).QueryCache) :
    (liftM ((SignSpec n X M).query msg) :
        StateT (AnnSpec n X M).QueryCache (OracleComp (unifSpec + SignSpec n X M)) _).run c =
      (fun u => (u, c)) <$>
        (liftM ((SignSpec n X M).query msg) : OracleComp (unifSpec + SignSpec n X M) _) := by
  rw [map_eq_bind_pure_comp]; rfl

theorem unifFwd_run (k : ℕ) (c : (AnnSpec n X M).QueryCache) :
    (unifFwdImpl (AnnSpec n X M) k).run c =
      (fun u => (u, c)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
  simpa using roSim.run_apply_inl (hashSpec := AnnSpec n X M) (AnnSpec n X M).randomOracle k c

theorem red_step (pk : X) (sk : ZMod n)
    (t : Explained (ZMod n) (Request X M) (Pts E)) (st : Core n X M)
    (c : (AnnSpec n X M).QueryCache) :
    (simulateQ (appImpl C challenge pk sk) (((redImpl C challenge pk t).run st).run c)).run
        st.signed =
      (fun y => (y, y.1.2.signed)) <$> ((jImpl C challenge pk sk t).run st).run c := by
  obtain ⟨⟨data, groups⟩, coeffs⟩ := t
  cases data with
  | random k =>
    unfold redImpl jImpl
    rw [coreImpl_run_random, coreImpl_run_random]
    simp [lift_unif_run, app_unif, unifFwd_run]
  | rand ms tail =>
    unfold redImpl jImpl
    rw [coreImpl_run_rand, coreImpl_run_rand]
    simp [StateT.run_bind, tableRO_run, app_lift, memoize_signed]
  | sign msg =>
    unfold redImpl jImpl
    rw [coreImpl_run_sign, coreImpl_run_sign]
    simp [lift_sign_run, app_sign, rom_sign]

/-! ## The forger's run -/

/-- The reduction's run of the forger inside the BIP340 game, with the signing
log as state, is the joint run; the log ends as the bookkeeping's `signed`. -/
theorem red_stack (pk : X) (sk : ZMod n) {Result : Type}
    (prog : OracleComp (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n X M)) Result)
    (st : Core n X M) (c : (AnnSpec n X M).QueryCache) :
    (simulateQ (appImpl C challenge pk sk)
        (((simulateQ (redImpl C challenge pk) prog).run st).run c)).run st.signed =
      (fun y => (y, y.1.2.signed)) <$>
        ((simulateQ (jImpl C challenge pk sk) prog).run st).run c := by
  induction prog using OracleComp.inductionOn generalizing st c with
  | pure x => simp
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [red_step]
    simp only [bind_map_left, map_bind]
    exact bind_congr fun y => ih y.1.1 y.1.2 y.2

/-! ## The verifier's randomizers -/

/-- The verifier's randomizer from the lazily sampled annotated oracle. -/
noncomputable def jZ (items : List (AItem n X M)) (i : ℕ) :
    StateT (AnnSpec n X M).QueryCache ProbComp (ZMod n) :=
  if i = 0 then pure 1 else (AnnSpec n X M).randomOracle (items.take (i + 1))

theorem zs_ann (items : List (AItem n X M)) (is : List ℕ) :
    simulateQ (AnnSpec n X M).romImpl (is.mapM (zQueryAnn items)) = is.mapM (jZ items) := by
  induction is with
  | nil => simp
  | cons i is ih =>
    rw [List.mapM_cons, List.mapM_cons]
    simp only [simulateQ_bind, simulateQ_pure, ih]
    congr 1
    unfold zQueryAnn jZ
    split_ifs <;> simp

theorem zs_red (pk : X) (sk : ZMod n) (items : List (AItem n X M)) (is : List ℕ)
    (c : (AnnSpec n X M).QueryCache) (l : List M) :
    (simulateQ (appImpl C challenge pk sk)
        ((is.mapM fun i => if i = 0 then pure 1 else tableRO (items.take (i + 1))).run c)).run l =
      (fun y => (y, l)) <$> (is.mapM (jZ items)).run c := by
  induction is generalizing c with
  | nil => simp
  | cons i is ih =>
    rw [List.mapM_cons, List.mapM_cons]
    simp only [StateT.run_bind, simulateQ_bind, StateT.run_pure, simulateQ_pure, map_bind]
    have hstep : (simulateQ (appImpl C challenge pk sk)
        ((if i = 0 then pure 1 else tableRO (items.take (i + 1)) :
          StateT (AnnSpec n X M).QueryCache (OracleComp (unifSpec + SignSpec n X M)) (ZMod n)).run
            c)).run l = (fun y => (y, l)) <$> (jZ items i).run c := by
      unfold jZ
      split_ifs
      · simp
      · rw [tableRO_run, app_lift]
    rw [hstep, bind_map_left]
    refine bind_congr fun y => ?_
    rw [ih, bind_map_left]
    simp

/-! ## The joint experiment -/

/-- The annotated experiment written out in `ProbComp`, with the lazily sampled
oracle's cache threaded explicitly. -/
noncomputable def jExp (F : AlgForger n E X M) : ProbComp (Transcript n X M) := do
  let ks ← (bip340 (M := M) C challenge ProbComp).keygen
  let p ← ((simulateQ (jImpl C challenge ks.1 ks.2)
    (F.main (initial C ((C.liftX ks.1).getD 0)))).run Core.init).run ∅
  let q ← ((List.range (finalItems C p.1.1 p.1.2).length).mapM
    (jZ (finalItems C p.1.1 p.1.2))).run p.2
  return (ks.1, finalItems C p.1.1 p.1.2, p.1.1.value.data.s, q.1, p.1.2.signed)

theorem rom_keygen (c : (AnnSpec n X M).QueryCache) :
    (simulateQ (AnnSpec n X M).romImpl
      (bip340 (M := M) C challenge (OracleComp (unifSpec + AnnSpec n X M))).keygen).run c =
      (fun ks => (ks, c)) <$> (bip340 (M := M) C challenge ProbComp).keygen := by
  simp only [bip340]
  rw [show ∀ (x : ProbComp (X × ZMod n)), (monadLift x : OracleComp (unifSpec + AnnSpec n X M) _) =
    liftM x from fun _ => rfl, OracleSpec.simulateQ_romImpl_liftM_run]
  rfl

theorem rom_annImpl (pk : X) (sk : ZMod n) {Result : Type}
    (prog : OracleComp (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n X M)) Result)
    (st : Core n X M) :
    simulateQ (AnnSpec n X M).romImpl ((simulateQ (annImpl C challenge pk sk) prog).run st) =
      (simulateQ (jImpl C challenge pk sk) prog).run st :=
  coreImpl_natural C challenge (fun x => simulateQ (AnnSpec n X M).romImpl x)
    (fun a => simulateQ_pure _ a) (fun x f => simulateQ_bind _ x f) pk _ _ _ prog st

theorem annROM_eq (F : AlgForger n E X M) : annROM C challenge F = jExp C challenge F := by
  unfold annROM annExperiment annPhase1 jExp
  simp only [simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind, StateT.run_pure,
    rom_keygen, rom_annImpl, zs_ann, map_bind, bind_map_left, bind_assoc, pure_bind, map_pure]

/-! ## The reduction inside the BIP340 game -/

theorem red_main_eq [Inhabited M] (F : AlgForger n E X M) (pk : X) :
    (reduction C challenge F).main pk = (do
      let p ← ((simulateQ (redImpl C challenge pk)
        (F.main (initial C ((C.liftX pk).getD 0)))).run Core.init).run ∅
      let q ← (tableZs (finalItems C p.1.1 p.1.2)).run p.2
      pure (extractForgery C challenge pk (finalItems C p.1.1 p.1.2) p.1.1.value.data.s q.1
        p.1.2.signed)) := rfl

/-- The signing log of the BIP340 game, kept as the list of signed messages. -/
theorem run_sign_eq (pk : X) (sk : ZMod n) {α : Type}
    (oa : OracleComp (unifSpec + SignSpec n X M) α) :
    (fun z => (z.1, z.2.map (fun e => e.1))) <$>
        (bip340 (M := M) C challenge ProbComp).runWithSigningOracle pk sk oa =
      (simulateQ (appImpl C challenge pk sk) oa).run [] := by
  simpa [SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle, appImpl,
    HasQuery.toQueryImpl_eq_id'] using
    QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog (spec₀ := unifSpec)
      (loggedSpec := SignSpec n X M) (m₀ := ProbComp)
      ((bip340 (M := M) C challenge ProbComp).sign pk sk) oa []

/-- The reduction's run in the BIP340 game is the joint run followed by extraction. -/
theorem red_run_eq [Inhabited M] (F : AlgForger n E X M) (pk : X) (sk : ZMod n) :
    (simulateQ (appImpl C challenge pk sk) ((reduction C challenge F).main pk)).run [] = (do
      let p ← ((simulateQ (jImpl C challenge pk sk)
        (F.main (initial C ((C.liftX pk).getD 0)))).run Core.init).run ∅
      let q ← ((List.range (finalItems C p.1.1 p.1.2).length).mapM
        (jZ (finalItems C p.1.1 p.1.2))).run p.2
      pure (extractForgery C challenge pk (finalItems C p.1.1 p.1.2) p.1.1.value.data.s q.1
        p.1.2.signed, p.1.2.signed)) := by
  have h := red_stack C challenge pk sk (F.main (initial C ((C.liftX pk).getD 0)))
    (Core.init : Core n X M) ∅
  rw [show (Core.init : Core n X M).signed = [] from rfl] at h
  rw [red_main_eq]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [h, bind_map_left]
  refine bind_congr fun p => ?_
  unfold tableZs
  rw [zs_red, bind_map_left]

/-- The outcome of the BIP340 game as a function of the transcript. -/
def gameOK [Inhabited M] (t : Transcript n X M) : Bool :=
  !decide ((extractForgery C challenge t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2).1 ∈ t.2.2.2.2) &&
    BIP340.verify C challenge t.1
      (extractForgery C challenge t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2).1
      (extractForgery C challenge t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2).2

theorem gameOK_iff [Inhabited M] (t : Transcript n X M) :
    gameOK C challenge t = true ↔ extractOK C challenge t := by
  simp [gameOK, extractOK, and_comm]

/-- **The BIP340 game of the reduction is the joint experiment followed by
extraction.** -/
theorem red_experiment_eq [Inhabited M] (F : AlgForger n E X M) :
    SignatureAlg.unforgeableExperiment (reduction C challenge F) =
      gameOK C challenge <$> jExp C challenge F := by
  have hexp : SignatureAlg.unforgeableExperiment (reduction C challenge F) = (do
      let ks ← (bip340 (M := M) C challenge ProbComp).keygen
      let z ← (bip340 (M := M) C challenge ProbComp).runWithSigningOracle ks.1 ks.2
        ((reduction C challenge F).main ks.1)
      let v ← (bip340 (M := M) C challenge ProbComp).verify ks.1 z.1.1 z.1.2
      pure (!z.2.wasQueried z.1.1 && v)) := by
    unfold SignatureAlg.unforgeableExperiment
    refine bind_congr fun ks => ?_
    obtain ⟨pk, sk⟩ := ks
    refine bind_congr fun z => ?_
    obtain ⟨⟨msg, σ⟩, log⟩ := z
    refine bind_congr fun v => ?_
    simp only [QueryLog.wasQueried_eq_decide_mem_map_fst]
    congr!
  have key : ∀ pk sk, (do
      let z ← (bip340 (M := M) C challenge ProbComp).runWithSigningOracle pk sk
        ((reduction C challenge F).main pk)
      let v ← (bip340 (M := M) C challenge ProbComp).verify pk z.1.1 z.1.2
      pure (!z.2.wasQueried z.1.1 && v)) = (do
      let w ← (simulateQ (appImpl C challenge pk sk) ((reduction C challenge F).main pk)).run []
      pure (!decide (w.1.1 ∈ w.2) && BIP340.verify C challenge pk w.1.1 w.1.2)) := by
    intro pk sk
    rw [← run_sign_eq, bind_map_left]
    refine bind_congr fun z => ?_
    simp [bip340, QueryLog.wasQueried_eq_decide_mem_map_fst]
  rw [hexp]
  unfold jExp
  simp only [key, red_run_eq, map_bind, bind_assoc, pure_bind, map_pure]
  rfl

/-- **Bridge B.** The annotated experiment's extraction succeeds exactly as often
as the reduction wins the BIP340 game. -/
theorem red_advantage_eq [Inhabited M] (F : AlgForger n E X M) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (reduction C challenge F) =
      Pr{let t ← annROM C challenge F}[extractOK C challenge t] := by
  unfold SignatureAlg.unforgeableAdvantage
  rw [ProbCompRuntime.probComp_evalDist, ← prEvent_eq_evalDist_singleton, red_experiment_eq,
    prEvent_map, annROM_eq]
  exact prEvent_congr_of_support _ _ _ fun t _ => gameOK_iff C challenge t

theorem bridge_reduction [Inhabited M] (F : AlgForger n E X M) :
    Pr{let t ← annROM C challenge F}[extractOK C challenge t] ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (reduction C challenge F) :=
  (red_advantage_eq C challenge F).ge

end Halfagg.Security
