import Halfagg.Proofs.BridgeReduction
import Halfagg.Proofs.Projection

/-!
# Bridge A: the standard game against the annotated experiment

`bridge_game`: the standard game with the erased forger wins exactly as often as
the annotated experiment's transcript wins. The game's plain random-oracle cache
is the projection (`plainOf`) of the annotated cache through the recorded
representations.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)

/-! ## The game's oracles, with the signing log as state -/

/-- The game's oracles for the adversary, with the signing log kept as the list
of signed messages. Uniform sampling and the randomizer hash pass through. -/
noncomputable def gApp (pk : X) (sk : ZMod n) :
    QueryImpl (GameSpec n X M) (StateT (List M) (OracleComp (unifSpec + RandSpec n X M))) :=
  (HasQuery.toQueryImpl (spec := unifSpec + RandSpec n X M)
      (m := OracleComp (unifSpec + RandSpec n X M))).liftTarget
      (StateT (List M) (OracleComp (unifSpec + RandSpec n X M))) +
    QueryImpl.appendInputLog
      ((bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec n X M))).sign pk sk)

theorem run_sign_eq_game (pk : X) (sk : ZMod n) {α : Type}
    (oa : OracleComp (GameSpec n X M) α) :
    (fun z => (z.1, z.2.map (fun e => e.1))) <$>
        (bip340 (M := M) C challenge
          (OracleComp (unifSpec + RandSpec n X M))).runWithSigningOracle pk sk oa =
      (simulateQ (gApp C challenge pk sk) oa).run [] := by
  simpa [SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle, gApp,
    HasQuery.toQueryImpl_eq_id'] using
    QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog
      (spec₀ := unifSpec + RandSpec n X M) (loggedSpec := SignSpec n X M)
      (m₀ := OracleComp (unifSpec + RandSpec n X M))
      ((bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec n X M))).sign pk sk) oa []

/-- A request of the game's adversary, run with the lazily sampled plain oracle. -/
noncomputable def gRun (pk : X) (sk : ZMod n) {α : Type} (oa : OracleComp (GameSpec n X M) α)
    (l : List M) (c : (RandSpec n X M).QueryCache) :
    ProbComp ((α × List M) × (RandSpec n X M).QueryCache) :=
  (simulateQ (RandSpec n X M).romImpl ((simulateQ (gApp C challenge pk sk) oa).run l)).run c

theorem gRun_pure (pk : X) (sk : ZMod n) {α : Type} (a : α) (l : List M)
    (c : (RandSpec n X M).QueryCache) :
    gRun C challenge pk sk (pure a) l c = pure ((a, l), c) := by
  simp [gRun]

theorem gRun_bind (pk : X) (sk : ZMod n) {α β : Type} (oa : OracleComp (GameSpec n X M) α)
    (f : α → OracleComp (GameSpec n X M) β) (l : List M) (c : (RandSpec n X M).QueryCache) :
    gRun C challenge pk sk (oa >>= f) l c =
      gRun C challenge pk sk oa l c >>= fun y => gRun C challenge pk sk (f y.1.1) y.1.2 y.2 := by
  simp [gRun, StateT.run_bind]

theorem unifFwd_runR (k : ℕ) (c : (RandSpec n X M).QueryCache) :
    (unifFwdImpl (RandSpec n X M) k).run c =
      (fun u => (u, c)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
  simpa using roSim.run_apply_inl (hashSpec := RandSpec n X M) (RandSpec n X M).randomOracle k c

theorem rom_signR (pk : X) (sk : ZMod n) (msg : M) (c : (RandSpec n X M).QueryCache) :
    (simulateQ (RandSpec n X M).romImpl
      ((bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec n X M))).sign pk sk
        msg)).run c =
      (fun sig => (sig, c)) <$> (bip340 (M := M) C challenge ProbComp).sign pk sk msg := by
  simp only [bip340]
  rw [show ∀ (x : ProbComp (X × ZMod n)), (monadLift x : OracleComp (unifSpec + RandSpec n X M) _) =
    liftM x from fun _ => rfl, OracleSpec.simulateQ_romImpl_liftM_run]
  rfl

theorem rom_keygenR (c : (RandSpec n X M).QueryCache) :
    (simulateQ (RandSpec n X M).romImpl
      (bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec n X M))).keygen).run c =
      (fun ks => (ks, c)) <$> (bip340 (M := M) C challenge ProbComp).keygen := by
  simp only [bip340]
  rw [show ∀ (x : ProbComp (X × ZMod n)), (monadLift x : OracleComp (unifSpec + RandSpec n X M) _) =
    liftM x from fun _ => rfl, OracleSpec.simulateQ_romImpl_liftM_run]
  rfl

theorem gRun_unif (pk : X) (sk : ZMod n) (k : ℕ) (l : List M)
    (c : (RandSpec n X M).QueryCache) :
    gRun C challenge pk sk (liftM ((GameSpec n X M).query (.inl (.inl k)))) l c =
      (fun u => ((u, l), c)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
  unfold gRun gApp
  simp [unifFwd_runR, rom_signR]

theorem gRun_rand (pk : X) (sk : ZMod n) (L : List (Item X M)) (l : List M)
    (c : (RandSpec n X M).QueryCache) :
    gRun C challenge pk sk (liftM ((GameSpec n X M).query (.inl (.inr L)))) l c =
      (fun p => ((p.1, l), p.2)) <$> ((RandSpec n X M).randomOracle L).run c := by
  unfold gRun gApp
  simp [unifFwd_runR, rom_signR]

theorem gRun_sign (pk : X) (sk : ZMod n) (msg : M) (l : List M)
    (c : (RandSpec n X M).QueryCache) :
    gRun C challenge pk sk (liftM ((GameSpec n X M).query (.inr msg))) l c =
      (fun sig => ((sig, l ++ [msg]), c)) <$>
        (bip340 (M := M) C challenge ProbComp).sign pk sk msg := by
  unfold gRun gApp
  simp [unifFwd_runR, rom_signR]

/-! ## One request, on each side -/

section Step

variable (pk : X) (sk : ZMod n) (groups : Groups (Pts E))
  (coeffs : Unit → List (List (ZMod n))) (st : Core n X M)

theorem g_random (k : ℕ) (l : List M) (c : (RandSpec n X M).QueryCache) :
    gRun C challenge pk sk (eraseImpl C (n := n) (M := M) ⟨.random k, groups⟩) l c =
      (fun u => ((⟨u, fun _ => []⟩, l), c)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
  rw [show eraseImpl C (n := n) (M := M) ⟨.random k, groups⟩ = (do
    let u ← (liftM ((GameSpec n X M).query (.inl (.inl k))) : OracleComp (GameSpec n X M) _)
    pure ⟨u, fun _ => []⟩) from rfl, gRun_bind, gRun_unif]
  simp [gRun_pure]

theorem g_rand (ms : List M) (l : List M) (c : (RandSpec n X M).QueryCache) :
    gRun C challenge pk sk (eraseImpl C (n := n) (M := M) ⟨.rand ms, groups⟩) l c =
      (fun p => ((⟨p.1, fun _ => []⟩, l), p.2)) <$>
        ((RandSpec n X M).randomOracle (toItems C ms (groups ()))).run c := by
  rw [show eraseImpl C (n := n) (M := M) ⟨.rand ms, groups⟩ = (do
    let z ← (liftM ((GameSpec n X M).query (.inl (.inr (toItems C ms (groups ()))))) :
      OracleComp (GameSpec n X M) _)
    pure ⟨z, fun _ => []⟩) from rfl, gRun_bind, gRun_rand]
  simp [gRun_pure]

theorem g_sign (msg : M) (l : List M) (c : (RandSpec n X M).QueryCache) :
    gRun C challenge pk sk (eraseImpl C (n := n) (M := M) ⟨.sign msg, groups⟩) l c =
      (fun sig => ((⟨sig.2, fun _ => [(C.liftX sig.1).getD 0]⟩, l ++ [msg]), c)) <$>
        (bip340 (M := M) C challenge ProbComp).sign pk sk msg := by
  rw [show eraseImpl C (n := n) (M := M) ⟨.sign msg, groups⟩ = (do
    let sig ← (liftM ((GameSpec n X M).query (.inr msg)) : OracleComp (GameSpec n X M) _)
    pure ⟨sig.2, fun _ => [(C.liftX sig.1).getD 0]⟩) from rfl, gRun_bind, gRun_sign]
  simp [gRun_pure]

theorem j_random (k : ℕ) (cA : (AnnSpec n X M).QueryCache) :
    ((jImpl C challenge pk sk ⟨⟨.random k, groups⟩, coeffs⟩).run st).run cA =
      (fun u => ((⟨u, fun _ => []⟩, st), cA)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
  unfold jImpl
  rw [coreImpl_run_random]
  simp [unifFwd_run]

theorem j_rand (ms : List M) (cA : (AnnSpec n X M).QueryCache) :
    ((jImpl C challenge pk sk ⟨⟨.rand ms, groups⟩, coeffs⟩).run st).run cA =
      (fun p => ((⟨p.1, fun _ => []⟩, memoize C st (groups ()) (coeffs ())), p.2)) <$>
        ((AnnSpec n X M).randomOracle (annotate (memoize C st (groups ()) (coeffs ())).memo
          (toItems C ms (groups ())))).run cA := by
  unfold jImpl
  rw [coreImpl_run_rand]
  simp

theorem j_sign (msg : M) (cA : (AnnSpec n X M).QueryCache) :
    ((jImpl C challenge pk sk ⟨⟨.sign msg, groups⟩, coeffs⟩).run st).run cA =
      (fun sig => ((⟨sig.2, fun _ => [(C.liftX sig.1).getD 0]⟩,
        { st with basis := st.basis ++ [(sig.2, -challenge sig.1 pk msg)]
                  signed := st.signed ++ [msg] }), cA)) <$>
        (bip340 (M := M) C challenge ProbComp).sign pk sk msg := by
  unfold jImpl
  rw [coreImpl_run_sign]
  simp [rom_sign]

end Step

theorem memoExt_memoize (st : Core n X M) (pts : List E) (coeffs : List (List (ZMod n))) :
    MemoExt st.memo (memoize C st pts coeffs).memo :=
  fun _ _ h => memoizeList_of_some C _ _ _ h

theorem covered_memoize (st : Core n X M) (ms : List M) (pts : List E)
    (coeffs : List (List (ZMod n))) :
    covered (memoize C st pts coeffs).memo (toItems C ms pts) := by
  intro it hit
  obtain ⟨R, hR, P, hP, h1, h2⟩ := toItems_mem C hit
  rw [h1, h2]
  exact ⟨memoizeList_isSome C _ _ _ _ hR, memoizeList_isSome C _ _ _ _ hP⟩

/-- **One request**: the game's run projects from the joint handler's. -/
theorem game_step (pk : X) (sk : ZMod n) (t : Explained (ZMod n) (Request M) (Pts E))
    (st : Core n X M) (cA : (AnnSpec n X M).QueryCache) (hinv : CacheInv st.memo cA) :
    gRun C challenge pk sk (eraseImpl C t.value) st.signed (plainOf st.memo cA) =
      (fun y => ((y.1.1, y.1.2.signed), plainOf y.1.2.memo y.2)) <$>
        ((jImpl C challenge pk sk t).run st).run cA := by
  obtain ⟨⟨data, groups⟩, coeffs⟩ := t
  cases data with
  | random k => rw [g_random, j_random]; simp
  | rand ms =>
    rw [g_rand, j_rand,
      ← plainOf_ext hinv (memoExt_memoize C st (groups ()) (coeffs ())),
      ro_step cA (covered_memoize C st ms (groups ()) (coeffs ()))]
    simp [memoize_signed]
  | sign msg => rw [g_sign, j_sign]; simp

/-- The joint handler keeps the cache invariant. -/
theorem game_step_inv (pk : X) (sk : ZMod n) (t : Explained (ZMod n) (Request M) (Pts E))
    (st : Core n X M) (cA : (AnnSpec n X M).QueryCache) (hinv : CacheInv st.memo cA) :
    ∀ y ∈ support (((jImpl C challenge pk sk t).run st).run cA),
      CacheInv y.1.2.memo y.2 := by
  obtain ⟨⟨data, groups⟩, coeffs⟩ := t
  intro y hy
  cases data with
  | random k =>
    rw [j_random, support_map] at hy
    obtain ⟨u, -, rfl⟩ := hy
    exact hinv
  | rand ms =>
    rw [j_rand, support_map] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    exact ro_step_inv (cacheInv_ext hinv (memoExt_memoize C st (groups ()) (coeffs ())))
      (covered_memoize C st ms (groups ()) (coeffs ())) p hp
  | sign msg =>
    rw [j_sign, support_map] at hy
    obtain ⟨sig, -, rfl⟩ := hy
    exact hinv

/-! ## The forger's run -/

theorem game_stack (pk : X) (sk : ZMod n) {Result : Type}
    (prog : OracleComp (explainedSpec (ZMod n) (Pts E) (Request M) (Reply n M)) Result)
    (st : Core n X M) (cA : (AnnSpec n X M).QueryCache) (hinv : CacheInv st.memo cA) :
    gRun C challenge pk sk (simulateQ (fun q => eraseImpl C q.value) prog) st.signed
        (plainOf st.memo cA) =
      (fun y => ((y.1.1, y.1.2.signed), plainOf y.1.2.memo y.2)) <$>
        ((simulateQ (jImpl C challenge pk sk) prog).run st).run cA := by
  induction prog using OracleComp.inductionOn generalizing st cA with
  | pure x => simp [gRun_pure]
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [gRun_bind, game_step C challenge pk sk t st cA hinv, bind_map_left, map_bind]
    refine bind_congr_of_forall_mem_support _ fun y hy => ?_
    exact ih y.1.1 y.1.2 y.2 (game_step_inv C challenge pk sk t st cA hinv y hy)

theorem j_stack_inv (pk : X) (sk : ZMod n) {Result : Type}
    (prog : OracleComp (explainedSpec (ZMod n) (Pts E) (Request M) (Reply n M)) Result)
    (st : Core n X M) (cA : (AnnSpec n X M).QueryCache) (hinv : CacheInv st.memo cA) :
    ∀ y ∈ support (((simulateQ (jImpl C challenge pk sk) prog).run st).run cA),
      CacheInv y.1.2.memo y.2 := by
  induction prog using OracleComp.inductionOn generalizing st cA with
  | pure x =>
    intro y hy
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact hinv
  | query_bind t next ih =>
    intro y hy
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨y₁, hy₁, hy⟩ := hy
    exact ih y₁.1.1 y₁.1.2 y₁.2 (game_step_inv C challenge pk sk t st cA hinv y₁ hy₁) y hy

/-! ## The verifier's randomizers -/

theorem zq_game (memo : X → Option (Rep n)) (its : List (Item X M))
    (hcov : covered memo its) (i : ℕ) (cA : (AnnSpec n X M).QueryCache)
    (hinv : CacheInv memo cA) :
    (simulateQ (RandSpec n X M).romImpl (zQuery (n := n) its i)).run (plainOf memo cA) =
        (fun y => (y.1, plainOf memo y.2)) <$> (jZ (annotate memo its) i).run cA ∧
      ∀ y ∈ support ((jZ (annotate memo its) i).run cA), CacheInv memo y.2 := by
  unfold zQuery jZ
  split_ifs with hi
  · refine ⟨by simp, fun y hy => ?_⟩
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact hinv
  · have hc : covered memo (its.take (i + 1)) := fun it hit => hcov it (List.mem_of_mem_take hit)
    have ht : (annotate memo its).take (i + 1) = annotate memo (its.take (i + 1)) := by
      simp [annotate, List.map_take]
    rw [ht]
    refine ⟨?_, ro_step_inv hinv hc⟩
    rw [← ro_step cA hc]
    simp

theorem game_zs (memo : X → Option (Rep n)) (its : List (Item X M))
    (hcov : covered memo its) (is : List ℕ) (cA : (AnnSpec n X M).QueryCache)
    (hinv : CacheInv memo cA) :
    (simulateQ (RandSpec n X M).romImpl (is.mapM (zQuery (n := n) its))).run (plainOf memo cA) =
      (fun y => (y.1, plainOf memo y.2)) <$> (is.mapM (jZ (annotate memo its))).run cA := by
  induction is generalizing cA with
  | nil => simp
  | cons i is ih =>
    obtain ⟨hstep, hstepinv⟩ := zq_game memo its hcov i cA hinv
    rw [List.mapM_cons, List.mapM_cons]
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind]
    rw [hstep, bind_map_left]
    refine bind_congr_of_forall_mem_support _ fun y hy => ?_
    rw [ih y.2 (hstepinv y hy), bind_map_left]
    simp

/-! ## Assembly -/

theorem gRun_map (pk : X) (sk : ZMod n) {α β : Type} (f : α → β)
    (oa : OracleComp (GameSpec n X M) α) (l : List M) (c : (RandSpec n X M).QueryCache) :
    gRun C challenge pk sk (f <$> oa) l c =
      (fun y => ((f y.1.1, y.1.2), y.2)) <$> gRun C challenge pk sk oa l c := by
  simp [gRun]

/-- The game after key generation, as the joint run followed by the win check. -/
theorem game_run_eq (F : AlgForger n E M) (pk : X) (sk : ZMod n) :
    (do
      let w ← gRun C challenge pk sk ((erase C F).main pk) [] ∅
      let zs ← (simulateQ (RandSpec n X M).romImpl
        ((List.range w.1.1.1.length).mapM (zQuery (n := n) w.1.1.1))).run w.2
      pure (aggWins C challenge pk w.1.1.1 w.1.1.2 zs.1 (fun m => w.1.2.contains m))) = (do
      let p ← ((simulateQ (jImpl C challenge pk sk)
        (F.main (initial C ((C.liftX pk).getD 0)))).run Core.init).run ∅
      let q ← ((List.range (finalItems C p.1.1 p.1.2).length).mapM
        (jZ (finalItems C p.1.1 p.1.2))).run p.2
      pure (aggWins C challenge pk ((finalItems C p.1.1 p.1.2).map strip) p.1.1.value.data.s q.1
        (fun m => p.1.2.signed.contains m))) := by
  have hstack := game_stack C challenge pk sk (F.main (initial C ((C.liftX pk).getD 0)))
    (Core.init : Core n X M) ∅ (cacheInv_empty _)
  rw [show (Core.init : Core n X M).signed = [] from rfl, plainOf_empty] at hstack
  simp only [erase]
  rw [gRun_map, hstack]
  simp only [bind_map_left, Functor.map_map]
  refine bind_congr_of_forall_mem_support _ fun p hp => ?_
  have hinv := j_stack_inv C challenge pk sk _ _ _ (cacheInv_empty _) p hp
  have hext := memoExt_memoize C p.1.2 (p.1.1.value.groups ()) (p.1.1.coefficients ())
  rw [← plainOf_ext hinv hext,
    game_zs _ _ (covered_memoize C p.1.2 p.1.1.value.data.ms (p.1.1.value.groups ())
      (p.1.1.coefficients ())) _ p.2 (cacheInv_ext hinv hext), bind_map_left]
  simp [finalItems, annotate, strip, Function.comp_def]

/-- The outcome of the game as a function of the transcript. -/
def winB (t : Transcript n X M) : Bool :=
  aggWins C challenge t.1 (t.2.1.map strip) t.2.2.1 t.2.2.2.1 (fun m => t.2.2.2.2.contains m)

/-- **The standard game with the erased forger is the joint experiment followed
by the win check.** -/
theorem game_experiment_eq (F : AlgForger n E M) :
    (simulateQ (RandSpec n X M).romImpl (aggExperiment C challenge (erase C F))).run' ∅ =
      winB C challenge <$> jExp C challenge F := by
  have hexp : aggExperiment C challenge (erase C F) = (do
      let ks ← (bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec n X M))).keygen
      let z ← (bip340 (M := M) C challenge
        (OracleComp (unifSpec + RandSpec n X M))).runWithSigningOracle ks.1 ks.2
          ((erase C F).main ks.1)
      let zs ← (List.range z.1.1.length).mapM (zQuery z.1.1)
      pure (aggWins C challenge ks.1 z.1.1 z.1.2 zs z.2.wasQueried)) := rfl
  have key : ∀ pk sk, (do
      let z ← (bip340 (M := M) C challenge
        (OracleComp (unifSpec + RandSpec n X M))).runWithSigningOracle pk sk ((erase C F).main pk)
      let zs ← (List.range z.1.1.length).mapM (zQuery (n := n) z.1.1)
      pure (aggWins C challenge pk z.1.1 z.1.2 zs z.2.wasQueried)) = (do
      let w ← (simulateQ (gApp C challenge pk sk) ((erase C F).main pk)).run []
      let zs ← (List.range w.1.1.length).mapM (zQuery (n := n) w.1.1)
      pure (aggWins C challenge pk w.1.1 w.1.2 zs (fun m => w.2.contains m))) := by
    intro pk sk
    rw [← run_sign_eq_game, bind_map_left]
    refine bind_congr fun z => bind_congr fun zs => ?_
    have hw : z.2.wasQueried = fun m => (List.map (fun e => e.1) z.2).contains m := by
      funext m
      simp [QueryLog.wasQueried_eq_decide_mem_map_fst]
    rw [hw]
  rw [hexp]
  unfold jExp
  simp only [key, simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind,
    StateT.run_pure, rom_keygenR, map_bind, bind_map_left, map_pure]
  refine bind_congr fun ks => ?_
  have h := game_run_eq C challenge F ks.1 ks.2
  simp only [gRun] at h
  simpa [winB] using h

/-- **Bridge A.** The standard game with the erased forger wins exactly as often
as the annotated experiment's transcript wins. -/
theorem bridge_game (F : AlgForger n E M) :
    aggAdvantage C challenge (erase C F) ≤
      Pr{let t ← annROM C challenge F}[winT C challenge t] := by
  unfold aggAdvantage
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton, game_experiment_eq,
    prEvent_map, annROM_eq]
  exact le_of_eq rfl

end Halfagg.Security
