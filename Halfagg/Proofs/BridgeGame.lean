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

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)
variable [SampleableType H] {red : H → ZMod n}

/-! ## The game's oracles, with the signing log as state -/

/-- The game's oracles for the adversary, with the signing log kept as the list
of signed messages. Uniform sampling and the randomizer hash pass through. -/
noncomputable def gApp (pk : X) (sk : ZMod n) :
    QueryImpl (GameSpec n H X M) (StateT (List M) (OracleComp (unifSpec + RandSpec H X M))) :=
  (HasQuery.toQueryImpl (spec := unifSpec + RandSpec H X M)
      (m := OracleComp (unifSpec + RandSpec H X M))).liftTarget
      (StateT (List M) (OracleComp (unifSpec + RandSpec H X M))) +
    QueryImpl.appendInputLog
      ((bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec H X M))).sign pk sk)

theorem run_sign_eq_game (pk : X) (sk : ZMod n) {α : Type}
    (oa : OracleComp (GameSpec n H X M) α) :
    (fun z => (z.1, z.2.map (fun e => e.1))) <$>
        (bip340 (M := M) C challenge
          (OracleComp (unifSpec + RandSpec H X M))).runWithSigningOracle pk sk oa =
      (simulateQ (gApp C challenge pk sk) oa).run [] := by
  simpa [SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle, gApp,
    HasQuery.toQueryImpl_eq_id'] using
    QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog
      (spec₀ := unifSpec + RandSpec H X M) (loggedSpec := SignSpec n X M)
      (m₀ := OracleComp (unifSpec + RandSpec H X M))
      ((bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec H X M))).sign pk sk) oa []

/-- A request of the game's adversary, run with the lazily sampled plain oracle. -/
noncomputable def gRun (pk : X) (sk : ZMod n) {α : Type} (oa : OracleComp (GameSpec n H X M) α)
    (l : List M) (c : (RandSpec H X M).QueryCache) :
    ProbComp ((α × List M) × (RandSpec H X M).QueryCache) :=
  (simulateQ (RandSpec H X M).romImpl ((simulateQ (gApp C challenge pk sk) oa).run l)).run c

theorem gRun_pure (pk : X) (sk : ZMod n) {α : Type} (a : α) (l : List M)
    (c : (RandSpec H X M).QueryCache) :
    gRun C challenge pk sk (pure a) l c = pure ((a, l), c) := by
  simp [gRun]

theorem gRun_bind (pk : X) (sk : ZMod n) {α β : Type} (oa : OracleComp (GameSpec n H X M) α)
    (f : α → OracleComp (GameSpec n H X M) β) (l : List M) (c : (RandSpec H X M).QueryCache) :
    gRun C challenge pk sk (oa >>= f) l c =
      gRun C challenge pk sk oa l c >>= fun y => gRun C challenge pk sk (f y.1.1) y.1.2 y.2 := by
  simp [gRun, StateT.run_bind]

theorem unifFwd_runR (k : ℕ) (c : (RandSpec H X M).QueryCache) :
    (unifFwdImpl (RandSpec H X M) k).run c =
      (fun u => (u, c)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
  simpa using roSim.run_apply_inl (hashSpec := RandSpec H X M) (RandSpec H X M).randomOracle k c

theorem rom_signR (pk : X) (sk : ZMod n) (msg : M) (c : (RandSpec H X M).QueryCache) :
    (simulateQ (RandSpec H X M).romImpl
      ((bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec H X M))).sign pk sk
        msg)).run c =
      (fun sig => (sig, c)) <$> (bip340 (M := M) C challenge ProbComp).sign pk sk msg := by
  simp only [bip340]
  rw [show ∀ (x : ProbComp (X × ZMod n)), (monadLift x : OracleComp (unifSpec + RandSpec H X M) _) =
    liftM x from fun _ => rfl, OracleSpec.simulateQ_romImpl_liftM_run]
  rfl

theorem rom_keygenR (c : (RandSpec H X M).QueryCache) :
    (simulateQ (RandSpec H X M).romImpl
      (bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec H X M))).keygen).run c =
      (fun ks => (ks, c)) <$> (bip340 (M := M) C challenge ProbComp).keygen := by
  simp only [bip340]
  rw [show ∀ (x : ProbComp (X × ZMod n)), (monadLift x : OracleComp (unifSpec + RandSpec H X M) _) =
    liftM x from fun _ => rfl, OracleSpec.simulateQ_romImpl_liftM_run]
  rfl

theorem gRun_unif (pk : X) (sk : ZMod n) (k : ℕ) (l : List M)
    (c : (RandSpec H X M).QueryCache) :
    gRun C challenge pk sk (liftM ((GameSpec n H X M).query (.inl (.inl k)))) l c =
      (fun u => ((u, l), c)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
  unfold gRun gApp
  simp [unifFwd_runR]

theorem gRun_rand (pk : X) (sk : ZMod n) (L : List (Item X M)) (l : List M)
    (c : (RandSpec H X M).QueryCache) :
    gRun C challenge pk sk (liftM ((GameSpec n H X M).query (.inl (.inr L)))) l c =
      (fun p => ((p.1, l), p.2)) <$> ((RandSpec H X M).randomOracle L).run c := by
  unfold gRun gApp
  simp

theorem gRun_sign (pk : X) (sk : ZMod n) (msg : M) (l : List M)
    (c : (RandSpec H X M).QueryCache) :
    gRun C challenge pk sk (liftM ((GameSpec n H X M).query (.inr msg))) l c =
      (fun sig => ((sig, l ++ [msg]), c)) <$>
        (bip340 (M := M) C challenge ProbComp).sign pk sk msg := by
  unfold gRun gApp
  simp [rom_signR]

/-! ## One request, on each side -/

section Step

variable (pk : X) (sk : ZMod n) (groups : Groups (Pts E))
  (coeffs : Unit → List (List (ZMod n))) (st : Core n X M)

theorem g_random (k : ℕ) (l : List M) (c : (RandSpec H X M).QueryCache) :
    gRun C challenge pk sk (eraseImpl C (n := n) (M := M) ⟨.random k, groups⟩) l c =
      (fun u => ((⟨u, fun _ => []⟩, l), c)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
  rw [show eraseImpl C (n := n) (M := M) ⟨.random k, groups⟩ = (do
    let u ← (liftM ((GameSpec n H X M).query (.inl (.inl k))) : OracleComp (GameSpec n H X M) _)
    pure ⟨u, fun _ => []⟩) from rfl, gRun_bind, gRun_unif]
  simp [gRun_pure]

theorem g_rand (ms : List M) (tail : List (Item X M)) (l : List M)
    (c : (RandSpec H X M).QueryCache) :
    gRun C challenge pk sk (eraseImpl C (n := n) (M := M) ⟨.rand ms tail, groups⟩) l c =
      (fun p => ((⟨p.1, fun _ => []⟩, l), p.2)) <$>
        ((RandSpec H X M).randomOracle (toItems C ms (groups ()) ++ rawTail C tail)).run c := by
  rw [show eraseImpl C (n := n) (M := M) ⟨.rand ms tail, groups⟩ = (do
    let z ← (liftM ((GameSpec n H X M).query
      (.inl (.inr (toItems C ms (groups ()) ++ rawTail C tail)))) :
      OracleComp (GameSpec n H X M) _)
    pure ⟨z, fun _ => []⟩) from rfl, gRun_bind, gRun_rand]
  simp [gRun_pure]

theorem g_sign (msg : M) (l : List M) (c : (RandSpec H X M).QueryCache) :
    gRun C challenge pk sk (eraseImpl C (n := n) (M := M) ⟨.sign msg, groups⟩) l c =
      (fun sig => ((⟨sig.2, fun _ => [(C.liftX sig.1).getD 0]⟩, l ++ [msg]), c)) <$>
        (bip340 (M := M) C challenge ProbComp).sign pk sk msg := by
  rw [show eraseImpl C (n := n) (M := M) ⟨.sign msg, groups⟩ = (do
    let sig ← (liftM ((GameSpec n H X M).query (.inr msg)) : OracleComp (GameSpec n H X M) _)
    pure ⟨sig.2, fun _ => [(C.liftX sig.1).getD 0]⟩) from rfl, gRun_bind, gRun_sign]
  simp [gRun_pure]

theorem j_random (k : ℕ) (cA : (AnnSpec n H X M).QueryCache) :
    ((jImpl (H := H) C challenge pk sk ⟨⟨.random k, groups⟩, coeffs⟩).run st).run cA =
      (fun u => ((⟨u, fun _ => []⟩, st), cA)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
  unfold jImpl
  rw [coreImpl_run_random]
  simp [unifFwd_run]

theorem j_rand (ms : List M) (tail : List (Item X M)) (cA : (AnnSpec n H X M).QueryCache) :
    ((jImpl (H := H) C challenge pk sk ⟨⟨.rand ms tail, groups⟩, coeffs⟩).run st).run cA =
      (fun p => ((⟨p.1, fun _ => []⟩, memoize C st (groups ()) (coeffs ())), p.2)) <$>
        ((AnnSpec n H X M).randomOracle (annotate C (memoize C st (groups ()) (coeffs ())).memo
          (toItems C ms (groups ()) ++ rawTail C tail))).run cA := by
  unfold jImpl
  rw [coreImpl_run_rand]
  simp

theorem j_sign (msg : M) (cA : (AnnSpec n H X M).QueryCache) :
    ((jImpl (H := H) C challenge pk sk ⟨⟨.sign msg, groups⟩, coeffs⟩).run st).run cA =
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
    (coeffs : List (List (ZMod n))) (tail : List (Item X M)) :
    covered C (memoize C st pts coeffs).memo (toItems C ms pts ++ rawTail C tail) := by
  refine covered_append C (fun it hit => ?_) (covered_rawTail C _ tail)
  obtain ⟨R, hR, P, hP, h1, h2⟩ := toItems_mem C hit
  rw [h1, h2]
  exact ⟨memoizeList_isSome C _ _ _ _ hR, memoizeList_isSome C _ _ _ _ hP⟩

theorem covered_memoize_nil (st : Core n X M) (ms : List M) (pts : List E)
    (coeffs : List (List (ZMod n))) :
    covered C (memoize C st pts coeffs).memo (toItems C ms pts) := by
  simpa [rawTail] using covered_memoize C st ms pts coeffs []

/-- **One request**: the game's run projects from the joint handler's. -/
theorem game_step (pk : X) (sk : ZMod n) (t : Explained (ZMod n) (Request X M) (Pts E))
    (st : Core n X M) (cA : (AnnSpec n H X M).QueryCache) (hinv : CacheInv C st.memo cA) :
    gRun C challenge pk sk (eraseImpl C t.value) st.signed (plainOf C st.memo cA) =
      (fun y => ((y.1.1, y.1.2.signed), plainOf C y.1.2.memo y.2)) <$>
        ((jImpl (H := H) C challenge pk sk t).run st).run cA := by
  obtain ⟨⟨data, groups⟩, coeffs⟩ := t
  cases data with
  | random k => rw [g_random, j_random]; simp
  | rand ms tail =>
    rw [g_rand, j_rand,
      ← plainOf_ext C hinv (memoExt_memoize C st (groups ()) (coeffs ())),
      ro_step C cA (covered_memoize C st ms (groups ()) (coeffs ()) tail)]
    simp [memoize_signed]
  | sign msg => rw [g_sign, j_sign]; simp

/-- The joint handler keeps the cache invariant. -/
theorem game_step_inv (pk : X) (sk : ZMod n) (t : Explained (ZMod n) (Request X M) (Pts E))
    (st : Core n X M) (cA : (AnnSpec n H X M).QueryCache) (hinv : CacheInv C st.memo cA) :
    ∀ y ∈ support (((jImpl (H := H) C challenge pk sk t).run st).run cA),
      CacheInv C y.1.2.memo y.2 := by
  obtain ⟨⟨data, groups⟩, coeffs⟩ := t
  intro y hy
  cases data with
  | random k =>
    rw [j_random, support_map] at hy
    obtain ⟨u, -, rfl⟩ := hy
    exact hinv
  | rand ms tail =>
    rw [j_rand, support_map] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    exact ro_step_inv C (cacheInv_ext C hinv (memoExt_memoize C st (groups ()) (coeffs ())))
      (covered_memoize C st ms (groups ()) (coeffs ()) tail) p hp
  | sign msg =>
    rw [j_sign, support_map] at hy
    obtain ⟨sig, -, rfl⟩ := hy
    exact hinv

/-! ## The forger's run -/

theorem game_stack (pk : X) (sk : ZMod n) {Result : Type}
    (prog : OracleComp (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)) Result)
    (st : Core n X M) (cA : (AnnSpec n H X M).QueryCache) (hinv : CacheInv C st.memo cA) :
    gRun C challenge pk sk (simulateQ (fun q => eraseImpl C q.value) prog) st.signed
        (plainOf C st.memo cA) =
      (fun y => ((y.1.1, y.1.2.signed), plainOf C y.1.2.memo y.2)) <$>
        ((simulateQ (jImpl (H := H) C challenge pk sk) prog).run st).run cA := by
  induction prog using OracleComp.inductionOn generalizing st cA with
  | pure x => simp [gRun_pure]
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [gRun_bind, game_step C challenge pk sk t st cA hinv, bind_map_left, map_bind]
    refine bind_congr_of_forall_mem_support _ fun y hy => ?_
    exact ih y.1.1 y.1.2 y.2 (game_step_inv C challenge pk sk t st cA hinv y hy)

theorem j_stack_inv (pk : X) (sk : ZMod n) {Result : Type}
    (prog : OracleComp (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)) Result)
    (st : Core n X M) (cA : (AnnSpec n H X M).QueryCache) (hinv : CacheInv C st.memo cA) :
    ∀ y ∈ support (((simulateQ (jImpl (H := H) C challenge pk sk) prog).run st).run cA),
      CacheInv C y.1.2.memo y.2 := by
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
    (hcov : covered C memo its) (i : ℕ) (cA : (AnnSpec n H X M).QueryCache)
    (hinv : CacheInv C memo cA) :
    (simulateQ (RandSpec H X M).romImpl (zQuery red (n := n) its i)).run (plainOf C memo cA) =
        (fun y => (y.1, plainOf C memo y.2)) <$> (jZ red (annotate C memo its) i).run cA ∧
      ∀ y ∈ support ((jZ red (annotate C memo its) i).run cA), CacheInv C memo y.2 := by
  unfold zQuery jZ
  split_ifs with hi
  · refine ⟨by simp, fun y hy => ?_⟩
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact hinv
  · have hc : covered C memo (its.take (i + 1)) := covered_take C hcov _
    rw [annotate_take]
    refine ⟨?_, fun y hy => ?_⟩
    · have hq : (simulateQ (RandSpec H X M).romImpl
          (HasQuery.query (spec := RandSpec H X M) (its.take (i + 1)) :
            OracleComp (unifSpec + RandSpec H X M) H)).run (plainOf C memo cA) =
          ((RandSpec H X M).randomOracle (its.take (i + 1))).run (plainOf C memo cA) := by
        simp
      simp only [simulateQ_map, StateT.run_map, hq, ro_step C cA hc, Functor.map_map]
    · rw [StateT.run_map, support_map] at hy
      obtain ⟨p, hp, rfl⟩ := hy
      exact ro_step_inv C hinv hc p hp

theorem game_zs (memo : X → Option (Rep n)) (its : List (Item X M))
    (hcov : covered C memo its) (is : List ℕ) (cA : (AnnSpec n H X M).QueryCache)
    (hinv : CacheInv C memo cA) :
    (simulateQ (RandSpec H X M).romImpl (is.mapM (zQuery red (n := n) its))).run
        (plainOf C memo cA) =
      (fun y => (y.1, plainOf C memo y.2)) <$> (is.mapM (jZ red (annotate C memo its))).run cA := by
  induction is generalizing cA with
  | nil => simp
  | cons i is ih =>
    obtain ⟨hstep, hstepinv⟩ := zq_game C memo its hcov i cA hinv
    rw [List.mapM_cons, List.mapM_cons]
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind]
    rw [hstep, bind_map_left]
    refine bind_congr_of_forall_mem_support _ fun y hy => ?_
    rw [ih y.2 (hstepinv y hy), bind_map_left]
    simp

/-! ## Assembly -/

theorem gRun_map (pk : X) (sk : ZMod n) {α β : Type} (f : α → β)
    (oa : OracleComp (GameSpec n H X M) α) (l : List M) (c : (RandSpec H X M).QueryCache) :
    gRun C challenge pk sk (f <$> oa) l c =
      (fun y => ((f y.1.1, y.1.2), y.2)) <$> gRun C challenge pk sk oa l c := by
  simp [gRun]

/-- The game after key generation, as the joint run followed by any check `f` of
the key, the items, `s`, the randomizers and the signed messages. -/
theorem game_run_eq {β : Type}
    (f : X → List (Item X M) → ZMod n → List (ZMod n) → List M → β)
    (F : AlgForger n H E X M) (pk : X) (sk : ZMod n) :
    (do
      let w ← gRun C challenge pk sk ((erase C F).main pk) [] ∅
      let zs ← (simulateQ (RandSpec H X M).romImpl
        ((List.range w.1.1.1.length).mapM (zQuery red (n := n) w.1.1.1))).run w.2
      pure (f pk w.1.1.1 w.1.1.2 zs.1 w.1.2)) = (do
      let p ← ((simulateQ (jImpl (H := H) C challenge pk sk)
        (F.main (initial C ((C.liftX pk).getD 0)))).run Core.init).run ∅
      let q ← ((List.range (finalItems C p.1.1 p.1.2).length).mapM
        (jZ red (finalItems C p.1.1 p.1.2))).run p.2
      pure (f pk ((finalItems C p.1.1 p.1.2).map strip) p.1.1.value.data.s q.1
        p.1.2.signed)) := by
  have hstack := game_stack C challenge pk sk (F.main (initial C ((C.liftX pk).getD 0)))
    (Core.init : Core n X M) ∅ (cacheInv_empty C _)
  rw [show (Core.init : Core n X M).signed = [] from rfl, plainOf_empty] at hstack
  simp only [erase]
  rw [gRun_map, hstack]
  simp only [bind_map_left, Functor.map_map]
  refine bind_congr_of_forall_mem_support _ fun p hp => ?_
  have hinv := j_stack_inv C challenge pk sk _ _ _ (cacheInv_empty C _) p hp
  have hext := memoExt_memoize C p.1.2 (p.1.1.value.groups ()) (p.1.1.coefficients ())
  rw [← plainOf_ext C hinv hext,
    game_zs C _ _ (covered_memoize_nil C p.1.2 p.1.1.value.data.ms (p.1.1.value.groups ())
      (p.1.1.coefficients ())) _ p.2 (cacheInv_ext C hinv hext), bind_map_left]
  simp [finalItems, map_strip_annotate, annotate_length]

/-- The outcome of the game as a function of the transcript. -/
def winB (t : Transcript n X M) : Bool :=
  aggWins C challenge t.1 (t.2.1.map strip) t.2.2.1 t.2.2.2.1 (fun m => t.2.2.2.2.contains m)

/-- **The standard game with the erased forger is the joint experiment followed
by the win check.** -/
theorem game_experiment_eq (F : AlgForger n H E X M) :
    (simulateQ (RandSpec H X M).romImpl (aggExperiment C challenge red (erase C F))).run' ∅ =
      winB C challenge <$> jExp C challenge red F := by
  have hexp : aggExperiment C challenge red (erase C F) = (do
      let ks ← (bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec H X M))).keygen
      let z ← (bip340 (M := M) C challenge
        (OracleComp (unifSpec + RandSpec H X M))).runWithSigningOracle ks.1 ks.2
          ((erase C F).main ks.1)
      let zs ← (List.range z.1.1.length).mapM (zQuery red z.1.1)
      pure (aggWins C challenge ks.1 z.1.1 z.1.2 zs z.2.wasQueried)) := rfl
  have key : ∀ pk sk, (do
      let z ← (bip340 (M := M) C challenge
        (OracleComp (unifSpec + RandSpec H X M))).runWithSigningOracle pk sk ((erase C F).main pk)
      let zs ← (List.range z.1.1.length).mapM (zQuery red (n := n) z.1.1)
      pure (aggWins C challenge pk z.1.1 z.1.2 zs z.2.wasQueried)) = (do
      let w ← (simulateQ (gApp C challenge pk sk) ((erase C F).main pk)).run []
      let zs ← (List.range w.1.1.length).mapM (zQuery red (n := n) w.1.1)
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
  have h := game_run_eq C challenge (red := red)
    (fun pk its s zs l => aggWins C challenge pk its s zs (fun m => l.contains m)) F ks.1 ks.2
  simp only [gRun] at h
  simpa [winB] using h

/-- **Bridge A.** The standard game with the erased forger wins exactly as often
as the annotated experiment's transcript wins. -/
theorem bridge_game (F : AlgForger n H E X M) :
    aggAdvantage C challenge red (erase C F) ≤
      Pr{let t ← annROM C challenge red F}[winT C challenge t] := by
  unfold aggAdvantage
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton, game_experiment_eq,
    prEvent_map, annROM_eq]
  exact le_of_eq rfl

end Halfagg.Security
