import Halfagg.SecurityROM
import Halfagg.Proofs.Eager
import Halfagg.Proofs.BridgeGame

/-!
# The oracle reduction against a fixed challenge table

With every challenge-hash query answered from a table `g`, VCVio's Fiat-Shamir
BIP340 game for `reductionROM F` is the BIP340 game of `Halfagg/Security.lean`
with the challenge function `hOf g` for `reduction (hOf g) (F.at g)`
(`rom_experiment_eq`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security Halfagg.LoggedRun

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (g : M × (X × X) → ZMod n)
variable [SampleableType H] {red : H → ZMod n}

/-! ## The Fiat-Shamir scheme with its hash answered from the table -/

theorem table_lift {α : Type} (x : ProbComp α) :
    simulateQ (tableImpl g) (liftM x : OracleComp (unifSpec + ChalSpec n X M) α) = x := by
  unfold tableImpl
  rw [QueryImpl.simulateQ_add_liftM_left, HasQuery.toQueryImpl_eq_id', simulateQ_id']

theorem table_hash (key : M × (X × X)) :
    simulateQ (tableImpl g)
      (liftM ((unifSpec + ChalSpec n X M).query (.inr key))) = pure (g key) := by
  simp [tableImpl]
  rfl

theorem table_hasQuery (key : M × (X × X)) :
    simulateQ (tableImpl g) (HasQuery.query (spec := ChalSpec n X M) key :
      OracleComp (unifSpec + ChalSpec n X M) (ZMod n)) = pure (g key) :=
  table_hash g key

theorem table_monadLift {α : Type} (x : ProbComp α) :
    simulateQ (tableImpl g) (monadLift x : OracleComp (unifSpec + ChalSpec n X M) α) = x :=
  table_lift g x

theorem fs_keygen :
    simulateQ (tableImpl g) (FiatShamir.inROM (sigma C) (keyGen C) M).keygen =
      (keyGen C).gen := by
  simp only [FiatShamir]
  exact table_lift g _

theorem fs_sign (P : Stmt C) (w : ZMod n) (msg : M) :
    simulateQ (tableImpl g) ((FiatShamir.inROM (sigma C) (keyGen C) M).sign P w msg) = (do
      let k ← $ᵗ (NonzeroScalar n)
      pure ((C.x (C.mulG k.1), C.x P.1),
        C.evenScalar k.1 + g (msg, (C.x (C.mulG k.1), C.x P.1)) * w)) := by
  simp only [FiatShamir, sigma, simulateQ_bind, simulateQ_pure, table_monadLift, table_hasQuery,
    bind_assoc, pure_bind]

theorem fs_verify (P : Stmt C) (msg : M) (σ : FSSig n X) :
    simulateQ (tableImpl g) ((FiatShamir.inROM (sigma C) (keyGen C) M).verify P msg σ) =
      pure ((sigma C).verify P σ.1 (g (msg, σ.1)) σ.2) := by
  simp only [FiatShamir, simulateQ_bind, simulateQ_pure, table_hasQuery, pure_bind]

/-! ## The Fiat-Shamir game's oracles, with the signing log as state -/

/-- The oracles of the Fiat-Shamir game for its adversary, with the signing log
kept as the list of signed messages. -/
noncomputable def appFS (P : Stmt C) (w : ZMod n) :
    QueryImpl (RomSpec n X M) (StateT (List M) (OracleComp (unifSpec + ChalSpec n X M))) :=
  (HasQuery.toQueryImpl (spec := unifSpec + ChalSpec n X M)
      (m := OracleComp (unifSpec + ChalSpec n X M))).liftTarget
      (StateT (List M) (OracleComp (unifSpec + ChalSpec n X M))) +
    QueryImpl.appendInputLog ((FiatShamir.inROM (sigma C) (keyGen C) M).sign P w)

theorem run_sign_eq_fs (P : Stmt C) (w : ZMod n) {α : Type}
    (oa : OracleComp (RomSpec n X M) α) :
    (fun z => (z.1, z.2.map (fun e => e.1))) <$>
        (FiatShamir.inROM (sigma C) (keyGen C) M).runWithSigningOracle P w oa =
      (simulateQ (appFS C P w) oa).run [] := by
  simpa [SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle, appFS,
    HasQuery.toQueryImpl_eq_id'] using
    QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog
      (spec₀ := unifSpec + ChalSpec n X M) (loggedSpec := M →ₒ FSSig n X)
      (m₀ := OracleComp (unifSpec + ChalSpec n X M))
      ((FiatShamir.inROM (sigma C) (keyGen C) M).sign P w) oa []

/-- A Fiat-Shamir signature with the challenge from the table. -/
noncomputable def signG (P : Stmt C) (w : ZMod n) (msg : M) : ProbComp (FSSig n X) := do
  let k ← $ᵗ (NonzeroScalar n)
  pure ((C.x (C.mulG k.1), C.x P.1),
    C.evenScalar k.1 + g (msg, (C.x (C.mulG k.1), C.x P.1)) * w)

/-- The game's oracles with the hash answered from the table. -/
noncomputable def fsImpl (P : Stmt C) (w : ZMod n) :
    QueryImpl (RomSpec n X M) (StateT (List M) ProbComp) :=
  (tableImpl g).liftTarget (StateT (List M) ProbComp) +
    QueryImpl.appendInputLog (signG C g P w)

theorem fsImpl_inl (P : Stmt C) (w : ZMod n) (t : ℕ ⊕ (M × (X × X))) (l : List M) :
    (fsImpl C g P w (.inl t)).run l = (fun u => (u, l)) <$> tableImpl g t := by
  simp [fsImpl]

theorem fsImpl_inr (P : Stmt C) (w : ZMod n) (msg : M) (l : List M) :
    (fsImpl C g P w (.inr msg)).run l = (fun sig => (sig, l ++ [msg])) <$> signG C g P w msg := by
  simp [fsImpl, map_eq_bind_pure_comp]

theorem appFS_inl (P : Stmt C) (w : ZMod n) (t : ℕ ⊕ (M × (X × X))) (l : List M) :
    (appFS C P w (.inl t)).run l =
      (fun u => (u, l)) <$> (liftM ((unifSpec + ChalSpec n X M).query t) :
        OracleComp (unifSpec + ChalSpec n X M) _) := by
  simp [appFS, HasQuery.toQueryImpl_eq_id']

theorem appFS_inr (P : Stmt C) (w : ZMod n) (msg : M) (l : List M) :
    (appFS C P w (.inr msg)).run l =
      (fun sig => (sig, l ++ [msg])) <$>
        (FiatShamir.inROM (sigma C) (keyGen C) M).sign P w msg := by
  simp [appFS, map_eq_bind_pure_comp]

/-- The game's run of an adversary with the hash answered from the table. -/
theorem fs_stack (P : Stmt C) (w : ZMod n) {α : Type} (oa : OracleComp (RomSpec n X M) α)
    (l : List M) :
    simulateQ (tableImpl g) ((simulateQ (appFS C P w) oa).run l) =
      (simulateQ (fsImpl C g P w) oa).run l := by
  induction oa using OracleComp.inductionOn generalizing l with
  | pure x => simp
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with t | msg
    · rw [appFS_inl, fsImpl_inl]
      simp only [bind_map_left, simulateQ_spec_query, simulateQ_map, ih]
    · rw [appFS_inr, fsImpl_inr]
      simp only [bind_map_left, simulateQ_map, fs_sign, ih, signG]

/-! ## Components of the reduction under the game's oracles -/

section Components

variable (P : Stmt C) (w : ZMod n)

theorem fs_hashQ (key : M × (X × X)) (l : List M) :
    (simulateQ (fsImpl C g P w) (hashQ (n := n) key)).run l = pure (g key, l) := by
  unfold hashQ
  rw [simulateQ_spec_query, fsImpl_inl, tableImpl_inr]
  simp

theorem fs_unif (k : ℕ) (l : List M) :
    (simulateQ (fsImpl C g P w)
      (liftM ((RomSpec n X M).query (.inl (.inl k))))).run l =
      (fun u => (u, l)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
  rw [simulateQ_spec_query, fsImpl_inl]
  rfl

theorem fs_signQ (msg : M) (l : List M) :
    (simulateQ (fsImpl C g P w) (liftM ((RomSpec n X M).query (.inr msg)))).run l =
      (fun sig => (sig, l ++ [msg])) <$> signG C g P w msg := by
  rw [simulateQ_spec_query, fsImpl_inr]

theorem fs_lift {α : Type} (x : ProbComp α) (l : List M) :
    (simulateQ (fsImpl C g P w) (liftM x : OracleComp (RomSpec n X M) α)).run l =
      (fun a => (a, l)) <$> x := by
  induction x using OracleComp.inductionOn generalizing l with
  | pure a => simp
  | query_bind k next ih =>
    have hq : (simulateQ (fsImpl C g P w)
        (liftM (unifSpec.query k) : OracleComp (RomSpec n X M) _)).run l =
        (fun u => (u, l)) <$> (liftM (unifSpec.query k) : ProbComp _) := fs_unif C g P w k l
    have hb : (liftM (liftM (unifSpec.query k) >>= next) : OracleComp (RomSpec n X M) α) =
        (liftM (unifSpec.query k) : OracleComp (RomSpec n X M) _) >>= fun u => liftM (next u) := by
      simp
      rfl
    rw [hb]
    simp only [simulateQ_bind, StateT.run_bind]
    rw [hq, bind_map_left, map_bind]
    exact bind_congr fun u => ih u l

end Components

/-! ## One oracle call of the forger -/

section Step

variable {d : ZMod n} (hd : d ≠ 0)

/-- The Fiat-Shamir public key of the secret key `d`. -/
def keyOf (d : ZMod n) : Stmt C := ⟨C.mulG (C.evenScalar d), C.evenScalar d, rfl⟩

include hd in
/-- BIP340 signing with the challenge function `hOf g` is Fiat-Shamir signing with
the hash answered from `g`, without the public key in the signature. -/
theorem sign_eq (msg : M) :
    (bip340 (M := M) C (hOf g) ProbComp).sign (C.x (C.mulG d)) d msg =
      (fun σ : FSSig n X => (σ.1.1, σ.2)) <$> signG C g (keyOf C d) (C.evenScalar d) msg := by
  simp only [bip340, signG, keyOf, map_bind, map_pure]
  refine bind_congr fun k => ?_
  simp [BIP340.sign, hd, k.2, hOf, C.x_evenScalar]

theorem rom_chal (pk : X) (key : M × (X × X)) (st : Core n X M)
    (c : (AnnSpec n H X M).QueryCache) (l : List M) :
    (simulateQ (fsImpl C g (keyOf C d) (C.evenScalar d))
      (((romHandler (H := H) (E := E) C pk (.inl key)).run st).run c)).run l =
      pure (((g key, st), c), l) := by
  have h : ((romHandler (H := H) (E := E) C pk (.inl key)).run st).run c =
      (fun e => ((e, st), c)) <$> hashQ (n := n) key := by
    simp [romHandler]
  rw [h, simulateQ_map, StateT.run_map, fs_hashQ]
  simp

section Runs

variable (pk : X) (groups : Groups (Pts E)) (coeffs : Unit → List (List (ZMod n)))
  (st : Core n X M) (c : (AnnSpec n H X M).QueryCache)

theorem rom_run_random (k : ℕ) :
    ((romHandler (H := H) C pk (.inr ⟨⟨.random k, groups⟩, coeffs⟩)).run st).run c =
      ((liftM ((RomSpec n X M).query (.inl (.inl k))) : OracleComp (RomSpec n X M) _) >>=
        fun u => pure ((⟨u, fun _ => []⟩, st), c)) := rfl

theorem rom_run_rand (ms : List M) (tail : List (Item X M)) :
    ((romHandler (H := H) C pk (.inr ⟨⟨.rand ms tail, groups⟩, coeffs⟩)).run st).run c =
      ((liftM (((AnnSpec n H X M).randomOracle
          (annotate C (memoize C st (groups ()) (coeffs ())).memo
            (toItems C ms (groups ()) ++ rawTail C tail))).run c) :
          OracleComp (RomSpec n X M) _) >>=
        fun p => pure ((⟨p.1, fun _ => []⟩, memoize C st (groups ()) (coeffs ())), p.2)) := rfl

theorem rom_run_sign (msg : M) :
    ((romHandler (H := H) C pk (.inr ⟨⟨.sign msg, groups⟩, coeffs⟩)).run st).run c =
      ((liftM ((RomSpec n X M).query (.inr msg)) : OracleComp (RomSpec n X M) _) >>= fun sig =>
        hashQ (n := n) (msg, (sig.1.1, pk)) >>= fun e =>
          pure ((⟨sig.2, fun _ => [(C.liftX sig.1.1).getD 0]⟩,
            { st with basis := st.basis ++ [(sig.2, -e)]
                      signed := st.signed ++ [msg] }), c)) := rfl

end Runs

include hd in
/-- **One request**: the oracle reduction's handling under the game's oracles is
the joint handler's. -/
theorem rom_step (t : Explained (ZMod n) (Request X M) (Pts E)) (st : Core n X M)
    (c : (AnnSpec n H X M).QueryCache) :
    (simulateQ (fsImpl C g (keyOf C d) (C.evenScalar d))
      (((romHandler (H := H) C (C.x (C.mulG d)) (.inr t)).run st).run c)).run st.signed =
      (fun y => (y, y.1.2.signed)) <$>
        ((jImpl (H := H) C (hOf g) (C.x (C.mulG d)) d t).run st).run c := by
  obtain ⟨⟨data, groups⟩, coeffs⟩ := t
  cases data with
  | random k =>
    rw [rom_run_random, j_random]
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
    rw [fs_unif]
    simp
  | rand ms tail =>
    rw [rom_run_rand, j_rand]
    simp [fs_lift, memoize_signed]
  | sign msg =>
    rw [rom_run_sign, j_sign, sign_eq C g hd]
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
    rw [fs_signQ]
    simp [fs_hashQ, hOf, keyOf]

include hd in
/-- **The forger's run**: the oracle reduction's run of the forger under the game's
oracles is the joint run of the forger with its challenge queries answered from
the table. -/
theorem rom_stack {Result : Type} (prog : OracleComp (RomForgerSpec n H E X M) Result)
    (st : Core n X M) (c : (AnnSpec n H X M).QueryCache) :
    (simulateQ (fsImpl C g (keyOf C d) (C.evenScalar d))
        (((simulateQ (romHandler (H := H) C (C.x (C.mulG d))) prog).run st).run c)).run st.signed =
      (fun y => (y, y.1.2.signed)) <$>
        ((simulateQ (jImpl (H := H) C (hOf g) (C.x (C.mulG d)) d)
          (simulateQ (answerChal g) prog)).run st).run c := by
  induction prog using OracleComp.inductionOn generalizing st c with
  | pure x => simp
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with key | t
    · rw [rom_chal]
      simp only [pure_bind, answerChal, ih, simulateQ_pure, StateT.run_pure]
    · rw [rom_step C g hd]
      simp only [answerChal, simulateQ_spec_query, bind_map_left, map_bind]
      exact bind_congr fun y => ih y.1.1 y.1.2 y.2

end Step

/-! ## The final phase -/

section Final

variable (P : Stmt C) (w : ZMod n)

theorem romTableRO_run (K : List (AItem n X M)) (c : (AnnSpec n H X M).QueryCache) :
    (romTableRO K).run c =
      (liftM (((AnnSpec n H X M).randomOracle K).run c) : OracleComp (RomSpec n X M) _) := rfl

theorem zs_rom (items : List (AItem n X M)) (is : List ℕ) (c : (AnnSpec n H X M).QueryCache)
    (l : List M) :
    (simulateQ (fsImpl C g P w)
        ((is.mapM fun i =>
          if i = 0 then pure 1 else red <$> romTableRO (items.take (i + 1))).run c)).run l =
      (fun y => (y, l)) <$> (is.mapM (jZ red items)).run c := by
  induction is generalizing c with
  | nil => simp
  | cons i is ih =>
    rw [List.mapM_cons, List.mapM_cons]
    simp only [StateT.run_bind, simulateQ_bind, StateT.run_pure, simulateQ_pure, map_bind]
    have hstep : (simulateQ (fsImpl C g P w)
        ((if i = 0 then pure 1 else red <$> romTableRO (items.take (i + 1)) :
          StateT (AnnSpec n H X M).QueryCache (OracleComp (RomSpec n X M)) (ZMod n)).run
            c)).run l = (fun y => (y, l)) <$> (jZ red items i).run c := by
      unfold jZ
      split_ifs
      · simp
      · simp only [StateT.run_map, simulateQ_map, romTableRO_run, fs_lift, Functor.map_map]
    rw [hstep, bind_map_left]
    refine bind_congr fun y => ?_
    rw [ih, bind_map_left]
    simp

theorem es_rom (items : List (AItem n X M)) (l : List M) :
    (simulateQ (fsImpl C g P w)
        (items.mapM fun a => hashQ (n := n) (a.m, (a.r, a.pk)))).run l =
      pure (items.map fun a => g (a.m, (a.r, a.pk)), l) := by
  induction items with
  | nil => simp
  | cons a items ih =>
    rw [List.mapM_cons]
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, fs_hashQ,
      pure_bind, ih, List.map_cons]

/-- The known challenges of a list are the table's challenges on its items. -/
theorem knownChal_eq (items : List (AItem n X M)) {a : AItem n X M} (ha : a ∈ items) :
    knownChal items (items.map fun b => g (b.m, (b.r, b.pk))) a.r a.pk a.m =
      hOf g a.r a.pk a.m := by
  unfold knownChal hOf
  induction items with
  | nil => cases ha
  | cons b rest ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.find?_cons]
    by_cases hb : b.r = a.r ∧ b.pk = a.pk ∧ b.m = a.m
    · simp [hb]
    · have hrest : a ∈ rest := by
        rcases List.mem_cons.mp ha with rfl | h
        · exact absurd ⟨rfl, rfl, rfl⟩ hb
        · exact h
      simp [hb]
      simpa using ih hrest

theorem starRep_congr {ch ch' : X → X → M → ZMod n} {a : AItem n X M}
    (h : ch a.r a.pk a.m = ch' a.r a.pk a.m) : starRep ch a = starRep ch' a := by
  simp [starRep, h]

/-- Signing with a constant challenge is signing with the table's challenge at
the one point where signing evaluates it. -/
theorem sign_const (x : ZMod n) (m : M) :
    BIP340.sign C (fun _ _ _ => g (m, (C.x (C.mulG 1), C.x (C.mulG x)))) (fun _ _ _ => 1) x m =
      BIP340.sign C (hOf g) (fun _ _ _ => 1) x m := by
  simp [BIP340.sign, hOf]

/-- A BIP340 forgery as a forgery of the Fiat-Shamir scheme. -/
def toFS (pk : X) (f : M × (X × ZMod n)) : M × FSSig n X := (f.1, ((f.2.1, pk), f.2.2))

/-- The oracle extraction, with the hash answered from the table, is
`extractForgery` for the challenge function `hOf g`. -/
theorem extract_rom [Inhabited M] (pk : X) (items : List (AItem n X M)) (s : ZMod n)
    (zs : List (ZMod n)) (signed : List M) (l : List M) :
    (simulateQ (fsImpl C g P w) (extractROM C pk items s zs signed
      (items.map fun a => g (a.m, (a.r, a.pk))))).run l =
      pure (toFS pk (extractForgery C (hOf g) pk items s zs signed), l) := by
  have hstar : ∀ b ∈ items,
      starRep (knownChal items (items.map fun a => g (a.m, (a.r, a.pk)))) b =
        starRep (hOf g) b := fun b hb => starRep_congr (knownChal_eq g items hb)
  have hα : isum (fun i b => zs.getD i 0 *
      (starRep (knownChal items (items.map fun a => g (a.m, (a.r, a.pk)))) b).1) 0 items =
      isum (fun i b => zs.getD i 0 * (starRep (hOf g) b).1) 0 items :=
    isum_congr fun i b hb _ _ => by rw [hstar b hb]
  have hβ : isum (fun i b => zs.getD i 0 *
      (starRep (knownChal items (items.map fun a => g (a.m, (a.r, a.pk)))) b).2) 0 items =
      isum (fun i b => zs.getD i 0 * (starRep (hOf g) b).2) 0 items :=
    isum_congr fun i b hb _ _ => by rw [hstar b hb]
  unfold extractROM extractForgery
  rcases hfind : items.find? (fun a => a.pk == pk && !signed.contains a.m) with _ | a
  · simp only [hfind]
    simp [toFS]
  · have ha := List.mem_of_find?_eq_some hfind
    simp only [hfind, hstar a ha, hα, hβ]
    split_ifs
    · simp [toFS]
    · simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, fs_hashQ,
        pure_bind, sign_const, toFS]

end Final

/-! ## The reduction's run and the experiment -/

section Experiment

variable {d : ZMod n} (hd : d ≠ 0)

include hd in
/-- The oracle reduction's run in the Fiat-Shamir game, with the hash answered
from the table, is the joint run followed by `extractForgery`. -/
theorem rom_run_eq [Inhabited M] (F : RomForger n H E X M) :
    (simulateQ (fsImpl C g (keyOf C d) (C.evenScalar d))
        ((reductionROM C red F).main (keyOf C d))).run [] = (do
      let p ← ((simulateQ (jImpl (H := H) C (hOf g) (C.x (C.mulG d)) d)
        ((F.at g).main (initial C ((C.liftX (C.x (C.mulG d))).getD 0)))).run Core.init).run ∅
      let q ← ((List.range (finalItems C p.1.1 p.1.2).length).mapM
        (jZ red (finalItems C p.1.1 p.1.2))).run p.2
      pure (toFS (C.x (C.mulG d)) (extractForgery C (hOf g) (C.x (C.mulG d))
        (finalItems C p.1.1 p.1.2) p.1.1.value.data.s q.1 p.1.2.signed), p.1.2.signed)) := by
  have hpk : C.x (keyOf C d).1 = C.x (C.mulG d) := C.x_evenScalar d
  have hstack := rom_stack C g hd (F.main (initial C ((C.liftX (C.x (C.mulG d))).getD 0)))
    (Core.init : Core n X M) ∅
  rw [show (Core.init : Core n X M).signed = [] from rfl] at hstack
  simp only [reductionROM, hpk, simulateQ_bind, StateT.run_bind]
  rw [hstack, bind_map_left]
  refine bind_congr fun p => ?_
  simp only [zs_rom, bind_map_left, es_rom, pure_bind, extract_rom]
  rfl

include hd in
/-- The Fiat-Shamir check of a signature carrying the public key is BIP340
verification with the table's challenge. -/
theorem verify_fs (msg : M) (r : X) (s : ZMod n) :
    (sigma C).verify (keyOf C d) (r, C.x (C.mulG d)) (g (msg, (r, C.x (C.mulG d)))) s =
      BIP340.verify C (hOf g) (C.x (C.mulG d)) msg (r, s) := by
  have h := sigma_verify_eq_verify C (M := M) (C.mulG_ne_zero (C.evenScalar_ne_zero hd))
    (C.hasEvenY_evenScalar hd) ⟨C.evenScalar d, rfl⟩ r (g (msg, (r, C.x (C.mulG d)))) s msg
  rw [C.x_evenScalar] at h
  rw [show keyOf C d = ⟨C.mulG (C.evenScalar d), C.evenScalar d, rfl⟩ from rfl, h]
  rfl

include hd in
/-- The game after key generation with secret key `d`. -/
theorem rom_game_key [Inhabited M] (F : RomForger n H E X M) :
    (do
      let z ← simulateQ (tableImpl g)
        ((FiatShamir.inROM (sigma C) (keyGen C) M).runWithSigningOracle (keyOf C d)
          (C.evenScalar d) ((reductionROM C red F).main (keyOf C d)))
      let v ← simulateQ (tableImpl g)
        ((FiatShamir.inROM (sigma C) (keyGen C) M).verify (keyOf C d) z.1.1 z.1.2)
      pure (!z.2.wasQueried z.1.1 && v)) = (do
      let p ← ((simulateQ (jImpl (H := H) C (hOf g) (C.x (C.mulG d)) d)
        ((F.at g).main (initial C ((C.liftX (C.x (C.mulG d))).getD 0)))).run Core.init).run ∅
      let q ← ((List.range (finalItems C p.1.1 p.1.2).length).mapM
        (jZ red (finalItems C p.1.1 p.1.2))).run p.2
      pure (gameOK C (hOf g) (C.x (C.mulG d), finalItems C p.1.1 p.1.2, p.1.1.value.data.s, q.1,
        p.1.2.signed))) := by
  have hrun := rom_run_eq C g (red := red) hd F
  rw [← fs_stack, ← run_sign_eq_fs, simulateQ_map] at hrun
  have key : (do
      let z ← simulateQ (tableImpl g)
        ((FiatShamir.inROM (sigma C) (keyGen C) M).runWithSigningOracle (keyOf C d)
          (C.evenScalar d) ((reductionROM C red F).main (keyOf C d)))
      let v ← simulateQ (tableImpl g)
        ((FiatShamir.inROM (sigma C) (keyGen C) M).verify (keyOf C d) z.1.1 z.1.2)
      pure (!z.2.wasQueried z.1.1 && v)) = (do
      let w ← (fun z => (z.1, z.2.map (fun e => e.1))) <$> simulateQ (tableImpl g)
        ((FiatShamir.inROM (sigma C) (keyGen C) M).runWithSigningOracle (keyOf C d)
          (C.evenScalar d) ((reductionROM C red F).main (keyOf C d)))
      pure (!decide (w.1.1 ∈ w.2) &&
        (sigma C).verify (keyOf C d) w.1.2.1 (g (w.1.1, w.1.2.1)) w.1.2.2)) := by
    rw [bind_map_left]
    refine bind_congr fun z => ?_
    simp [fs_verify, QueryLog.wasQueried_eq_decide_mem_map_fst]
  rw [key, hrun]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun p => bind_congr fun q => ?_
  simp only [toFS, verify_fs C g hd, gameOK]
  rfl

/-- **The oracle reduction against a fixed table.** With every hash query
answered from `g`, the Fiat-Shamir game of `reductionROM F` is the joint
experiment for the challenge function `hOf g`, followed by extraction. -/
theorem rom_experiment_eq [Inhabited M] (F : RomForger n H E X M) :
    simulateQ (tableImpl g) (SignatureAlg.unforgeableExperiment (reductionROM C red F)) =
      gameOK C (hOf g) <$> jExp C (hOf g) red (F.at g) := by
  have hexp : SignatureAlg.unforgeableExperiment (reductionROM C red F) = (do
      let ks ← (FiatShamir.inROM (sigma C) (keyGen C) M).keygen
      let z ← (FiatShamir.inROM (sigma C) (keyGen C) M).runWithSigningOracle ks.1 ks.2
        ((reductionROM C red F).main ks.1)
      let v ← (FiatShamir.inROM (sigma C) (keyGen C) M).verify ks.1 z.1.1 z.1.2
      pure (!z.2.wasQueried z.1.1 && v)) := by
    unfold SignatureAlg.unforgeableExperiment
    refine bind_congr fun ks => ?_
    obtain ⟨pk, sk⟩ := ks
    refine bind_congr fun z => ?_
    obtain ⟨⟨msg, σ⟩, log⟩ := z
    refine bind_congr fun v => ?_
    simp only [QueryLog.wasQueried_eq_decide_mem_map_fst]
    congr!
  rw [hexp]
  unfold jExp
  simp only [simulateQ_bind, simulateQ_pure, fs_keygen, map_bind]
  have hgen : (keyGen C).gen = (do
      let k ← $ᵗ (NonzeroScalar n)
      pure (keyOf C k.1, C.evenScalar k.1)) := rfl
  have hkg : (bip340 (M := M) C (hOf g) ProbComp).keygen = (do
      let k ← $ᵗ (NonzeroScalar n)
      pure (C.x (C.mulG k.1), k.1)) := rfl
  rw [hgen, hkg]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun k => ?_
  rw [rom_game_key C g k.2 F]
  simp only [map_pure]

end Experiment

end Halfagg.Security
