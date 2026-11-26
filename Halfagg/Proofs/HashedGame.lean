import Halfagg.SecurityHashed
import Halfagg.Proofs.Hop
import Halfagg.Proofs.Explained

/-!
# The game with hash outputs as an oracle machine

`aggExperimentROMH` samples the table of hash outputs first. To count how many
entries the game reads, `gameM` is the same game as a computation that queries
the challenge hash: for the forger's queries, once per signature and once per
item of the forgery. `gameM_table` says that `gameM` with its queries answered
from a table is the game for that table, and `gameM_bound` counts the queries.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security Halfagg.LoggedRun Halfagg.Hop

attribute [local instance] smulVal

-- Uniform nonces, as in `Halfagg/SecurityROM.lean`.
attribute [local instance] NonceGen.uniform

variable {n : ℕ} [Fact n.Prime] {H Hc E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)
variable [SampleableType H] (red : H → ZMod n) (redc : Hc → ZMod n)

/-- The machine's oracles: uniform sampling and the challenge hash. -/
abbrev MSpec (Hc X M : Type) := unifSpec + ChalSpecH Hc X M

/-- A challenge hash query. -/
def chalQ (key : M × (X × X)) : OracleComp (MSpec Hc X M) Hc :=
  liftM ((MSpec Hc X M).query (.inr key))

section Table

variable (g : M × (X × X) → Hc)

theorem tbl_lift {α : Type} (x : ProbComp α) :
    simulateQ (tableImpl (R := fun _ => Hc) g) (liftM x : OracleComp (MSpec Hc X M) α) = x := by
  unfold tableImpl
  rw [QueryImpl.simulateQ_add_liftM_left, HasQuery.toQueryImpl_eq_id', simulateQ_id']

theorem tbl_chal (key : M × (X × X)) :
    simulateQ (tableImpl (R := fun _ => Hc) g) (chalQ (Hc := Hc) key) = pure (g key) := by
  simp [chalQ, tableImpl]
  rfl

end Table

/-! ## The forger's oracles -/

/-- The game's handling of the forger's oracles, with the challenge hash as an
oracle. The state is the list of signed messages and the cache of the
randomizer hash. -/
noncomputable def hHandler (pk : X) (sk : ZMod n) :
    QueryImpl (RomForgerSpecH n H Hc E X M)
      (StateT (List M × (RandSpec H X M).QueryCache) (OracleComp (MSpec Hc X M)))
  | .inl key => fun st => do
      let h ← chalQ key
      pure (h, st)
  | .inr ⟨⟨.random k, _⟩, _⟩ => fun st => do
      let u ← (liftM (liftM (unifSpec.query k) : ProbComp _) : OracleComp (MSpec Hc X M) _)
      pure (⟨u, fun _ => []⟩, st)
  | .inr ⟨⟨.rand ms tail, groups⟩, _⟩ => fun st => do
      let p ← (liftM (((RandSpec H X M).randomOracle
        (toItems C ms (groups ()) ++ rawTail C tail)).run st.2) : OracleComp (MSpec Hc X M) _)
      pure (⟨p.1, fun _ => []⟩, (st.1, p.2))
  | .inr ⟨⟨.sign msg, _⟩, _⟩ => fun st => do
      let k ← (liftM ($ᵗ (NonzeroScalar n)) : OracleComp (MSpec Hc X M) _)
      let h ← chalQ (msg, (C.x (C.mulG k.1), C.x (C.mulG sk)))
      pure (⟨((BIP340.sign C (fun _ _ _ => redc h) (fun _ _ _ => k.1) sk msg).getD (pk, 0)).2,
          fun _ => [(C.liftX ((BIP340.sign C (fun _ _ _ => redc h) (fun _ _ _ => k.1) sk
            msg).getD (pk, 0)).1).getD 0]⟩, (st.1 ++ [msg], st.2))

section Runs

variable (pk : X) (sk : ZMod n) (groups : Groups (Pts E)) (coeffs : Unit → List (List (ZMod n)))
  (st : List M × (RandSpec H X M).QueryCache)

theorem h_run_chal (key : M × (X × X)) :
    (hHandler (H := H) (E := E) C redc pk sk (.inl key)).run st =
      (chalQ key >>= fun h => pure (h, st)) := rfl

theorem h_run_random (k : ℕ) :
    (hHandler (H := H) C redc pk sk (.inr ⟨⟨.random k, groups⟩, coeffs⟩)).run st =
      ((liftM (liftM (unifSpec.query k) : ProbComp _) : OracleComp (MSpec Hc X M) _) >>=
        fun u => pure (⟨u, fun _ => []⟩, st)) := rfl

theorem h_run_rand (ms : List M) (tail : List (Item X M)) :
    (hHandler (H := H) C redc pk sk (.inr ⟨⟨.rand ms tail, groups⟩, coeffs⟩)).run st =
      ((liftM (((RandSpec H X M).randomOracle
          (toItems C ms (groups ()) ++ rawTail C tail)).run st.2) :
          OracleComp (MSpec Hc X M) _) >>=
        fun p => pure (⟨p.1, fun _ => []⟩, (st.1, p.2))) := rfl

theorem h_run_sign (msg : M) :
    (hHandler (H := H) C redc pk sk (.inr ⟨⟨.sign msg, groups⟩, coeffs⟩)).run st =
      ((liftM ($ᵗ (NonzeroScalar n)) : OracleComp (MSpec Hc X M) _) >>= fun k =>
        chalQ (msg, (C.x (C.mulG k.1), C.x (C.mulG sk))) >>= fun h =>
          pure (⟨((BIP340.sign C (fun _ _ _ => redc h) (fun _ _ _ => k.1) sk msg).getD
              (pk, 0)).2,
            fun _ => [(C.liftX ((BIP340.sign C (fun _ _ _ => redc h) (fun _ _ _ => k.1) sk
              msg).getD (pk, 0)).1).getD 0]⟩, (st.1 ++ [msg], st.2))) := rfl

end Runs

section Table

variable (g : M × (X × X) → Hc)

/-- **One request**: the machine's handling with the table is the game's. -/
theorem h_step (pk : X) (sk : ZMod n) (t : Explained (ZMod n) (Request X M) (Pts E))
    (l : List M) (c : (RandSpec H X M).QueryCache) :
    simulateQ (tableImpl (R := fun _ => Hc) g)
        ((hHandler (H := H) C redc pk sk (.inr t)).run (l, c)) =
      (fun y => (y.1.1, (y.1.2, y.2))) <$>
        gRun C (hOf fun key => redc (g key)) pk sk (eraseImpl C t.value) l c := by
  obtain ⟨⟨data, groups⟩, coeffs⟩ := t
  cases data with
  | random k =>
    rw [h_run_random, g_random]
    simp [tbl_lift]
  | rand ms tail =>
    rw [h_run_rand, g_rand]
    simp [tbl_lift]
  | sign msg =>
    rw [h_run_sign, g_sign]
    simp only [simulateQ_bind, simulateQ_pure, tbl_lift, tbl_chal, pure_bind, bip340]
    rw [show ∀ (x : ProbComp (X × ZMod n)), (monadLift x : ProbComp _) = x from fun _ => rfl]
    simp only [map_bind, map_pure]
    refine bind_congr fun k => ?_
    simp [BIP340.sign, hOf]

/-- **The forger's run**: the machine's run with the table is the game's run
for the forger with its challenge queries answered from the table. -/
theorem h_stack (pk : X) (sk : ZMod n) {Result : Type}
    (prog : OracleComp (RomForgerSpecH n H Hc E X M) Result) (l : List M)
    (c : (RandSpec H X M).QueryCache) :
    simulateQ (tableImpl (R := fun _ => Hc) g)
        ((simulateQ (hHandler (H := H) C redc pk sk) prog).run (l, c)) =
      (fun y => (y.1.1, (y.1.2, y.2))) <$>
        gRun C (hOf fun key => redc (g key)) pk sk
          (simulateQ (fun q => eraseImpl C q.value) (simulateQ (answerChalH g) prog)) l c := by
  induction prog using OracleComp.inductionOn generalizing l c with
  | pure x => simp [gRun_pure]
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with key | t
    · rw [h_run_chal]
      simp only [simulateQ_bind, simulateQ_pure, tbl_chal, pure_bind, answerChalH]
      exact ih (g key) l c
    · rw [h_step]
      have hq : simulateQ (fun q => eraseImpl C (n := n) (H := H) (M := M) q.value)
          (answerChalH (H := H) (E := E) g (.inr t)) = eraseImpl C t.value := by
        simp [answerChalH]
      rw [hq, gRun_bind, bind_map_left, map_bind]
      exact bind_congr fun y => ih y.1.1 y.1.2 y.2

end Table

/-! ## The whole game -/

/-- An item without representations, for `knownChal`. -/
def toA (it : Item X M) : AItem n X M := ⟨it.1, it.2.1, it.2.2, 0, 0⟩

/-- The items of a forgery. -/
def outItems (out : Explained (ZMod n) (Out n M) (Pts E)) : List (Item X M) :=
  toItems C out.value.data.ms (out.value.groups ())

/-- The challenges of a list of items, from the oracle. -/
def chalsM (its : List (Item X M)) : OracleComp (MSpec Hc X M) (List (ZMod n)) :=
  its.mapM fun it => redc <$> chalQ (Hc := Hc) (it.2.2, (it.1, it.2.1))

/-- **The game as an oracle machine.** It queries the challenge hash for the
forger, once for every signature, and once for every item of the forgery. -/
noncomputable def gameM (F : RomForgerH n H Hc E X M) : OracleComp (MSpec Hc X M) Bool := do
  let ks ← (liftM (bip340 (M := M) C (fun _ _ _ => 0) ProbComp).keygen :
    OracleComp (MSpec Hc X M) _)
  let w ← (simulateQ (hHandler (H := H) C redc ks.1 ks.2)
    (F.main (initial C ((C.liftX ks.1).getD 0)))).run ([], ∅)
  let zs ← (liftM ((simulateQ (RandSpec H X M).romImpl
    ((List.range (outItems C w.1).length).mapM (zQuery red (n := n) (outItems C w.1)))).run
      w.2.2) : OracleComp (MSpec Hc X M) _)
  let es ← chalsM redc (outItems C w.1)
  pure (aggWins C (knownChal ((outItems C w.1).map toA) es) ks.1 (outItems C w.1)
    w.1.value.data.s zs.1 (fun m => w.2.1.contains m))

section Table

variable (g : M × (X × X) → Hc)

theorem tbl_chals (its : List (Item X M)) :
    simulateQ (tableImpl (R := fun _ => Hc) g) (chalsM redc its) =
      pure (its.map fun it => redc (g (it.2.2, (it.1, it.2.1)))) := by
  unfold chalsM
  induction its with
  | nil => simp
  | cons it its ih =>
    rw [List.mapM_cons]
    simp only [simulateQ_bind, simulateQ_pure, simulateQ_map, tbl_chal, map_pure, pure_bind, ih,
      List.map_cons]

/-- The win check with the challenges of the items is the win check with the
challenge function. -/
theorem aggWins_toA (gs : M × (X × X) → ZMod n) (pk : X) (its : List (Item X M)) (s : ZMod n)
    (zs : List (ZMod n)) (sg : M → Bool) :
    aggWins C (knownChal (its.map toA) (its.map fun it => gs (it.2.2, (it.1, it.2.1)))) pk its
        s zs sg = aggWins C (hOf gs) pk its s zs sg := by
  have h := aggWins_known C gs pk (its.map toA) s zs sg
  simpa [toA, Function.comp_def] using h

/-- **The machine with its queries answered from a table is the game for that
table.** -/
theorem gameM_table (F : RomForgerH n H Hc E X M) :
    simulateQ (tableImpl (R := fun _ => Hc) g) (gameM C red redc F) =
      (simulateQ (RandSpec H X M).romImpl
        (aggExperiment C (hOf fun key => redc (g key)) red (erase C (F.at g)))).run' ∅ := by
  rw [game_form C (hOf fun key => redc (g key)) red]
  unfold gameM
  simp only [simulateQ_bind, tbl_lift]
  refine bind_congr fun ks => ?_
  rw [h_stack, bind_map_left]
  have he : (erase C (F.at g)).main ks.1 = (fun out => (outItems C out, out.value.data.s)) <$>
      simulateQ (fun q => eraseImpl C q.value) (simulateQ (answerChalH g)
        (F.main (initial C ((C.liftX ks.1).getD 0)))) := rfl
  rw [he, gRun_map, bind_map_left]
  refine bind_congr fun y => ?_
  simp only [finish, tbl_chals, simulateQ_pure, pure_bind]
  refine bind_congr fun zs => ?_
  rw [aggWins_toA C (fun key => redc (g key))]

end Table

/-! ## The machine's queries -/

theorem mLift_bound {α : Type} (x : ProbComp α) :
    (liftM x : OracleComp (MSpec Hc X M) α).IsQueryBoundP isHash 0 := by
  induction x using OracleComp.inductionOn with
  | pure a => simp
  | query_bind k next ih =>
    have hb : (liftM (liftM (unifSpec.query k) >>= next) : OracleComp (MSpec Hc X M) α) =
        (liftM ((MSpec Hc X M).query (.inl k)) : OracleComp (MSpec Hc X M) _) >>=
          fun u => liftM (next u) := by
      simp
      rfl
    rw [hb]
    refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun u _ => ih u
    rw [isQueryBoundP_query_iff]
    simp [isHash]

theorem chalQ_bound (key : M × (X × X)) :
    (chalQ (Hc := Hc) key).IsQueryBoundP isHash 1 := by
  unfold chalQ
  rw [isQueryBoundP_query_iff]
  exact fun _ => Nat.one_pos

/-- One oracle call of the forger costs a hash query if it is a challenge query
or a signing request. -/
theorem hHandler_bound (pk : X) (sk : ZMod n) (t : (RomForgerSpecH n H Hc E X M).Domain)
    (st : List M × (RandSpec H X M).QueryCache) :
    ((hHandler (H := H) C redc pk sk t).run st).IsQueryBoundP isHash
      ((if isChalCall t = true then 1 else 0) + (if isSignCall t = true then 1 else 0)) := by
  rcases t with key | ⟨⟨data, groups⟩, coeffs⟩
  · rw [h_run_chal]
    exact (isQueryBoundP_bind (m := 0) (chalQ_bound key)
      fun _ _ => isQueryBoundP_pure _ _ _).mono (by simp [isChalCall, isSignCall])
  · cases data with
    | random k =>
      rw [h_run_random]
      exact (isQueryBoundP_bind (n := 0) (m := 0) (mLift_bound _)
        fun _ _ => isQueryBoundP_pure _ _ _).mono (by simp)
    | rand ms tail =>
      rw [h_run_rand]
      exact (isQueryBoundP_bind (n := 0) (m := 0) (mLift_bound _)
        fun _ _ => isQueryBoundP_pure _ _ _).mono (by simp)
    | sign msg =>
      rw [h_run_sign]
      exact (isQueryBoundP_bind (n := 0) (mLift_bound _) fun k _ =>
        isQueryBoundP_bind (m := 0) (chalQ_bound _)
          fun _ _ => isQueryBoundP_pure _ _ _).mono
        (by simp [isChalCall, isSignCall, isSign])

/-- The forger's run costs a hash query per challenge query and per signing
request. -/
theorem h_stack_bound (pk : X) (sk : ZMod n) {Result : Type}
    (prog : OracleComp (RomForgerSpecH n H Hc E X M) Result) (a b : ℕ)
    (ha : prog.IsQueryBoundP (fun t => isChalCall t) a)
    (hb : prog.IsQueryBoundP (fun t => isSignCall t) b)
    (st : List M × (RandSpec H X M).QueryCache) :
    ((simulateQ (hHandler (H := H) C redc pk sk) prog).run st).IsQueryBoundP isHash (a + b) := by
  induction prog using OracleComp.inductionOn generalizing a b st with
  | pure x => simp
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at ha hb
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    refine (isQueryBoundP_bind (hHandler_bound C redc pk sk t st) fun y _ =>
      ih y.1 _ _ (ha.2 y.1) (hb.2 y.1) y.2).mono ?_
    by_cases h1 : isChalCall t = true <;> by_cases h2 : isSignCall t = true
    · rcases t with key | t <;> simp [isChalCall, isSignCall] at h1 h2
    · obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.pos_iff_ne_zero.mp (ha.1.resolve_left (not_not.mpr h1)))
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Nat.succ_sub_one]
      omega
    · obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.pos_iff_ne_zero.mp (hb.1.resolve_left (not_not.mpr h2)))
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Nat.succ_sub_one]
      omega
    · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
      omega

/-- Every output of the forger's run under `hHandler` is an output of the
forger. -/
theorem h_support (pk : X) (sk : ZMod n) {Result : Type}
    (prog : OracleComp (RomForgerSpecH n H Hc E X M) Result)
    (st : List M × (RandSpec H X M).QueryCache) :
    ∀ z ∈ support ((simulateQ (hHandler (H := H) C redc pk sk) prog).run st),
      z.1 ∈ support prog := by
  induction prog using OracleComp.inductionOn generalizing st with
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

theorem chalsM_bound (its : List (Item X M)) :
    (chalsM (Hc := Hc) redc its).IsQueryBoundP isHash its.length := by
  unfold chalsM
  induction its with
  | nil => simp
  | cons it its ih =>
    rw [List.mapM_cons]
    refine (isQueryBoundP_bind (n := 1) ?_ fun _ _ =>
      isQueryBoundP_bind (m := 0) ih fun _ _ => isQueryBoundP_pure _ _ _).mono ?_
    · rw [isQueryBoundP_map_iff]
      exact chalQ_bound _
    · simp only [List.length_cons]
      omega

/-- **The machine's queries**: at most `qH + qS + ℓ` for a forger with at most
`qH` challenge queries, `qS` signing requests and forgeries of at most `ℓ`
items. -/
theorem gameM_bound (F : RomForgerH n H Hc E X M) (qH qS ℓ : ℕ)
    (hFH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hFS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ) :
    (gameM C red redc F).IsQueryBoundP isHash (qH + qS + ℓ) := by
  unfold gameM
  refine (isQueryBoundP_bind (n := 0) (m := qH + qS + ℓ) (mLift_bound _) fun ks _ =>
    isQueryBoundP_bind (n := qH + qS) (m := ℓ)
      (h_stack_bound C redc _ _ _ qH qS (hFH _) (hFS _) _) fun w hw => ?_).mono (by omega)
  have hlen : (outItems C w.1).length ≤ ℓ :=
    (toItems_length_le C _ _).trans (hL _ _ (h_support C redc _ _ _ _ w hw))
  exact (isQueryBoundP_bind (n := 0) (mLift_bound _) fun zs _ =>
    isQueryBoundP_bind (m := 0) (chalsM_bound redc _)
      fun es _ => isQueryBoundP_pure _ _ _).mono (by omega)

/-! ## The comparison -/

/-- The forger for scalar answers, with the table `g`, is the forger with the
table of the hash outputs `rep (g key)`. -/
theorem erase_viaRep (rep : ZMod n → Hc) (F : RomForgerH n H Hc E X M)
    (g : M × (X × X) → ZMod n) :
    erase C ((F.viaRep rep).at g) = erase C (F.at fun key => rep (g key)) := by
  simp only [erase, RomForger.at, RomForgerH.at, RomForgerH.viaRep, answerChal_repChal]

/-- **The game with hash outputs against the game with scalars.** A forger with
at most `qH` challenge queries, `qS` signing requests and forgeries of at most
`ℓ` items wins the game with hash outputs at most as often as `F.viaRep rep`
wins the game with scalars, plus `qH + qS + ℓ` times the probability that a
uniform hash output `h` is not `rep (redc h)`. -/
theorem aggAdvantageROMH_le_viaRep [Finite M] [Finite X] [Finite Hc] [SampleableType Hc]
    [SampleableType (M × (X × X) → Hc)] [SampleableType (M × (X × X) → ZMod n)]
    (rep : ZMod n → Hc) (hrep : ∀ c, redc (rep c) = c) (F : RomForgerH n H Hc E X M)
    (qH qS ℓ : ℕ)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ) :
    aggAdvantageROMH C red redc F ≤ aggAdvantageROM C red (F.viaRep rep) +
      ((qH + qS + ℓ : ℕ) : ℝ≥0∞) * Pr{let h ← $ᵗ Hc}[rep (redc h) ≠ h] := by
  have h := table_hop (D := M × (X × X)) redc rep hrep (gameM C red redc F) (fun b => b = true)
    (qH + qS + ℓ) (gameM_bound C red redc F qH qS ℓ hH hS hL)
  simp only [gameM_table] at h
  have hg : ∀ g : M × (X × X) → ZMod n, (fun key => redc (rep (g key))) = g := fun g =>
    funext fun key => hrep (g key)
  simp only [hg, ← erase_viaRep] at h
  exact h

/-! ## The forger for scalar answers -/

/-- `F.viaRep rep` makes the oracle calls of `F`. -/
theorem viaRep_queries (rep : ZMod n → Hc) (F : RomForgerH n H Hc E X M)
    (p : M × (X × X) ⊕ Explained (ZMod n) (Request X M) (Pts E) → Bool) (q : ℕ)
    (h : ∀ input, (F.main input).IsQueryBoundP (fun t => p t) q)
    (input : Message Unit (Pts E)) :
    ((F.viaRep rep).main input).IsQueryBoundP (fun t => p t) q := by
  refine IsQueryBoundP.simulateQ_of_step (h input) (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with key | t
    · simp only [repChal]
      rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      exact fun _ => Nat.one_pos
    · simp only [repChal]
      rw [isQueryBoundP_query_iff]
      exact fun _ => Nat.one_pos
  · rcases t with key | t
    · simp only [repChal]
      rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      exact fun h' => absurd h' ht
    · simp only [repChal]
      rw [isQueryBoundP_query_iff]
      exact fun h' => absurd h' ht

/-- Every output of `F.viaRep rep` is an output of `F`. -/
theorem viaRep_support (rep : ZMod n → Hc) {α : Type}
    (prog : OracleComp (RomForgerSpecH n H Hc E X M) α) :
    ∀ z ∈ support (simulateQ (repChal rep) prog), z ∈ support prog := by
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

theorem explainsH_chal {α : Type} (key : M × (X × X))
    (next : Hc → OracleComp (RomForgerSpecH n H Hc E X M) α) (seen : List X) :
    ExplainsNoncesH C (liftM ((RomForgerSpecH n H Hc E X M).query (.inl key)) >>= next) seen ↔
      key.2.1 ∈ seen ∧ ∀ e, ExplainsNoncesH C (next e) seen := Iff.rfl

theorem explainsH_request {α : Type} (q : Explained (ZMod n) (Request X M) (Pts E))
    (next : Message (Reply n H X M q.value.data) (Pts E) →
      OracleComp (RomForgerSpecH n H Hc E X M) α) (seen : List X) :
    ExplainsNoncesH C (liftM ((RomForgerSpecH n H Hc E X M).query (.inr q)) >>= next) seen ↔
      ∀ rep, ExplainsNoncesH C (next rep)
        (if isRand q.value.data then (q.value.groups ()).map C.x ++ seen else seen) := Iff.rfl

/-- `F.viaRep rep` explains the nonces it hashes if `F` does. -/
theorem viaRep_explains (rep : ZMod n → Hc) {α : Type}
    (prog : OracleComp (RomForgerSpecH n H Hc E X M) α) (seen : List X)
    (h : ExplainsNoncesH C prog seen) :
    ExplainsNonces C (simulateQ (repChal rep) prog) seen := by
  induction prog using OracleComp.inductionOn generalizing seen with
  | pure x => trivial
  | query_bind t next ih =>
    rcases t with key | q
    · rw [explainsH_chal] at h
      have hs : simulateQ (repChal rep)
          (liftM ((RomForgerSpecH n H Hc E X M).query (.inl key)) >>= next) =
          liftM ((RomForgerSpec n H E X M).query (.inl key)) >>= fun c =>
            simulateQ (repChal rep) (next (rep c)) := by
        simp [repChal]
      rw [hs, explains_chal]
      exact ⟨h.1, fun e => ih _ _ (h.2 _)⟩
    · rw [explainsH_request] at h
      have hs : simulateQ (repChal rep)
          (liftM ((RomForgerSpecH n H Hc E X M).query (.inr q)) >>= next) =
          liftM ((RomForgerSpec n H E X M).query (.inr q)) >>= fun r =>
            simulateQ (repChal rep) (next r) := by
        simp [repChal]
      rw [hs, explains_request]
      exact fun r => ih _ _ (h r)

end Halfagg.Security
