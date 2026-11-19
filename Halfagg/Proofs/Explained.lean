import Halfagg.Proofs.Tight

/-!
# Forgers that explain the nonces they hash: proofs

The signature machine of `Halfagg/SecurityTight.lean` forges only if the
challenge of the target item cancels the coefficient of `P*` in the item's
nonce point (`repB_hit`). For a forger with `ExplainsNonces` this has
probability at most `(qH + 1)/n`:

* `repB_le_lazy`: the event is at most as likely as the analysis machine
  `hitExp` reporting it, and that machine reaches the challenge hash only
  through an oracle, so the hash can be sampled lazily.
* `forger_inv`: in the lazy run, every cached challenge belongs to a signed
  message or misses `-β` for the recorded coefficient `β` of its nonce
  (`HInv`), except with probability `1/n` per challenge query.
* `hit_lazy`: so the analysis machine reports the event with probability at
  most `(qH + 1)/n`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security Halfagg.LoggedRun

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)
variable [SampleableType H] {red : H → ZMod n}


/-! ## The event: the challenge of the target item cancels its coefficient -/

/-- All items lift, and the target item's challenge is `-β` for the recorded
coefficient `β` of `P*` in its nonce point. -/
def hitI (ch : X → X → M → ZMod n) (pk : X) (items : List (AItem n X M)) (signed : List M) :
    Bool :=
  match target pk items signed with
  | none => false
  | some a => items.all (fun b => lifts C (strip b)) && decide (a.repR.2 + ch a.r a.pk a.m = 0)

/-- If the signature machine's event occurs, the challenge of the target item
cancels the coefficient of `P*` in its nonce point. -/
theorem repB_hit (ch : X → X → M → ZMod n) (hx0 : C.liftX (C.x 0) = none)
    (F : AlgForger n H E X M)
    (r : X × Explained (ZMod n) (Out n M) (Pts E) × Core n X M)
    (hr : r ∈ support (annPhase1 C ch F)) (zs : List (ZMod n))
    (hR : repB C ch
      (r.1, finalItems C r.2.1 r.2.2, r.2.1.value.data.s, zs, r.2.2.signed) = true) :
    hitI C ch r.1 (finalItems C r.2.1 r.2.2) r.2.2.signed = true := by
  obtain ⟨d, hd, heven, hpk, -, recv, hcore, hval⟩ := phase1_ok C ch hx0 F r hr
  have hPstar : C.liftX (C.x (C.mulG d)) = some (C.mulG d) :=
    C.liftX_x _ (C.mulG_ne_zero hd) heven
  unfold repB at hR
  unfold hitI
  rcases hfind : target r.1 (finalItems C r.2.1 r.2.2) r.2.2.signed with _ | a
  · rw [hfind] at hR
    exact Bool.noConfusion hR
  · simp only [hfind] at hR ⊢
    rw [hpk, hPstar, Option.getD_some] at hR
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq] at hR
    obtain ⟨⟨⟨hkey, hw⟩, hβ⟩, -⟩ := hR
    have hl0 := hw
    simp only [aggWins, verifyWith, Bool.and_eq_true, List.all_eq_true] at hl0
    have hl1 := hl0.1.1.2
    rw [items_map] at hl1
    have hlift : ∀ b ∈ finalItems C r.2.1 r.2.2, lifts C (strip b) = true :=
      fun b hb => hl1 _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
    have hl : ∀ it ∈ toItems C r.2.1.value.data.ms (r.2.1.value.groups ()),
        lifts C it = true := by
      have h2 := hl1
      rw [show (fun a : AItem n X M => (a.r, a.pk, a.m)) = strip from rfl, finalItems,
        map_strip_annotate] at h2
      exact h2
    have hok := finalItems_ok C hx0 d hcore hval hl
    have ha := List.mem_of_find?_eq_some hfind
    have hpa := List.find?_some hfind
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hpa
    obtain ⟨hapk, -⟩ := hpa
    have hPa : repPoint C d a.repPk = C.mulG d :=
      ((hok a ha).2 _ (by rw [hapk, hpk, hPstar])).symm
    have hPd : a.repPk.1 + a.repPk.2 * d = d := C.mulG_injective hPa
    have hb : a.repPk.2 = 1 := by
      by_contra hb
      apply hkey
      apply congrArg C.mulG
      unfold candKey
      rw [← hpk]
      simp only [hfind, hb, ↓reduceIte]
      rw [div_eq_iff (sub_ne_zero.mpr (Ne.symm hb))]
      linear_combination hPd
    simp only [starRep, hb, mul_one] at hβ
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨hlift, hβ⟩

/-! ## The analysis machine -/

/-- The last step of the analysis machine: ask for the challenge of the target
item and report whether it cancels the item's coefficient. -/
noncomputable def hitFin (pk : X) (out : Explained (ZMod n) (Out n M) (Pts E))
    (st : Core n X M) : OracleComp (RomSpec n X M) Bool :=
  match target pk (finalItems C out st) st.signed with
  | none => pure false
  | some a => do
      let e ← hashQ (n := n) (a.m, (a.r, a.pk))
      pure ((finalItems C out st).all (fun b => lifts C (strip b)) &&
        decide (a.repR.2 + e = 0))

/-- The analysis machine: the forger's run as in `romMachine`, then `hitFin`. -/
noncomputable def hitProg (F : RomForger n H E X M) (P : Stmt C) :
    OracleComp (RomSpec n X M) Bool := do
  let r ← ((simulateQ (romHandler (H := H) C (C.x P.1))
    (F.main (initial C ((C.liftX (C.x P.1)).getD 0)))).run Core.init).run ∅
  hitFin C (C.x P.1) r.1.1 r.1.2

/-- The analysis machine inside the Fiat-Shamir game's oracles, with the
challenge hash as an oracle. -/
noncomputable def hitExp (F : RomForger n H E X M) :
    OracleComp (unifSpec + ChalSpec n X M) Bool := do
  let k ← (monadLift ($ᵗ (NonzeroScalar n) : ProbComp _) :
    OracleComp (unifSpec + ChalSpec n X M) _)
  Prod.fst <$> (simulateQ (appFS C (keyOf C k.1) (C.evenScalar k.1))
    (hitProg C F (keyOf C k.1))).run []

section Table

variable (g : M × (X × X) → ZMod n)

theorem hitFin_table (P : Stmt C) (w : ZMod n) (pk : X)
    (out : Explained (ZMod n) (Out n M) (Pts E)) (st : Core n X M) (l : List M) :
    (simulateQ (fsImpl C g P w) (hitFin C pk out st)).run l =
      pure (hitI C (hOf g) pk (finalItems C out st) st.signed, l) := by
  unfold hitFin hitI
  rcases hfind : target pk (finalItems C out st) st.signed with _ | a
  · simp
  · simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, fs_hashQ,
      pure_bind, hOf]
    rfl

/-- Against a fixed table, the analysis machine is the joint run followed by
the event. -/
theorem hitExp_table (F : RomForger n H E X M) :
    simulateQ (tableImpl g) (hitExp C F) = (do
      let k ← $ᵗ (NonzeroScalar n)
      let p ← ((simulateQ (jImpl (H := H) C (hOf g) (C.x (C.mulG k.1)) k.1)
        ((F.at g).main (initial C ((C.liftX (C.x (C.mulG k.1))).getD 0)))).run Core.init).run ∅
      pure (hitI C (hOf g) (C.x (C.mulG k.1)) (finalItems C p.1.1 p.1.2) p.1.2.signed)) := by
  unfold hitExp
  simp only [simulateQ_bind, table_monadLift, simulateQ_map]
  refine bind_congr fun k => ?_
  have hpk : C.x (keyOf C k.1).1 = C.x (C.mulG k.1) := C.x_evenScalar k.1
  have hstack := rom_stack C g k.2 (F.main (initial C ((C.liftX (C.x (C.mulG k.1))).getD 0)))
    (Core.init : Core n X M) ∅
  rw [show (Core.init : Core n X M).signed = [] from rfl] at hstack
  rw [fs_stack]
  unfold hitProg
  simp only [hpk, simulateQ_bind, StateT.run_bind, map_bind]
  rw [hstack, bind_map_left]
  refine bind_congr fun p => ?_
  rw [hitFin_table]
  rfl

end Table

/-- The forger's run with a key is a run of `annPhase1`. -/
theorem phase_support (ch : X → X → M → ZMod n) (F : AlgForger n H E X M) (k : NonzeroScalar n)
    (p : (Explained (ZMod n) (Out n M) (Pts E) × Core n X M) × (AnnSpec n H X M).QueryCache)
    (hp : p ∈ support (((simulateQ (jImpl (H := H) C ch (C.x (C.mulG k.1)) k.1)
      (F.main (initial C ((C.liftX (C.x (C.mulG k.1))).getD 0)))).run Core.init).run ∅)) :
    (C.x (C.mulG k.1), p.1.1, p.1.2) ∈ support (annPhase1 C ch F) := by
  unfold annPhase1
  rw [mem_support_bind_iff]
  refine ⟨(C.x (C.mulG k.1), k.1), ?_, ?_⟩
  · simp only [bip340]
    rw [show ∀ (x : ProbComp (X × ZMod n)),
      (monadLift x : OracleComp (unifSpec + AnnSpec n H X M) _) =
        liftComp x (unifSpec + AnnSpec n H X M) from fun _ => (liftComp_eq_liftM _).symm,
      support_liftComp]
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨k, by simp, rfl⟩
  · rw [mem_support_bind_iff]
    refine ⟨p.1, ?_, by simp⟩
    refine support_simulateQ_run'_subset (AnnSpec n H X M).romImpl _ ∅ ?_
    rw [StateT.run'_eq, support_map, rom_annImpl]
    exact ⟨p, hp, rfl⟩

/-- The signature machine's event implies the analysis machine's, table by
table, and the analysis machine can sample its table lazily. -/
theorem repB_le_lazy [Finite M] [Finite X] [SampleableType (M × (X × X) → ZMod n)]
    (hx0 : C.liftX (C.x 0) = none) (F : RomForger n H E X M) :
    Pr{let b ← (($ᵗ (M × (X × X) → ZMod n)) >>= fun g =>
        repB C (hOf g) <$> jExp C (hOf g) red (F.at g))}[b = true] ≤
      Pr{let b ← (simulateQ (ChalSpec n X M).romImpl (hitExp C F)).run' ∅}[b = true] := by
  rw [rom_eq_table]
  simp only [hitExp_table]
  refine prEvent_bind_mono _ _ _ _ _ fun g => ?_
  rw [prEvent_map, jExp_eq]
  refine prEvent_bind_mono _ _ _ _ _ fun k => ?_
  unfold jRun
  have h := prEvent_bind_le_prEvent_add_of_support
    (((simulateQ (jImpl (H := H) C (hOf g) (C.x (C.mulG k.1)) k.1)
      ((F.at g).main (initial C ((C.liftX (C.x (C.mulG k.1))).getD 0)))).run Core.init).run ∅)
    (fun p => ((List.range (finalItems C p.1.1 p.1.2).length).mapM
        (jZ red (finalItems C p.1.1 p.1.2))).run p.2 >>= fun q =>
      pure (C.x (C.mulG k.1), finalItems C p.1.1 p.1.2, p.1.1.value.data.s, q.1, p.1.2.signed))
    (fun p => hitI C (hOf g) (C.x (C.mulG k.1)) (finalItems C p.1.1 p.1.2) p.1.2.signed = true)
    (fun t : Transcript n X M => repB C (hOf g) t = true) (ε := 0) fun p hp hno => by
      rw [nonpos_iff_eq_zero]
      refine prEvent_eq_zero_of_forall_mem_support _ _ fun t ht hR => hno ?_
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at ht
      obtain ⟨q, -, rfl⟩ := ht
      exact repB_hit C (hOf g) hx0 (F.at g) _ (phase_support C (hOf g) (F.at g) k p hp) q.1 hR
  rw [add_zero] at h
  refine h.trans (le_of_eq ?_)
  rw [bind_pure_comp, prEvent_map]

/-! ## The game's oracles with a lazily sampled challenge hash -/

section Lazy

variable (P : Stmt C) (w : ZMod n)

/-- A computation of the Fiat-Shamir adversary under the game's oracles, with
the signing log `l` and the lazily sampled challenge hash's cache `cH`. -/
noncomputable def lzRun {α : Type} (x : OracleComp (RomSpec n X M) α) (l : List M)
    (cH : (ChalSpec n X M).QueryCache) :
    ProbComp ((α × List M) × (ChalSpec n X M).QueryCache) :=
  (simulateQ (ChalSpec n X M).romImpl ((simulateQ (appFS C P w) x).run l)).run cH

theorem lz_pure {α : Type} (a : α) (l : List M) (cH : (ChalSpec n X M).QueryCache) :
    lzRun C P w (pure a) l cH = pure ((a, l), cH) := by
  simp [lzRun]

theorem lz_bind {α β : Type} (x : OracleComp (RomSpec n X M) α)
    (f : α → OracleComp (RomSpec n X M) β) (l : List M) (cH : (ChalSpec n X M).QueryCache) :
    lzRun C P w (x >>= f) l cH =
      lzRun C P w x l cH >>= fun y => lzRun C P w (f y.1.1) y.1.2 y.2 := by
  simp [lzRun, simulateQ_bind, StateT.run_bind]

theorem lz_map {α β : Type} (x : OracleComp (RomSpec n X M) α) (f : α → β) (l : List M)
    (cH : (ChalSpec n X M).QueryCache) :
    lzRun C P w (f <$> x) l cH = (fun y => ((f y.1.1, y.1.2), y.2)) <$> lzRun C P w x l cH := by
  rw [map_eq_bind_pure_comp, lz_bind, map_eq_bind_pure_comp]
  exact bind_congr fun y => lz_pure C P w _ _ _

theorem chal_unif (k : ℕ) (cH : (ChalSpec n X M).QueryCache) :
    (simulateQ (ChalSpec n X M).romImpl
      (liftM ((unifSpec + ChalSpec n X M).query (.inl k)))).run cH =
      (fun u => (u, cH)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
  simpa using roSim.run_apply_inl (hashSpec := ChalSpec n X M) (ChalSpec n X M).randomOracle k cH

theorem chal_ro (key : M × (X × X)) (cH : (ChalSpec n X M).QueryCache) :
    (simulateQ (ChalSpec n X M).romImpl
      (liftM ((unifSpec + ChalSpec n X M).query (.inr key)))).run cH =
      ((ChalSpec n X M).randomOracle key).run cH := by
  simp

theorem chal_monadLift {α : Type} (x : ProbComp α) (cH : (ChalSpec n X M).QueryCache) :
    (simulateQ (ChalSpec n X M).romImpl
      (monadLift x : OracleComp (unifSpec + ChalSpec n X M) α)).run cH =
      (fun a => (a, cH)) <$> x := by
  rw [show (monadLift x : OracleComp (unifSpec + ChalSpec n X M) α) = liftM x from rfl,
    OracleSpec.simulateQ_romImpl_liftM_run]

theorem chal_hasQuery (key : M × (X × X)) (cH : (ChalSpec n X M).QueryCache) :
    (simulateQ (ChalSpec n X M).romImpl
      (HasQuery.query (spec := ChalSpec n X M) key :
        OracleComp (unifSpec + ChalSpec n X M) (ZMod n))).run cH =
      ((ChalSpec n X M).randomOracle key).run cH := by
  simp

theorem lz_unif (k : ℕ) (l : List M) (cH : (ChalSpec n X M).QueryCache) :
    lzRun C P w (liftM ((RomSpec n X M).query (.inl (.inl k)))) l cH =
      (fun u => ((u, l), cH)) <$> (liftM (unifSpec.query k) : ProbComp _) := by
  unfold lzRun
  rw [simulateQ_spec_query, appFS_inl, simulateQ_map, StateT.run_map, chal_unif]
  simp

theorem lz_hash (key : M × (X × X)) (l : List M) (cH : (ChalSpec n X M).QueryCache) :
    lzRun C P w (hashQ (n := n) key) l cH =
      (fun p => ((p.1, l), p.2)) <$> ((ChalSpec n X M).randomOracle key).run cH := by
  unfold lzRun hashQ
  rw [simulateQ_spec_query, appFS_inl, simulateQ_map, StateT.run_map, chal_ro]
  rfl

theorem lz_lift {α : Type} (x : ProbComp α) (l : List M) (cH : (ChalSpec n X M).QueryCache) :
    lzRun C P w (liftM x : OracleComp (RomSpec n X M) α) l cH =
      (fun a => ((a, l), cH)) <$> x := by
  induction x using OracleComp.inductionOn generalizing l cH with
  | pure a => simp [lzRun]
  | query_bind k next ih =>
    have hb : (liftM (liftM (unifSpec.query k) >>= next) : OracleComp (RomSpec n X M) α) =
        (liftM (unifSpec.query k) : OracleComp (RomSpec n X M) _) >>= fun u => liftM (next u) := by
      simp
      rfl
    have hq : lzRun C P w (liftM (unifSpec.query k) : OracleComp (RomSpec n X M) _) l cH =
        (fun u => ((u, l), cH)) <$> (liftM (unifSpec.query k) : ProbComp _) :=
      lz_unif C P w k l cH
    rw [hb, lz_bind, hq, bind_map_left, map_bind]
    exact bind_congr fun u => ih u l cH

theorem lz_sign (msg : M) (l : List M) (cH : (ChalSpec n X M).QueryCache) :
    lzRun C P w (liftM ((RomSpec n X M).query (.inr msg))) l cH = (do
      let k ← $ᵗ (NonzeroScalar n)
      let p ← ((ChalSpec n X M).randomOracle (msg, (C.x (C.mulG k.1), C.x P.1))).run cH
      pure ((((C.x (C.mulG k.1), C.x P.1), C.evenScalar k.1 + p.1 * w), l ++ [msg]), p.2)) := by
  unfold lzRun
  rw [simulateQ_spec_query, appFS_inr, simulateQ_map, StateT.run_map]
  simp only [FiatShamir, sigma, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    map_bind, map_pure, chal_monadLift, chal_hasQuery, bind_assoc, pure_bind]

/-! ## The invariant -/

/-- Every cached challenge belongs to a signed message, or its nonce has a
recorded representation whose coefficient of `P*` the challenge does not cancel. -/
def HInv (st : Core n X M) (cH : (ChalSpec n X M).QueryCache) : Prop :=
  ∀ K e, cH K = some e → K.1 ∈ st.signed ∨ ∃ ρ : Rep n, st.memo K.2.1 = some ρ ∧ ρ.2 + e ≠ 0

theorem hinv_memoize {st : Core n X M} {cH : (ChalSpec n X M).QueryCache} (h : HInv st cH)
    (pts : List E) (coeffs : List (List (ZMod n))) : HInv (memoize C st pts coeffs) cH := by
  intro K e hK
  rcases h K e hK with h1 | ⟨ρ, hρ, hne⟩
  · exact Or.inl h1
  · exact Or.inr ⟨ρ, memoizeList_of_some C st.basis pts coeffs hρ, hne⟩

/-- One lazily sampled query caches at most its own key. -/
theorem ro_support (key : M × (X × X)) (cH : (ChalSpec n X M).QueryCache)
    (p : ZMod n × (ChalSpec n X M).QueryCache)
    (hp : p ∈ support (((ChalSpec n X M).randomOracle key).run cH)) :
    ∀ K e, p.2 K = some e → cH K = some e ∨ K = key := by
  intro K e h
  rw [randomOracle.run_eq] at hp
  rcases hc : cH key with _ | u
  · rw [hc] at hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
    obtain ⟨u, -, rfl⟩ := hp
    by_cases hK : K = key
    · exact Or.inr hK
    · left
      rwa [QueryCache.cacheQuery_of_ne _ _ hK] at h
  · rw [hc] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact Or.inl h

theorem prEvent_bind_le_of_forall {α β : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (q : β → Prop) (ε : ℝ≥0∞) (h : ∀ a ∈ support mx, Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let y ← mx >>= f}[q y] ≤ ε := by
  have h' := prEvent_bind_le_prEvent_add_of_support mx f (fun _ => False) q
    (fun a ha _ => h a ha)
  rwa [prEvent_eq_zero_of_forall_mem_support _ _ (fun _ _ hf => hf), zero_add] at h'

theorem explains_chal {α : Type} (key : M × (X × X))
    (next : ZMod n → OracleComp (RomForgerSpec n H E X M) α) (seen : List X) :
    ExplainsNonces C (liftM ((RomForgerSpec n H E X M).query (.inl key)) >>= next) seen ↔
      key.2.1 ∈ seen ∧ ∀ e, ExplainsNonces C (next e) seen := Iff.rfl

theorem explains_request {α : Type} (q : Explained (ZMod n) (Request X M) (Pts E))
    (next : Message (Reply n H X M q.value.data) (Pts E) → OracleComp (RomForgerSpec n H E X M) α)
    (seen : List X) :
    ExplainsNonces C (liftM ((RomForgerSpec n H E X M).query (.inr q)) >>= next) seen ↔
      ∀ rep, ExplainsNonces C (next rep)
        (if isRand q.value.data then (q.value.groups ()).map C.x ++ seen else seen) := Iff.rfl

/-- The explained x-coordinates have recorded representations. -/
def Seen (st : Core n X M) (seen : List X) : Prop := ∀ x ∈ seen, (st.memo x).isSome

/-- A request of the forger keeps the invariant, and a randomizer request
records a representation for each of its points. -/
theorem step_request (t : Explained (ZMod n) (Request X M) (Pts E)) (st : Core n X M)
    (cA : (AnnSpec n H X M).QueryCache) (l : List M) (cH : (ChalSpec n X M).QueryCache)
    (seen : List X) (h : HInv st cH) (hs : Seen st seen) :
    ∀ z ∈ support (lzRun C P w (((romHandler (H := H) C (C.x P.1) (.inr t)).run st).run cA) l cH),
      HInv z.1.1.1.2 z.2 ∧ Seen z.1.1.1.2
        (if isRand t.value.data then (t.value.groups ()).map C.x ++ seen else seen) := by
  obtain ⟨⟨data, groups⟩, coeffs⟩ := t
  intro z hz
  cases data with
  | random k =>
    rw [rom_run_random, lz_bind, lz_unif] at hz
    simp only [bind_map_left, lz_pure, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact ⟨h, by simpa [isRand] using hs⟩
  | rand ms tail =>
    rw [rom_run_rand, lz_bind, lz_lift] at hz
    simp only [bind_map_left, lz_pure, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at hz
    obtain ⟨p, -, rfl⟩ := hz
    refine ⟨hinv_memoize C h _ _, fun x hx => ?_⟩
    simp only [isRand, ↓reduceIte, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨Y, hY, rfl⟩ | hx
    · exact memoizeList_isSome C st.basis _ _ st.memo hY
    · obtain ⟨ρ, hρ⟩ := Option.isSome_iff_exists.mp (hs x hx)
      have hm := memoizeList_of_some C st.basis (groups ()) (coeffs ()) hρ
      simp only [memoize, hm, Option.isSome_some]
  | sign msg =>
    rw [rom_run_sign, lz_bind, lz_sign] at hz
    simp only [bind_assoc, pure_bind, lz_bind, lz_hash, bind_map_left, lz_pure, support_bind,
      support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨k, -, p, hp, q, hq, rfl⟩ := hz
    refine ⟨fun K e hK => ?_, fun x hx => hs x (by simpa [isRand] using hx)⟩
    rcases ro_support _ _ q hq K e hK with h1 | rfl
    · rcases ro_support _ _ p hp K e h1 with h2 | rfl
      · rcases h K e h2 with h3 | ⟨ρ, hρ, hne⟩
        · exact Or.inl (List.mem_append_left _ h3)
        · exact Or.inr ⟨ρ, hρ, hne⟩
      · exact Or.inl (by simp)
    · exact Or.inl (by simp)

/-- A fresh challenge breaks the invariant only if it is `-β` for the recorded
coefficient `β` of its nonce. -/
theorem hinv_fresh {st : Core n X M} {cH : (ChalSpec n X M).QueryCache} (h : HInv st cH)
    (key : M × (X × X)) {ρ : Rep n} (hρ : st.memo key.2.1 = some ρ) (u : ZMod n)
    (hno : ¬ HInv st (cH.cacheQuery key u)) : u = -ρ.2 := by
  by_contra hu
  refine hno fun K e hK => ?_
  by_cases hKk : K = key
  · subst hKk
    rw [QueryCache.cacheQuery_self] at hK
    cases hK
    exact Or.inr ⟨ρ, hρ, fun h0 => hu (eq_neg_of_add_eq_zero_right h0)⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ hKk] at hK
    exact h K e hK

theorem uniform_eq_le (c : ZMod n) :
    Pr{let u ← $ᵗ (ZMod n)}[u = c] = (n : ℝ≥0∞)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample_eq_singleton, ZMod.card]

/-- A challenge query of the forger is one lazily sampled query. -/
theorem chal_run (key : M × (X × X)) (st : Core n X M) (cA : (AnnSpec n H X M).QueryCache)
    (l : List M) (cH : (ChalSpec n X M).QueryCache) :
    lzRun C P w (((romHandler (H := H) (E := E) C (C.x P.1) (.inl key)).run st).run cA) l cH =
      (fun q => ((((q.1, st), cA), l), q.2)) <$>
        ((ChalSpec n X M).randomOracle key).run cH := by
  have hraw : ((romHandler (H := H) (E := E) C (C.x P.1) (.inl key)).run st).run cA =
      (fun e => ((e, st), cA)) <$> hashQ (n := n) key := by
    simp [romHandler]
  rw [hraw, lz_map, lz_hash, Functor.map_map]

/-- A challenge query on an explained nonce breaks the invariant with
probability at most `1/n`. -/
theorem step_chal (key : M × (X × X)) (st : Core n X M) (cA : (AnnSpec n H X M).QueryCache)
    (l : List M) (cH : (ChalSpec n X M).QueryCache) (h : HInv st cH) {ρ : Rep n}
    (hρ : st.memo key.2.1 = some ρ) :
    Pr{let z ← lzRun C P w (((romHandler (H := H) (E := E) C (C.x P.1) (.inl key)).run st).run cA)
        l cH}[¬ HInv z.1.1.1.2 z.2] ≤ (n : ℝ≥0∞)⁻¹ := by
  rw [chal_run, prEvent_map, randomOracle.run_eq]
  rcases hc : cH key with _ | u
  · simp only []
    rw [bind_pure_comp, prEvent_map]
    exact (prEvent_mono_of_support _ _ _ fun u _ hu => hinv_fresh h key hρ u hu).trans
      (le_of_eq (uniform_eq_le _))
  · simp only []
    rw [prEvent_eq_zero_of_forall_mem_support]
    · exact zero_le
    · intro z hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact not_not.mpr h

/-- **The forger's run keeps the invariant**, except with probability `1/n` per
challenge query. -/
theorem forger_inv {α : Type} (prog : OracleComp (RomForgerSpec n H E X M) α) (Q : ℕ)
    (hQ : prog.IsQueryBoundP (fun t => isChalCall t) Q) (seen : List X)
    (hE : ExplainsNonces C prog seen) (st : Core n X M)
    (cA : (AnnSpec n H X M).QueryCache) (l : List M) (cH : (ChalSpec n X M).QueryCache)
    (h : HInv st cH) (hs : Seen st seen) :
    Pr{let z ← lzRun C P w (((simulateQ (romHandler (H := H) C (C.x P.1)) prog).run st).run cA)
        l cH}[¬ HInv z.1.1.1.2 z.2] ≤ Q * (n : ℝ≥0∞)⁻¹ := by
  induction prog using OracleComp.inductionOn generalizing Q seen st cA l cH with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, lz_pure]
    rw [prEvent_eq_zero_of_forall_mem_support]
    · exact zero_le
    · intro z hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact not_not.mpr h
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at hQ
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [lz_bind]
    rcases t with key | t
    · rw [explains_chal] at hE
      obtain ⟨ρ, hρ⟩ := Option.isSome_iff_exists.mp (hs _ hE.1)
      have hpos : 0 < Q := hQ.1.resolve_left (by simp [isChalCall])
      obtain ⟨Q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun y => ¬ HInv y.1.1.1.2 y.2) _
        (ε := (Q' : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) fun y hy hI => ?_).trans ?_
      · rw [chal_run, support_map] at hy
        obtain ⟨q, -, rfl⟩ := hy
        exact ih q.1 Q' ((hQ.2 q.1).mono (by simp [isChalCall])) seen (hE.2 _) _ _ _ _
          (not_not.mp hI) hs
      · refine (add_le_add (step_chal C P w key st cA l cH h hρ) le_rfl).trans (le_of_eq ?_)
        push_cast
        ring
    · rw [explains_request] at hE
      refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun y => ¬ HInv y.1.1.1.2 y.2) _
        (ε := (Q : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) fun y hy _ => ?_).trans ?_
      · have hstep := step_request C P w t st cA l cH seen h hs y hy
        exact ih y.1.1.1.1 Q ((hQ.2 y.1.1.1.1).mono (by simp [isChalCall])) _ (hE _) _ _ _ _
          hstep.1 hstep.2
      · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun y hy =>
          not_not.mpr (step_request C P w t st cA l cH seen h hs y hy).1, zero_add]

/-- From a state with the invariant, the last step reports a cancellation with
probability at most `1/n`. -/
theorem hitFin_lazy (out : Explained (ZMod n) (Out n M) (Pts E)) (st : Core n X M)
    (l : List M) (cH : (ChalSpec n X M).QueryCache) (h : HInv st cH) :
    Pr{let z ← lzRun C P w (hitFin C (C.x P.1) out st) l cH}[z.1.1 = true] ≤
      (n : ℝ≥0∞)⁻¹ := by
  unfold hitFin
  rcases hfind : target (C.x P.1) (finalItems C out st) st.signed with _ | a
  · simp only []
    rw [lz_pure, prEvent_eq_zero_of_forall_mem_support]
    · exact zero_le
    · intro z hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp
  · simp only []
    rw [lz_bind, lz_hash, bind_map_left]
    simp only [lz_pure]
    rw [bind_pure_comp, prEvent_map, randomOracle.run_eq]
    have hpa := List.find?_some hfind
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hpa
    have ha := List.mem_of_find?_eq_some hfind
    rcases hc : cH (a.m, (a.r, a.pk)) with _ | e
    · simp only []
      rw [bind_pure_comp, prEvent_map]
      refine (prEvent_mono_of_support _ _ (fun u => u = -a.repR.2) fun u _ hu => ?_).trans
        (le_of_eq (uniform_eq_le _))
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hu
      exact eq_neg_of_add_eq_zero_right hu.2
    · simp only []
      rw [prEvent_eq_zero_of_forall_mem_support]
      · exact zero_le
      · intro z hz
        simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, not_and]
        intro hall
        rcases h _ e hc with hs | ⟨ρ, hρ, hne⟩
        · exact absurd hs hpa.2
        · have hl : ∀ it ∈ toItems C out.value.data.ms (out.value.groups ()),
              lifts C it = true := by
            intro it hit
            have hmap := map_strip_annotate C
              (memoize C st (out.value.groups ()) (out.coefficients ())).memo
              (toItems C out.value.data.ms (out.value.groups ()))
            rw [← hmap] at hit
            obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hit
            exact hall b hb
          have ha' := ha
          rw [finalItems, annotate_of_lifts C _ hl] at ha'
          obtain ⟨it, -, rfl⟩ := List.mem_map.mp ha'
          have hmemo := memoizeList_of_some C st.basis (out.value.groups ())
            (out.coefficients ()) hρ
          simp only [memoize, hmemo, Option.getD_some]
          exact hne

end Lazy

/-- **The analysis machine reports a cancellation with probability at most
`(qH + 1)/n`**, for a forger with `qH` challenge queries that explains their
nonces. -/
theorem hit_lazy (F : RomForger n H E X M) (qH : ℕ)
    (hH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hE : ∀ input, ExplainsNonces C (F.main input) []) :
    Pr{let b ← (simulateQ (ChalSpec n X M).romImpl (hitExp C F)).run' ∅}[b = true] ≤
      (qH + 1 : ℝ≥0∞) / n := by
  have hrun : (simulateQ (ChalSpec n X M).romImpl (hitExp C F)).run' ∅ = (do
      let k ← $ᵗ (NonzeroScalar n)
      (fun z => z.1.1) <$> lzRun C (keyOf C k.1) (C.evenScalar k.1)
        (hitProg C F (keyOf C k.1)) [] ∅) := by
    unfold hitExp lzRun
    simp only [simulateQ_bind, simulateQ_map, StateT.run'_eq, StateT.run_bind, StateT.run_map,
      chal_monadLift, map_bind, bind_map_left, Functor.map_map]
  rw [hrun]
  refine prEvent_bind_le_of_forall _ _ _ _ fun k _ => ?_
  rw [prEvent_map]
  unfold hitProg
  rw [lz_bind]
  have hinit : HInv (Core.init : Core n X M) (∅ : (ChalSpec n X M).QueryCache) := by
    intro K e hK
    cases hK
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun y => ¬ HInv y.1.1.1.2 y.2) _
    (ε := (n : ℝ≥0∞)⁻¹) fun y _ hy =>
      hitFin_lazy C (keyOf C k.1) (C.evenScalar k.1) y.1.1.1.1 y.1.1.1.2 y.1.2 y.2
        (not_not.mp hy)).trans ?_
  refine (add_le_add (forger_inv C (keyOf C k.1) (C.evenScalar k.1) _ qH (hH _) [] (hE _)
    _ _ _ _ hinit (fun x hx => by simp at hx)) le_rfl).trans (le_of_eq ?_)
  rw [div_eq_mul_inv, add_mul, one_mul]

end Halfagg.Security
