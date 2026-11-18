import Halfagg.Proofs.ROM

/-!
# Query counts of the oracle reduction

`reductionROM_bound`: if the forger makes at most `qH` challenge-hash queries and
`qS` signing requests and its forgeries have at most `ℓ` items, then
`reductionROM F` makes at most `qS` signing queries and `qH + qS + ℓ + 1` hash
queries.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)

section Bound

variable (p : (RomSpec n X M).Domain → Prop) [DecidablePred p] (cH cS : ℕ)
  (hU : ∀ k, ¬ p (.inl (.inl k))) (hH : ∀ key, p (.inl (.inr key)) → 0 < cH)
  (hS : ∀ m, p (.inr m) → 0 < cS)

include hH in
theorem hashQ_bound (key : M × (X × X)) : (hashQ (n := n) key).IsQueryBoundP p cH := by
  unfold hashQ
  rw [isQueryBoundP_query_iff]
  exact hH key

include hS in
theorem signQ_bound (msg : M) :
    (liftM ((RomSpec n X M).query (.inr msg)) : OracleComp (RomSpec n X M) _).IsQueryBoundP p
      cS := by
  rw [isQueryBoundP_query_iff]
  exact hS msg

include hU in
theorem unifQ_bound (k : ℕ) :
    (liftM ((RomSpec n X M).query (.inl (.inl k))) :
      OracleComp (RomSpec n X M) _).IsQueryBoundP p 0 := by
  rw [isQueryBoundP_query_iff]
  exact fun h => absurd h (hU k)

include hU in
theorem romLift_bound {α : Type} (x : ProbComp α) :
    (liftM x : OracleComp (RomSpec n X M) α).IsQueryBoundP p 0 := by
  induction x using OracleComp.inductionOn with
  | pure a => simp
  | query_bind k next ih =>
    have hb : (liftM (liftM (unifSpec.query k) >>= next) : OracleComp (RomSpec n X M) α) =
        (liftM (unifSpec.query k) : OracleComp (RomSpec n X M) _) >>= fun u => liftM (next u) := by
      simp
      rfl
    rw [hb]
    exact isQueryBoundP_bind (n := 0) (m := 0) (unifQ_bound p hU k) fun u _ => ih u

/-- The cost of one oracle call of the forger: `cH` for a challenge query,
`cS + cH` for a signing request, nothing otherwise. -/
def callCost (t : (RomForgerSpec n E X M).Domain) : ℕ :=
  (if isChalCall t = true then cH else 0) + (if isSignCall t = true then cS + cH else 0)

include hU hH hS in
theorem romHandler_bound (pk : X) (t : (RomForgerSpec n E X M).Domain) (st : Core n X M)
    (c : (AnnSpec n X M).QueryCache) :
    (((romHandler C pk t).run st).run c).IsQueryBoundP p (callCost cH cS t) := by
  rcases t with key | ⟨⟨data, groups⟩, coeffs⟩
  · have h : ((romHandler (E := E) C pk (.inl key)).run st).run c =
        (hashQ (n := n) key >>= fun e => pure ((e, st), c)) := by
      simp [romHandler, map_eq_bind_pure_comp]
    rw [h]
    exact (isQueryBoundP_bind (m := 0) (hashQ_bound p cH hH key)
      fun _ _ => isQueryBoundP_pure _ _ _).mono (by simp [callCost, isChalCall, isSignCall])
  · cases data with
    | random k =>
      rw [rom_run_random]
      exact (isQueryBoundP_bind (n := 0) (m := 0) (unifQ_bound p hU k)
        fun _ _ => isQueryBoundP_pure _ _ _).mono (by simp)
    | rand ms tail =>
      rw [rom_run_rand]
      exact (isQueryBoundP_bind (n := 0) (m := 0) (romLift_bound p hU _)
        fun _ _ => isQueryBoundP_pure _ _ _).mono (by simp)
    | sign msg =>
      rw [rom_run_sign]
      exact (isQueryBoundP_bind (signQ_bound p cS hS msg) fun sig _ =>
        isQueryBoundP_bind (m := 0) (hashQ_bound p cH hH _)
          fun _ _ => isQueryBoundP_pure _ _ _).mono
        (by simp [callCost, isChalCall, isSignCall, isSign])

include hU hH hS in
/-- The forger's run costs `cH` per challenge query and `cS + cH` per signing
request. -/
theorem rom_stack_bound (pk : X) {Result : Type}
    (prog : OracleComp (RomForgerSpec n E X M) Result) (a b : ℕ)
    (ha : prog.IsQueryBoundP (fun t => isChalCall t) a)
    (hb : prog.IsQueryBoundP (fun t => isSignCall t) b)
    (st : Core n X M) (c : (AnnSpec n X M).QueryCache) :
    (((simulateQ (romHandler C pk) prog).run st).run c).IsQueryBoundP p
      (a * cH + b * (cS + cH)) := by
  induction prog using OracleComp.inductionOn generalizing a b st c with
  | pure x => simp
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at ha hb
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    refine (isQueryBoundP_bind (romHandler_bound C p cH cS hU hH hS pk t st c) fun y _ =>
      ih y.1.1 _ _ (ha.2 y.1.1) (hb.2 y.1.1) y.1.2 y.2).mono ?_
    unfold callCost
    by_cases h1 : isChalCall t = true <;> by_cases h2 : isSignCall t = true
    · rcases t with key | t <;> simp [isChalCall, isSignCall] at h1 h2
    · obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.pos_iff_ne_zero.mp (ha.1.resolve_left (not_not.mpr h1)))
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Nat.succ_sub_one, Nat.succ_mul]
      omega
    · obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.pos_iff_ne_zero.mp (hb.1.resolve_left (not_not.mpr h2)))
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Nat.succ_sub_one, Nat.succ_mul]
      omega
    · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
      omega

end Bound

/-- Every output of the forger's run under `romHandler` is an output of the
forger. -/
theorem rom_support (pk : X) {Result : Type}
    (prog : OracleComp (RomForgerSpec n E X M) Result) (st : Core n X M)
    (c : (AnnSpec n X M).QueryCache) :
    ∀ z ∈ support (((simulateQ (romHandler C pk) prog).run st).run c), z.1.1 ∈ support prog := by
  induction prog using OracleComp.inductionOn generalizing st c with
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
    exact (mem_support_bind_iff _ _ _).mpr ⟨y.1.1, mem_support_query _ y.1.1, ih _ _ _ z hz⟩

/-! ## The whole reduction -/

section Main

variable (p : (RomSpec n X M).Domain → Prop) [DecidablePred p] (cH cS : ℕ)
  (hU : ∀ k, ¬ p (.inl (.inl k))) (hH : ∀ key, p (.inl (.inr key)) → 0 < cH)
  (hS : ∀ m, p (.inr m) → 0 < cS)

include hU in
theorem zsRom_bound (items : List (AItem n X M)) (is : List ℕ)
    (c : (AnnSpec n X M).QueryCache) :
    ((is.mapM fun i => if i = 0 then pure 1 else romTableRO (items.take (i + 1)) :
      StateT (AnnSpec n X M).QueryCache (OracleComp (RomSpec n X M)) _).run
        c).IsQueryBoundP p 0 := by
  induction is generalizing c with
  | nil => simp
  | cons i is ih =>
    rw [List.mapM_cons]
    simp only [StateT.run_bind, StateT.run_pure]
    refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun y _ =>
      isQueryBoundP_bind (n := 0) (m := 0) (ih y.2) fun _ _ => isQueryBoundP_pure _ _ _
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · rw [romTableRO_run]
      exact romLift_bound p hU _

include hH in
theorem esRom_bound (items : List (AItem n X M)) :
    (items.mapM fun a => hashQ (n := n) (a.m, (a.r, a.pk))).IsQueryBoundP p
      (items.length * cH) := by
  induction items with
  | nil => simp
  | cons a items ih =>
    rw [List.mapM_cons]
    refine (isQueryBoundP_bind (hashQ_bound p cH hH _) fun _ _ =>
      isQueryBoundP_bind (m := 0) ih fun _ _ => isQueryBoundP_pure _ _ _).mono ?_
    simp only [List.length_cons, Nat.succ_mul]
    omega

include hH in
theorem extractROM_bound [Inhabited M] (pk : X) (items : List (AItem n X M)) (s : ZMod n)
    (zs : List (ZMod n)) (signed : List M) (es : List (ZMod n)) :
    (extractROM C pk items s zs signed es).IsQueryBoundP p cH := by
  unfold extractROM
  split
  · exact isQueryBoundP_pure _ _ _
  · split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_bind (m := 0) (hashQ_bound p cH hH _)
        fun _ _ => isQueryBoundP_pure _ _ _

theorem reductionROM_main_eq [Inhabited M] (F : RomForger n E X M) (P : Stmt C) :
    (reductionROM C F).main P = (do
      let r ← ((simulateQ (romHandler C (C.x P.1))
        (F.main (initial C ((C.liftX (C.x P.1)).getD 0)))).run Core.init).run ∅
      let q ← ((List.range (finalItems C r.1.1 r.1.2).length).mapM fun i =>
        if i = 0 then pure 1 else romTableRO ((finalItems C r.1.1 r.1.2).take (i + 1))).run r.2
      let es ← (finalItems C r.1.1 r.1.2).mapM fun a => hashQ (n := n) (a.m, (a.r, a.pk))
      extractROM C (C.x P.1) (finalItems C r.1.1 r.1.2) r.1.1.value.data.s q.1 r.1.2.signed
        es) := rfl

include hU hH hS in
/-- The reduction's cost for a forger with at most `qH` challenge queries, `qS`
signing requests and forgeries of at most `ℓ` items. -/
theorem reductionROM_cost [Inhabited M] (F : RomForger n E X M) (qH qS ℓ : ℕ)
    (hFH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hFS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (P : Stmt C) :
    ((reductionROM C F).main P).IsQueryBoundP p
      (qH * cH + qS * (cS + cH) + (ℓ * cH + cH)) := by
  rw [reductionROM_main_eq]
  refine isQueryBoundP_bind (rom_stack_bound C p cH cS hU hH hS _ _ qH qS (hFH _) (hFS _) _ _)
    fun r hr => ?_
  have hlen : (finalItems C r.1.1 r.1.2).length ≤ ℓ := by
    simp only [finalItems, annotate_length]
    exact (toItems_length_le C _ _).trans (hL _ _ (rom_support C _ _ _ _ r hr))
  refine (isQueryBoundP_bind (n := 0) (zsRom_bound p hU _ _ _) fun q _ =>
    isQueryBoundP_bind (esRom_bound p cH hH _) fun es _ =>
      extractROM_bound C p cH hH _ _ _ _ _ _).mono ?_
  have := Nat.mul_le_mul_right cH hlen
  omega

end Main

/-- **The oracle reduction's query counts**, in the form
`Taproot.BIP340Security.euf_cma` asks for. -/
theorem reductionROM_bound [Inhabited M] (F : RomForger n E X M) (qH qS ℓ : ℕ)
    (hFH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hFS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (P : Stmt C) :
    FiatShamir.signHashQueryBound (M := M) (Commit := X × X) (Chal := ZMod n)
      (S' := FSSig n X) (oa := (reductionROM C F).main P) qS (qH + qS + ℓ + 1) := by
  refine ⟨?_, ?_⟩
  · refine (reductionROM_cost C _ 0 1 (by simp) (by simp) (by simp) F qH qS ℓ hFH hFS hL P).mono
      (by omega)
  · refine (reductionROM_cost C _ 1 0 (by simp) (by simp) (by simp) F qH qS ℓ hFH hFS hL P).mono
      (by omega)

/-! ## The forger with its challenge queries answered from a table -/

theorem at_queries (F : RomForger n E X M) (q : ℕ)
    (h : ∀ input, (F.main input).IsQueryBoundP (fun t => isRandCall t) q)
    (g : M × (X × X) → ZMod n) (input : Message Unit (Pts E)) :
    ((F.at g).main input).IsQueryBoundP (fun r => isRand r.value.data) q := by
  refine IsQueryBoundP.simulateQ_of_step (h input) (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with key | t
    · simp [isRandCall] at ht
    · simp only [answerChal]
      rw [isQueryBoundP_query_iff]
      exact fun _ => Nat.one_pos
  · rcases t with key | t
    · exact isQueryBoundP_pure _ _ _
    · simp only [answerChal]
      rw [isQueryBoundP_query_iff]
      exact fun h' => absurd h' ht

end Halfagg.Security
