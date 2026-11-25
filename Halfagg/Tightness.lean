import Halfagg.Unforgeability

/-!
# The bound of `halfagg_unforgeable` is tight in `q`

`grinder q` is an algebraic forger that makes no signing requests and at most
`q` randomizer requests. `grinder_advantage`: it wins the standard game with
probability at least `1 - ((n - 1)/n)^q`, which is about `q/n`. So the additive
term of `halfagg_unforgeable`, which is `(q + 1)/n` here, is tight up to one
query, unless BIP340 can be forged without signing queries.

This file is in the uniform model: the randomizer hash answers in `ZMod n` and
`red` is the identity.

The forger uses the target key's point `P*` as every nonce: the item
`(x(P*), pk*, m)` contributes `P* + e⋅P* = (1 + e)⋅P*` to the verification
equation. If `1 + e = 0` for some message, that item alone verifies with `s = 0`
(and is a BIP340 forgery). Otherwise the forger fixes the first item with message
`0` and tries the second items with messages `1, …, q`: a randomizer `z` with
`(1 + e₀) + z⋅(1 + eⱼ) = 0` makes the two-item aggregate verify with `s = 0`, and
each try finds one with probability `1/n`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] (C : Curve n E X) (challenge : X → X → ℕ → ZMod n)

/-- `1 + e` for the item `(pk, pk, m)`: with `R = P`, the item's term is
`P + e⋅P = (1 + e)⋅P`. -/
def gβ (pk : X) (m : ℕ) : ZMod n := 1 + challenge pk pk m

/-- `k` copies of the second received point, the target key's point `P*`. -/
def copies (b : Groups (Pts E)) (k : ℕ) : (s : Unit) → List (Fin (b s).length → ZMod n) :=
  fun _ => List.replicate k fun i => if i.val = 1 then 1 else 0

/-- Try the second items with messages `j + 1, …, j + k`. -/
def grindLoop (pk : X) : (k j : ℕ) → (b : Groups (Pts E)) →
    OracleComp (explainedSpec (ZMod n) (Pts E) (Request X ℕ) (Reply n (ZMod n) X ℕ))
      (Explained (ZMod n) (Out n ℕ) (Pts E))
  | 0, _, b => pure (Explained.ofVectors b ⟨[], 0⟩ (copies b 0))
  | k + 1, j, b =>
    OracleComp.queryBind
      (spec := explainedSpec (ZMod n) (Pts E) (Request X ℕ) (Reply n (ZMod n) X ℕ))
      (Explained.ofVectors b (Request.rand [0, j + 1] []) (copies b 4)) fun rep =>
    let z : ZMod n := rep.data
    if gβ challenge pk 0 + z * gβ challenge pk (j + 1) = 0 then
      pure (Explained.ofVectors (extend b rep.groups) ⟨[0, j + 1], 0⟩ (copies _ 4))
    else grindLoop pk k (j + 1) (extend b rep.groups)

theorem grindLoop_algebraic (pk : X) (k j : ℕ) (b : Groups (Pts E)) :
    IsAlgebraic b (grindLoop (E := E) challenge pk k j b) := by
  induction k generalizing j b with
  | zero => exact Explained.valid_ofVectors _ _ _
  | succ k ih =>
    refine ⟨Explained.valid_ofVectors _ _ _, fun rep => ?_⟩
    dsimp only
    split_ifs
    · exact Explained.valid_ofVectors _ _ _
    · exact ih _ _

/-- The grinding forger. -/
def grinder (q : ℕ) : AlgForger n (ZMod n) E X ℕ where
  main input :=
    let pk := C.x ((input.groups ()).getD 1 0)
    match (List.range (q + 1)).find? (fun m => gβ challenge pk m == 0) with
    | some m => pure (Explained.ofVectors input.groups ⟨[m], 0⟩ (copies _ 2))
    | none => grindLoop challenge pk q 0 input.groups
  algebraic input := by
    dsimp only
    split
    · exact Explained.valid_ofVectors _ _ _
    · exact grindLoop_algebraic challenge _ _ _ _

/-! ## Winning transcripts -/

section Wins

variable {d : ZMod n} (hd : d ≠ 0)
include hd

set_option linter.flexible false in
theorem wins_one (m : ℕ) (hm : gβ challenge (C.x (C.mulG d)) m = 0) :
    aggWins C challenge (C.x (C.mulG d)) [(C.x (C.mulG d), C.x (C.mulG d), m)] 0 [1]
      (fun m => ([] : List ℕ).contains m) = true := by
  have hP := C.liftX_x_mulG hd
  have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
  simp [aggWins, verifyWith, items, lifts, term, hP, C.val_smul_mulG, ZMod.val_one]
  simp only [← map_add]
  rw [← map_zero C.mulG]
  congr 1
  unfold gβ at hm
  linear_combination -(C.evenScalar d) * hm

set_option linter.flexible false in
theorem wins_two (j : ℕ) (z : ZMod n)
    (hz : gβ challenge (C.x (C.mulG d)) 0 + z * gβ challenge (C.x (C.mulG d)) (j + 1) = 0) :
    aggWins C challenge (C.x (C.mulG d))
      [(C.x (C.mulG d), C.x (C.mulG d), 0), (C.x (C.mulG d), C.x (C.mulG d), j + 1)] 0 [1, z]
      (fun m => ([] : List ℕ).contains m) = true := by
  have hP := C.liftX_x_mulG hd
  have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
  simp [aggWins, verifyWith, items, lifts, term, hP, C.val_smul_mulG, ZMod.val_one]
  simp only [← map_add]
  rw [← map_zero C.mulG]
  congr 1
  unfold gβ at hz
  linear_combination -(C.evenScalar d) * hz

end Wins

theorem evalP (G P : E) :
    evaluate (List.ofFn fun i : Fin 2 => if i.val = 1 then (1 : ZMod n) else 0) [G, P] = P := by
  have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
  have h : (List.ofFn fun i : Fin 2 => if i.val = 1 then (1 : ZMod n) else 0) = [0, 1] := by
    simp [List.ofFn_succ]
  rw [h]
  simp only [evaluate, List.mapIdx_cons, List.mapIdx_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.sum_cons, List.sum_nil, add_zero]
  change (0 : ZMod n).val • G + (1 : ZMod n).val • P = P
  simp [ZMod.val_one]

theorem pr_ne (t : ZMod n) :
    Pr{let u ← $ᵗ (ZMod n)}[u ≠ t] = ((n - 1 : ℕ) : ℝ≥0∞) / n := by
  have : NeZero n := ⟨(Fact.out : n.Prime).ne_zero⟩
  rw [SampleableType.prEvent_uniformSample, ZMod.card, Finset.filter_ne' Finset.univ t,
    Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ, ZMod.card]

/-! ## The grinding loop loses with probability at most `((n - 1)/n)^k` -/

/-- The oracle key of the try with second message `j + 1`. -/
def gKey (pk : X) (j : ℕ) : List (Item X ℕ) := [(pk, pk, 0), (pk, pk, j + 1)]

/-- The erased forger's output. -/
def eraseOut (out : Explained (ZMod n) (Out n ℕ) (Pts E)) : List (Item X ℕ) × ZMod n :=
  (toItems C out.value.data.ms (out.value.groups ()), out.value.data.s)

section Loop

variable {d : ZMod n} (hd : d ≠ 0)

theorem groups_copies {D : Type} (data : D) (k : ℕ) :
    (Explained.ofVectors (F := ZMod n) (G := Pts E)
      (fun _ => [C.G, C.mulG (C.evenScalar d)]) data
        (copies (fun _ => [C.G, C.mulG (C.evenScalar d)]) k)).value.groups () =
      List.replicate k (C.mulG (C.evenScalar d)) := by
  simp only [Explained.ofVectors, copies, List.map_replicate]
  congr 1
  exact evalP _ _

theorem items_two {D : Type} (data : D) (j : ℕ) :
    toItems C [0, j + 1] ((Explained.ofVectors (F := ZMod n) (G := Pts E)
      (fun _ => [C.G, C.mulG (C.evenScalar d)]) data
        (copies (fun _ => [C.G, C.mulG (C.evenScalar d)]) 4)).value.groups ()) =
      gKey (C.x (C.mulG d)) j := by
  rw [groups_copies]
  simp [toItems, pairs, List.replicate, C.x_evenScalar, gKey]

theorem items_one {D : Type} (data : D) (m : ℕ) :
    toItems C [m] ((Explained.ofVectors (F := ZMod n) (G := Pts E)
      (fun _ => [C.G, C.mulG (C.evenScalar d)]) data
        (copies (fun _ => [C.G, C.mulG (C.evenScalar d)]) 2)).value.groups ()) =
      [(C.x (C.mulG d), C.x (C.mulG d), m)] := by
  rw [groups_copies]
  simp [toItems, pairs, List.replicate, C.x_evenScalar]

/-- One try: a fresh uniform randomizer, then success or the next try. -/
theorem grind_step [NonceGen n ℕ] (sk : ZMod n) (k j : ℕ) (c : (RandSpec (ZMod n) X ℕ).QueryCache)
    (hc : c (gKey (C.x (C.mulG d)) j) = none) :
    gRun C challenge (C.x (C.mulG d)) sk (eraseOut C <$> simulateQ (fun q => eraseImpl C q.value)
        (grindLoop challenge (C.x (C.mulG d)) (k + 1) j
          (fun _ => [C.G, C.mulG (C.evenScalar d)]))) [] c =
      (($ᵗ (ZMod n) : ProbComp (ZMod n)) >>= fun u =>
        if gβ challenge (C.x (C.mulG d)) 0 + u * gβ challenge (C.x (C.mulG d)) (j + 1) = 0 then
          pure (((gKey (C.x (C.mulG d)) j, (0 : ZMod n)), ([] : List ℕ)),
            c.cacheQuery (gKey (C.x (C.mulG d)) j) u)
        else
          gRun C challenge (C.x (C.mulG d)) sk
            (eraseOut C <$> simulateQ (fun q => eraseImpl C q.value)
              (grindLoop challenge (C.x (C.mulG d)) k (j + 1)
                (fun _ => [C.G, C.mulG (C.evenScalar d)]))) []
            (c.cacheQuery (gKey (C.x (C.mulG d)) j) u)) := by
  rw [grindLoop]
  have e : ∀ {α : Type}
      (t : (explainedSpec (ZMod n) (Pts E) (Request X ℕ) (Reply n (ZMod n) X ℕ)).Domain)
      (f : _ → OracleComp (explainedSpec (ZMod n) (Pts E) (Request X ℕ) (Reply n (ZMod n) X ℕ)) α),
      OracleComp.queryBind t f =
        (liftM ((explainedSpec (ZMod n) (Pts E) (Request X ℕ) (Reply n (ZMod n) X ℕ)).query t) >>=
          f) :=
    fun _ _ => rfl
  rw [e]
  simp only [simulateQ_bind, simulateQ_spec_query, map_bind, gRun_bind]
  have hq := g_rand C challenge (C.x (C.mulG d)) sk
    (Explained.ofVectors (F := ZMod n) (G := Pts E) (fun _ => [C.G, C.mulG (C.evenScalar d)])
      (Request.rand (X := X) [0, j + 1] [])
      (copies (fun _ => [C.G, C.mulG (C.evenScalar d)]) 4)).value.groups [0, j + 1] [] [] c
  rw [items_two] at hq
  have hq' : gRun C challenge (C.x (C.mulG d)) sk (eraseImpl C
      (Explained.ofVectors (F := ZMod n) (G := Pts E) (fun _ => [C.G, C.mulG (C.evenScalar d)])
        (Request.rand (X := X) [0, j + 1] [])
        (copies (fun _ => [C.G, C.mulG (C.evenScalar d)]) 4)).value) [] c =
      (fun p => ((⟨p.1, fun _ => []⟩, []), p.2)) <$>
        ((RandSpec (ZMod n) X ℕ).randomOracle (gKey (C.x (C.mulG d)) j)).run c := hq
  rw [hq', randomOracle.run_eq]
  simp only [hc, map_bind, map_pure, bind_assoc, pure_bind]
  refine bind_congr (m := ProbComp) fun u => ?_
  split_ifs with h
  · simp only [simulateQ_pure, map_pure, gRun_pure, eraseOut]
    refine congrArg pure (Prod.ext (Prod.ext (Prod.ext ?_ rfl) rfl) rfl)
    exact items_two C (⟨[0, j + 1], 0⟩ : Out n ℕ) j
  · rfl

set_option linter.flexible false in
include hd in
/-- After a successful try, the verifier reads the same randomizer and accepts. -/
theorem finish_two (j : ℕ) (u : ZMod n) (c : (RandSpec (ZMod n) X ℕ).QueryCache)
    (hz : gβ challenge (C.x (C.mulG d)) 0 + u * gβ challenge (C.x (C.mulG d)) (j + 1) = 0) :
    finish C challenge id (C.x (C.mulG d))
      (((gKey (C.x (C.mulG d)) j, (0 : ZMod n)), ([] : List ℕ)),
        c.cacheQuery (gKey (C.x (C.mulG d)) j) u) = pure true := by
  have hw := wins_two C challenge hd j u hz
  have hr : List.range (gKey (C.x (C.mulG d)) j).length = [0, 1] := rfl
  have ht : (gKey (C.x (C.mulG d)) j).take 2 = gKey (C.x (C.mulG d)) j := rfl
  unfold finish
  simp only [hr, List.mapM_cons, List.mapM_nil, zQuery]
  simp [gKey] at hw ⊢
  exact hw

set_option linter.flexible false in
include hd in
/-- A single item with `1 + e = 0` is accepted. -/
theorem finish_one (m : ℕ) (c : (RandSpec (ZMod n) X ℕ).QueryCache)
    (hm : gβ challenge (C.x (C.mulG d)) m = 0) :
    finish C challenge id (C.x (C.mulG d))
      ((([(C.x (C.mulG d), C.x (C.mulG d), m)], (0 : ZMod n)), ([] : List ℕ)), c) = pure true := by
  have hw := wins_one C challenge hd m hm
  unfold finish
  simp only [List.length_singleton, List.range_one, List.mapM_cons, List.mapM_nil, zQuery]
  simp at hw ⊢
  exact hw

theorem gKey_ne (pk : X) {i j : ℕ} (h : i ≠ j) : gKey pk i ≠ gKey pk j := by
  simp [gKey, h]

include hd in
/-- **The loop loses with probability at most `((n - 1)/n)^k`**, if the keys of
its `k` tries are fresh and none of their coefficients vanishes. -/
theorem grind_loss [NonceGen n ℕ] (sk : ZMod n) (k j : ℕ) (c : (RandSpec (ZMod n) X ℕ).QueryCache)
    (hc : ∀ i, j ≤ i → c (gKey (C.x (C.mulG d)) i) = none)
    (hβ : ∀ i, j ≤ i → i < j + k → gβ challenge (C.x (C.mulG d)) (i + 1) ≠ 0) :
    Pr{let b ← (gRun C challenge (C.x (C.mulG d)) sk
        (eraseOut C <$> simulateQ (fun q => eraseImpl C q.value)
          (grindLoop challenge (C.x (C.mulG d)) k j
            (fun _ => [C.G, C.mulG (C.evenScalar d)]))) [] c >>=
        finish C challenge id (C.x (C.mulG d)))}[b = false] ≤
      (((n - 1 : ℕ) : ℝ≥0∞) / n) ^ k := by
  induction k generalizing j c with
  | zero => rw [pow_zero]; exact prEvent_le_one _
  | succ k ih =>
    have hβj := hβ j le_rfl (by omega)
    rw [grind_step C challenge sk k j c (hc j le_rfl), bind_assoc, pow_succ']
    have hiff : ∀ u : ZMod n,
        gβ challenge (C.x (C.mulG d)) 0 + u * gβ challenge (C.x (C.mulG d)) (j + 1) = 0 ↔
          u = -(gβ challenge (C.x (C.mulG d)) 0) / gβ challenge (C.x (C.mulG d)) (j + 1) := by
      intro u
      rw [eq_div_iff hβj]
      constructor <;> intro h <;> linear_combination h
    refine (prEvent_bind_le_prEvent_mul_of_forall_le _ _
      (fun u => u ≠ -(gβ challenge (C.x (C.mulG d)) 0) / gβ challenge (C.x (C.mulG d)) (j + 1))
      _ (ε := (((n - 1 : ℕ) : ℝ≥0∞) / n) ^ k) (fun u hu => ?_) (fun u hu => ?_)).trans
      (le_of_eq (by rw [pr_ne]))
    · have hne : ¬ (gβ challenge (C.x (C.mulG d)) 0 +
          u * gβ challenge (C.x (C.mulG d)) (j + 1) = 0) := fun h => hu ((hiff u).mp h)
      simp only [hne, ↓reduceIte]
      refine ih (j + 1) _ (fun i hi => ?_) (fun i hi hi' => hβ i (by omega) (by omega))
      rw [QueryCache.cacheQuery_of_ne _ _ (gKey_ne _ (by omega))]
      exact hc i (by omega)
    · have heq := (hiff u).mpr (not_not.mp hu)
      simp only [heq, ↓reduceIte, pure_bind]
      rw [finish_two C challenge hd j u c heq]
      simp

include hd in
/-- After key generation with secret key `d`, the forger loses with probability
at most `((n - 1)/n)^q`. -/
theorem grinder_loss_key [NonceGen n ℕ] (q : ℕ) :
    Pr{let b ← (gRun C challenge (C.x (C.mulG d)) d
        ((erase C (grinder C challenge q)).main (C.x (C.mulG d))) [] ∅ >>=
        finish C challenge id (C.x (C.mulG d)))}[b = false] ≤ (((n - 1 : ℕ) : ℝ≥0∞) / n) ^ q := by
  have hP : (C.liftX (C.x (C.mulG d))).getD 0 = C.mulG (C.evenScalar d) := by
    rw [C.liftX_x_mulG hd]; rfl
  have hmain : (erase C (grinder C challenge q)).main (C.x (C.mulG d)) =
      eraseOut C <$> simulateQ (fun q => eraseImpl C q.value)
        ((grinder C challenge q).main (initial C (C.mulG (C.evenScalar d)))) := by
    rw [← hP]; rfl
  have hpk : C.x (((initial C (C.mulG (C.evenScalar d))).groups ()).getD 1 0) = C.x (C.mulG d) := by
    simp [initial, C.x_evenScalar]
  rw [hmain]
  simp only [grinder, hpk]
  split
  · next m hfind =>
    have hm : gβ challenge (C.x (C.mulG d)) m = 0 := by
      simpa using List.find?_some hfind
    simp only [simulateQ_pure, map_pure, gRun_pure, pure_bind, eraseOut]
    have hfin : finish C challenge id (C.x (C.mulG d))
        (((toItems C [m] ((Explained.ofVectors (F := ZMod n) (G := Pts E)
          (fun _ => [C.G, C.mulG (C.evenScalar d)]) (⟨[m], 0⟩ : Out n ℕ)
          (copies (fun _ => [C.G, C.mulG (C.evenScalar d)]) 2)).value.groups ()), (0 : ZMod n)),
          ([] : List ℕ)), ∅) = pure true := by
      rw [items_one]
      exact finish_one C challenge hd m ∅ hm
    refine (le_of_eq (congrArg (fun mx : ProbComp Bool => Pr{let b ← mx}[b = false]) hfin)).trans ?_
    simp
  · next hfind =>
    refine grind_loss C challenge hd d q 0 ∅ (fun i _ => rfl) fun i _ hi => ?_
    have := List.find?_eq_none.mp hfind (i + 1) (List.mem_range.mpr (by omega))
    simpa using this

end Loop

/-- **The bound is tight in `q`.** The grinding forger makes no signing requests
and at most `q` randomizer requests, and wins the standard game with probability
at least `1 - ((n - 1)/n)^q`. -/
theorem grinder_advantage [NonceGen n ℕ] (q : ℕ) :
    1 - (((n - 1 : ℕ) : ℝ≥0∞) / n) ^ q ≤
      aggAdvantage C challenge id (erase C (grinder C challenge q)) := by
  have hloss : Pr{let b ← (simulateQ (RandSpec (ZMod n) X ℕ).romImpl
      (aggExperiment C challenge id (erase C (grinder C challenge q)))).run' ∅}[b = false] ≤
      (((n - 1 : ℕ) : ℝ≥0∞) / n) ^ q := by
    rw [game_form C challenge id]
    refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun ks hks => ?_
    have hk : ks.2 ≠ 0 ∧ ks.1 = C.x (C.mulG ks.2) := by
      have h' : ks ∈ support (do
          let d ← $ᵗ (NonzeroScalar n)
          return (C.x (C.mulG d.1), d.1) : ProbComp (X × ZMod n)) := hks
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h'
      obtain ⟨d, -, rfl⟩ := h'
      exact ⟨d.2, rfl⟩
    obtain ⟨pk, sk⟩ := ks
    dsimp only at hk ⊢
    obtain ⟨hne, rfl⟩ := hk
    exact grinder_loss_key C challenge hne q
  unfold aggAdvantage
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton]
  have htot := prEvent_add_prEvent_not_eq_prEvent_true
    ((simulateQ (RandSpec (ZMod n) X ℕ).romImpl
      (aggExperiment C challenge id (erase C (grinder C challenge q)))).run' ∅) (fun b => b = true)
  rw [OracleComp.prEvent_true_eq_one] at htot
  simp only [Bool.not_eq_true] at htot
  rw [← htot]
  refine (tsub_le_tsub_left hloss _).trans (le_of_eq ?_)
  exact ENNReal.add_sub_cancel_right (ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _))

end Halfagg.Security

/-! ## The forger's query counts, and the theorem applied to it -/

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] (C : Curve n E X) (challenge : X → X → ℕ → ZMod n)

theorem queryBind_eq {α : Type}
    (t : (explainedSpec (ZMod n) (Pts E) (Request X ℕ) (Reply n (ZMod n) X ℕ)).Domain)
    (f : _ → OracleComp (explainedSpec (ZMod n) (Pts E) (Request X ℕ) (Reply n (ZMod n) X ℕ)) α) :
    OracleComp.queryBind t f =
      (liftM ((explainedSpec (ZMod n) (Pts E) (Request X ℕ) (Reply n (ZMod n) X ℕ)).query t) >>=
        f) := rfl

theorem grindLoop_queries (pk : X) (k j : ℕ) (b : Groups (Pts E)) :
    (grindLoop (E := E) challenge pk k j b).IsQueryBoundP (fun r => isRand r.value.data) k := by
  induction k generalizing j b with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ k ih =>
    rw [grindLoop, queryBind_eq]
    refine (isQueryBoundP_query_bind_iff
      (fun r : Explained (ZMod n) (Request X ℕ) (Pts E) => isRand r.value.data = true) _ _ _).mpr
      ⟨Or.inr (Nat.succ_pos k), fun rep => ?_⟩
    have hr : isRand (Explained.ofVectors (F := ZMod n) b (Request.rand (X := X) [0, j + 1] [])
        (copies b 4)).value.data = true := rfl
    simp only [hr, ↓reduceIte, Nat.add_sub_cancel]
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact ih _ _

theorem grindLoop_signs (pk : X) (p : ℕ → Bool) (k j : ℕ) (b : Groups (Pts E)) :
    (grindLoop (E := E) challenge pk k j b).IsQueryBoundP (fun r => isSign p r.value.data) 0 := by
  induction k generalizing j b with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ k ih =>
    rw [grindLoop, queryBind_eq]
    refine (isQueryBoundP_query_bind_iff
      (fun r : Explained (ZMod n) (Request X ℕ) (Pts E) => isSign p r.value.data = true) _ _ _).mpr
      ⟨Or.inl (fun h => Bool.noConfusion h), fun rep => ?_⟩
    have hr : isSign p (Explained.ofVectors (F := ZMod n) b (Request.rand (X := X) [0, j + 1] [])
        (copies b 4)).value.data = false := rfl
    simp only [hr, Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact ih _ _

theorem grinder_queries (q : ℕ) : ∀ input,
    ((grinder C challenge q).main input).IsQueryBoundP (fun r => isRand r.value.data) q := by
  intro input
  simp only [grinder]
  split
  · exact isQueryBoundP_pure _ _ _
  · exact grindLoop_queries challenge _ _ _ _

theorem grinder_signs (q : ℕ) (p : ℕ → Bool) : ∀ input,
    ((grinder C challenge q).main input).IsQueryBoundP (fun r => isSign p r.value.data) 0 := by
  intro input
  simp only [grinder]
  split
  · exact isQueryBoundP_pure _ _ _
  · exact grindLoop_signs challenge _ _ _ _ _

/-- The main theorem applied to the grinding forger: its reduction is a BIP340
forger that wins with probability at least `1 - ((n - 1)/n)^q - (q + 1)/n`. -/
theorem grinder_sandwich [NonceGen n ℕ] (hx0 : C.liftX (C.x 0) = none) (q : ℕ) :
    1 - (((n - 1 : ℕ) : ℝ≥0∞) / n) ^ q ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (reduction C challenge id (grinder C challenge q)) + ((q : ℕ) + 1 : ℝ≥0∞) / n := by
  rw [div_eq_mul_inv]
  exact (grinder_advantage C challenge q).trans
    (halfagg_unforgeable C challenge id hx0 (grinder C challenge q) q
      (grinder_queries C challenge q) _ (id_bound n))

/-- That reduction makes no signing queries. -/
theorem grinder_reduction_no_sign [NonceGen n ℕ] (q : ℕ) (pk : X) :
    ((reduction C challenge id (grinder C challenge q)).main pk).IsQueryBoundP
      (fun t => isSignQuery (fun _ => true) t) 0 :=
  reduction_sign_queries C challenge id (grinder C challenge q) (fun _ => true) 0
    (grinder_signs C challenge q _) pk

end Halfagg.Security
