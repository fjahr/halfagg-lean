import Halfagg.Tightness
import Halfagg.Knowledge
import Halfagg.UnforgeabilityTight

/-!
# The games can be won

A bound on a forger's success says nothing if no forger can win the game at
all, and a mistake in a definition could make a game impossible to win. This
file has a forger that wins with positive probability, for every randomizer
hash, every reduction of its outputs and every nonce derivation of the signer.

`bettor m₀` bets that the secret key is `1`. It sends the target key's point in
a randomizer request for the empty list and outputs the one-item aggregate
`(pk*, pk*, m₀)` with `s = (1 + e)⋅k`, where `k⋅G` is the even-y point of the
key `1`. If the secret key is `1`, this is a BIP340 signature on `m₀` with the
key's own point as nonce. It asks for no signature.

* `bettor_advantage_pos`: the bettor wins the standard game with positive
  probability, and `bettor_queries` is the hypothesis of `halfagg_unforgeable`
  for it.
* `bettor_verify_pos`: its aggregate verifies with positive probability in the
  game of `halfagg_knowledge`.
* `bettorRom_advantage_pos`: with the challenge hash as an oracle, `bettorRom`
  wins with positive probability. It explains its nonce
  (`bettorRom_explains`), as `halfagg_dlog_tight` asks.
* `bettor_bound`, `bettorRom_bound`: `halfagg_unforgeable` and
  `halfagg_dlog_tight` applied to these forgers.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)
variable [SampleableType H] (red : H → ZMod n)

/-- The forger that bets on the secret key `1`. Its nonce and its key are the
x-coordinate of the point in its randomizer request, the target key's point. -/
def bettor (m₀ : M) : AlgForger n H E X M where
  main input :=
    let req : Explained (ZMod n) (Request X M) (Pts E) :=
      Explained.ofVectors input.groups (Request.rand [] []) (copies input.groups 1)
    OracleComp.queryBind
      (spec := explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)) req fun rep =>
    let pk : X := C.x ((req.value.groups ()).headD 0)
    pure (Explained.ofVectors (extend input.groups rep.groups)
      (⟨[m₀], (1 + challenge pk pk m₀) * C.evenScalar 1⟩ : Out n M) (copies _ 2))
  algebraic _ :=
    ⟨Explained.valid_ofVectors _ _ _, fun _ => Explained.valid_ofVectors _ _ _⟩

/-! ## The bet pays if the secret key is `1` -/

set_option linter.flexible false in
/-- The bettor's aggregate verifies for the key `1`. -/
theorem wins_bet (m₀ : M) :
    aggWins C challenge (C.x (C.mulG 1)) [(C.x (C.mulG 1), C.x (C.mulG 1), m₀)]
      ((1 + challenge (C.x (C.mulG 1)) (C.x (C.mulG 1)) m₀) * C.evenScalar 1) [1]
      (fun m => ([] : List M).contains m) = true := by
  have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
  have hP := C.liftX_x_mulG (one_ne_zero (α := ZMod n))
  simp [aggWins, verifyWith, items, lifts, term, hP, C.val_smul_mulG, ZMod.val_one]
  simp only [← map_add]
  congr 1
  ring

theorem items_bet {D : Type} (data : D) (m₀ : M) :
    toItems C [m₀] ((Explained.ofVectors (F := ZMod n) (G := Pts E)
      (fun _ => [C.G, C.mulG (C.evenScalar 1)]) data
        (copies (fun _ => [C.G, C.mulG (C.evenScalar 1)]) 2)).value.groups ()) =
      [(C.x (C.mulG 1), C.x (C.mulG 1), m₀)] := by
  rw [groups_copies]
  simp [toItems, pairs, List.replicate, C.x_evenScalar]

/-- The x-coordinate of the point in the bettor's request is the public key of
the secret key `1`. -/
theorem key_bet {D : Type} (data : D) :
    C.x (((Explained.ofVectors (F := ZMod n) (G := Pts E)
      (fun _ => [C.G, C.mulG (C.evenScalar 1)]) data
        (copies (fun _ => [C.G, C.mulG (C.evenScalar 1)]) 1)).value.groups ()).headD 0) =
      C.x (C.mulG 1) := by
  rw [groups_copies]
  simp [List.replicate, C.x_evenScalar]

/-- The game's run of the bettor against the key `1`: one fresh randomizer for
the empty list, and then the bettor's aggregate. -/
theorem bet_run [NonceGen n M] (sk : ZMod n) (m₀ : M) :
    gRun C challenge (C.x (C.mulG 1)) sk
        ((erase C (bettor (H := H) C challenge m₀)).main (C.x (C.mulG 1))) [] ∅ =
      (($ᵗ H : ProbComp H) >>= fun u =>
        pure ((([(C.x (C.mulG 1), C.x (C.mulG 1), m₀)],
          (1 + challenge (C.x (C.mulG 1)) (C.x (C.mulG 1)) m₀) * C.evenScalar 1), ([] : List M)),
          (∅ : (RandSpec H X M).QueryCache).cacheQuery [] u)) := by
  have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
  have hP := C.liftX_x_mulG (one_ne_zero (α := ZMod n))
  have e : ∀ {α : Type}
      (t : (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)).Domain)
      (f : _ → OracleComp (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)) α),
      OracleComp.queryBind t f =
        (liftM ((explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)).query t) >>=
          f) :=
    fun _ _ => rfl
  have hinit : initial C ((C.liftX (C.x (C.mulG 1))).getD 0) =
      (⟨(), fun _ => [C.G, C.mulG (C.evenScalar 1)]⟩ : Message Unit (Pts E)) := by
    simp [initial, hP]
  simp only [erase]
  rw [hinit]
  simp only [bettor]
  rw [e]
  simp only [simulateQ_bind, simulateQ_spec_query, map_bind, gRun_bind]
  have hq := g_rand C challenge (C.x (C.mulG 1)) sk
    (Explained.ofVectors (F := ZMod n) (G := Pts E) (fun _ => [C.G, C.mulG (C.evenScalar 1)])
      (Request.rand (X := X) (M := M) [] [])
      (copies (fun _ => [C.G, C.mulG (C.evenScalar 1)]) 1)).value.groups [] [] []
      (∅ : (RandSpec H X M).QueryCache)
  have hq' : gRun C challenge (C.x (C.mulG 1)) sk (eraseImpl C
      (Explained.ofVectors (F := ZMod n) (G := Pts E) (fun _ => [C.G, C.mulG (C.evenScalar 1)])
        (Request.rand (X := X) (M := M) [] [])
        (copies (fun _ => [C.G, C.mulG (C.evenScalar 1)]) 1)).value) [] ∅ =
      (fun p => ((⟨p.1, fun _ => []⟩, []), p.2)) <$>
        ((RandSpec H X M).randomOracle []).run ∅ := hq
  rw [hq', randomOracle.run_eq]
  have hc : (∅ : (RandSpec H X M).QueryCache) [] = none := rfl
  simp only [hc, map_bind, map_pure, bind_assoc, pure_bind]
  refine bind_congr (m := ProbComp) fun u => ?_
  simp only [simulateQ_pure, map_pure, gRun_pure]
  refine congrArg pure (Prod.ext (Prod.ext (Prod.ext ?_ ?_) rfl) rfl)
  · exact items_bet C (⟨[m₀], 0⟩ : Out n M) m₀
  · change (1 + challenge _ _ m₀) * C.evenScalar 1 = _
    rw [key_bet]

set_option linter.flexible false in
/-- The verifier accepts the bettor's aggregate for the key `1`. -/
theorem finish_bet (m₀ : M) (c : (RandSpec H X M).QueryCache) :
    finish C challenge red (C.x (C.mulG 1))
      ((([(C.x (C.mulG 1), C.x (C.mulG 1), m₀)],
        (1 + challenge (C.x (C.mulG 1)) (C.x (C.mulG 1)) m₀) * C.evenScalar 1), ([] : List M)),
        c) = pure true := by
  have hw := wins_bet C challenge m₀
  unfold finish
  simp only [List.length_singleton, List.range_one, List.mapM_cons, List.mapM_nil, zQuery]
  simp at hw ⊢
  exact hw

/-- A run of the game in which the bettor wins. -/
theorem bettor_wins [NonceGen n M] (m₀ : M) :
    true ∈ support ((simulateQ (RandSpec H X M).romImpl
      (aggExperiment C challenge red (erase C (bettor C challenge m₀)))).run' ∅) := by
  have : Fact (1 < n) := ⟨(Fact.out : n.Prime).one_lt⟩
  rw [game_form C challenge red, mem_support_bind_iff]
  refine ⟨(C.x (C.mulG 1), 1), ?_, ?_⟩
  · have h : ((C.x (C.mulG 1), (1 : ZMod n)) : X × ZMod n) ∈ support (do
        let d ← $ᵗ (NonzeroScalar n)
        return (C.x (C.mulG d.1), d.1) : ProbComp (X × ZMod n)) := by
      rw [mem_support_bind_iff]
      exact ⟨⟨1, one_ne_zero⟩, mem_support_uniformSample _, by simp⟩
    exact h
  · dsimp only
    rw [bet_run]
    simp only [bind_assoc, pure_bind, finish_bet]
    obtain ⟨u, hu⟩ := support_uniformSample_nonempty (α := H)
    rw [mem_support_bind_iff]
    exact ⟨u, hu, by simp⟩

/-- **The standard game can be won.** The bettor wins it with positive
probability, for every randomizer hash, every reduction of its outputs and
every nonce derivation of the signer. -/
theorem bettor_advantage_pos [NonceGen n M] (m₀ : M) :
    0 < aggAdvantage C challenge red (erase C (bettor C challenge m₀)) := by
  unfold aggAdvantage
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton, prEvent_pos_iff]
  exact ⟨true, bettor_wins C challenge red m₀, rfl⟩

/-- The bettor makes one randomizer request: the hypothesis of
`halfagg_unforgeable` and of `halfagg_knowledge` with `q = 1`. -/
theorem bettor_queries (m₀ : M) (input : Message Unit (Pts E)) :
    ((bettor (H := H) C challenge m₀).main input).IsQueryBoundP
      (fun r => isRand r.value.data) 1 := by
  have e : ∀ {α : Type}
      (t : (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)).Domain)
      (f : _ → OracleComp (explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)) α),
      OracleComp.queryBind t f =
        (liftM ((explainedSpec (ZMod n) (Pts E) (Request X M) (Reply n H X M)).query t) >>=
          f) :=
    fun _ _ => rfl
  unfold bettor
  simp only [e]
  exact (isQueryBoundP_query_bind_iff
    (fun r : Explained (ZMod n) (Request X M) (Pts E) => isRand r.value.data = true) _ _ _).mpr
    ⟨Or.inr Nat.one_pos, fun _ => isQueryBoundP_pure _ _ _⟩

/-! ## The game of the knowledge theorem -/

/-- A win in the standard game is a verifying aggregate. -/
theorem aggAdvantage_le_verify [NonceGen n M] (F : AlgForger n H E X M) :
    aggAdvantage C challenge red (erase C F) ≤ aggVerifyAdvantage C challenge red (erase C F) := by
  unfold aggAdvantage aggVerifyAdvantage
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton,
    ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton,
    game_experiment_eq, verify_experiment_eq, prEvent_map, prEvent_map]
  refine prEvent_mono_of_support _ _ _ fun t _ h => ?_
  simp only [winB, aggWins, Bool.and_eq_true] at h
  exact h.1

/-- **The game of the knowledge theorem can be won.** The bettor's aggregate
verifies with positive probability. -/
theorem bettor_verify_pos [NonceGen n M] (m₀ : M) :
    0 < aggVerifyAdvantage C challenge red (erase C (bettor C challenge m₀)) :=
  (bettor_advantage_pos C challenge red m₀).trans_le (aggAdvantage_le_verify C challenge red _)

/-- `halfagg_unforgeable` applied to the bettor. Its left-hand side is positive
(`bettor_advantage_pos`). -/
theorem bettor_bound [NonceGen n M] [Inhabited M] (hx0 : C.liftX (C.x 0) = none) (m₀ : M)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    aggAdvantage C challenge red (erase C (bettor C challenge m₀)) ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (reduction C challenge red (bettor C challenge m₀)) + 2 * μ := by
  have h := halfagg_unforgeable C challenge red hx0 (bettor C challenge m₀) 1
    (bettor_queries C challenge m₀) μ hμ
  rwa [Nat.cast_one, one_add_one_eq_two] at h

/-! ## The game with the challenge hash as an oracle -/

section Rom

-- Uniform nonces, as in `Halfagg/SecurityROM.lean`.
attribute [local instance] NonceGen.uniform

/-- The bettor with oracle access to the challenge hash. It sends the target
key's point in a randomizer request, asks for the challenge of `m₀` with that
point's x-coordinate as nonce and as key, and outputs the bettor's aggregate. -/
def bettorRom (m₀ : M) : RomForger n H E X M where
  main input :=
    let req : Explained (ZMod n) (Request X M) (Pts E) :=
      Explained.ofVectors input.groups (Request.rand [] []) (copies input.groups 1)
    OracleComp.queryBind (spec := RomForgerSpec n H E X M) (.inr req) fun rep =>
    let pk : X := C.x ((req.value.groups ()).headD 0)
    OracleComp.queryBind (spec := RomForgerSpec n H E X M) (.inl (m₀, (pk, pk))) fun e =>
    pure (Explained.ofVectors (extend input.groups rep.groups)
      (⟨[m₀], (1 + e) * C.evenScalar 1⟩ : Out n M) (copies _ 2))
  algebraic _ _ :=
    ⟨Explained.valid_ofVectors _ _ _, fun _ => Explained.valid_ofVectors _ _ _⟩

/-- With its challenge queries answered from a table, `bettorRom` is the bettor
for the challenge hash of that table. -/
theorem bettorRom_at (g : M × (X × X) → ZMod n) (m₀ : M) :
    (bettorRom (H := H) C m₀).at g = bettor C (hOf g) m₀ := rfl

/-- **The game with the challenge hash as a random oracle can be won.** -/
theorem bettorRom_advantage_pos [SampleableType (M × (X × X) → ZMod n)] (m₀ : M) :
    0 < aggAdvantageROM C red (bettorRom C m₀) := by
  unfold aggAdvantageROM aggExperimentROM
  rw [prEvent_pos_iff]
  refine ⟨true, ?_, rfl⟩
  obtain ⟨g, hg⟩ := support_uniformSample_nonempty (α := M × (X × X) → ZMod n)
  rw [mem_support_bind_iff]
  refine ⟨g, hg, ?_⟩
  rw [bettorRom_at]
  exact bettor_wins C (hOf g) red m₀

/-- `bettorRom` explains the nonce of its challenge query. -/
theorem bettorRom_explains (m₀ : M) (input : Message Unit (Pts E)) :
    ExplainsNonces C ((bettorRom (H := H) C m₀).main input) [] :=
  fun _ => ⟨by simp [Explained.ofVectors, isRand, copies], fun _ => trivial⟩

theorem romBind_eq {α : Type} (t : (RomForgerSpec n H E X M).Domain)
    (f : _ → OracleComp (RomForgerSpec n H E X M) α) :
    OracleComp.queryBind t f = (liftM ((RomForgerSpec n H E X M).query t) >>= f) := rfl

/-- `bettorRom` makes one randomizer request. -/
theorem bettorRom_rand (m₀ : M) (input : Message Unit (Pts E)) :
    ((bettorRom (H := H) C m₀).main input).IsQueryBoundP (fun t => isRandCall t) 1 := by
  unfold bettorRom
  simp only [romBind_eq]
  exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr ⟨Or.inr Nat.one_pos, fun _ =>
    (isQueryBoundP_query_bind_iff _ _ _ _).mpr
      ⟨Or.inl (by simp [isRandCall]), fun _ => isQueryBoundP_pure _ _ _⟩⟩

/-- `bettorRom` makes one challenge query. -/
theorem bettorRom_chal (m₀ : M) (input : Message Unit (Pts E)) :
    ((bettorRom (H := H) C m₀).main input).IsQueryBoundP (fun t => isChalCall t) 1 := by
  unfold bettorRom
  simp only [romBind_eq]
  exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr ⟨Or.inl (by simp [isChalCall]), fun _ =>
    (isQueryBoundP_query_bind_iff _ _ _ _).mpr
      ⟨Or.inr (by simp [isChalCall]), fun _ => isQueryBoundP_pure _ _ _⟩⟩

/-- `bettorRom` makes no signing request. -/
theorem bettorRom_sign (m₀ : M) (input : Message Unit (Pts E)) :
    ((bettorRom (H := H) C m₀).main input).IsQueryBoundP (fun t => isSignCall t) 0 := by
  unfold bettorRom
  simp only [romBind_eq]
  exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr
    ⟨Or.inl (by simp [isSignCall, isSign, Explained.ofVectors]), fun _ =>
      (isQueryBoundP_query_bind_iff _ _ _ _).mpr
        ⟨Or.inl (by simp [isSignCall]), fun _ => isQueryBoundP_pure _ _ _⟩⟩

/-- `bettorRom` outputs one item. -/
theorem bettorRom_length (m₀ : M) (input : Message Unit (Pts E)) :
    ∀ out ∈ support ((bettorRom (H := H) C m₀).main input), out.value.data.ms.length ≤ 1 := by
  intro out hout
  unfold bettorRom at hout
  simp only [romBind_eq, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
    at hout
  obtain ⟨_, -, _, -, rfl⟩ := hout
  simp [Explained.ofVectors]

/-- `halfagg_dlog_tight` applied to `bettorRom`: one randomizer request, one
challenge query, no signing request and one item. Its left-hand side is
positive (`bettorRom_advantage_pos`). -/
theorem bettorRom_bound [Inhabited M] [Finite M] [Finite X]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none) (m₀ : M)
    (μ : ℝ≥0∞) (hμ : RedBound red μ) :
    aggAdvantageROM C red (bettorRom C m₀) ≤
      Pr{let x ← dlogExperiment C (dlogOfKeyRecovery C
        (keySolver C red (bettorRom C m₀)))}[x = true] + 2 * μ + 2 / n := by
  have h := halfagg_dlog_tight C red hx0 (bettorRom C m₀) 1 1 0 1 (bettorRom_rand C m₀)
    (bettorRom_chal C m₀) (bettorRom_sign C m₀) (bettorRom_length C m₀) (bettorRom_explains C m₀)
    μ hμ
  simpa [one_add_one_eq_two] using h

end Rom

end Halfagg.Security
