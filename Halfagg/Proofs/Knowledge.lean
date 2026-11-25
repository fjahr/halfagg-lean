import Halfagg.SecurityKnowledge
import Halfagg.Proofs.BridgeGame
import Halfagg.Proofs.TightBound
import Halfagg.Proofs.SignQueries

/-!
# Knowledge of the individual signatures: proofs

The verification game and the extraction experiment are both functions of the
annotated experiment's transcript (`verify_advantage_eq`,
`extract_advantage_eq`). On a transcript whose aggregate verifies, the extractor
fails only in the bad event of the unforgeability proof (`extract_all_or_bad`),
so the same bound applies (`know_bad`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security Halfagg.LoggedRun

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)
variable [SampleableType H] {red : H → ZMod n} {μ : ℝ≥0∞}

/-! ## Algebra -/

/-- **Extraction of every signature.** If an aggregate with valid representations
verifies, then every extracted signature verifies, or some coefficient `β*ᵢ` is
nonzero while the randomized sum `Σ zᵢ⋅β*ᵢ` vanishes. -/
theorem extract_all_or_bad (d : ZMod n) (items : List (AItem n X M)) (s : ZMod n)
    (zs : List (ZMod n)) (hok : ∀ a ∈ items, ItemOK C d a)
    (hver : aggVerifies C challenge (items.map strip) s zs = true) :
    extractWins C challenge (items.map strip) s zs
        (items.map (extractSig challenge items s zs)) = true ∨
    ((∃ a ∈ items, (starRep challenge a).2 ≠ 0) ∧
      isum (fun i b => zs.getD i 0 * (starRep challenge b).2) 0 items = 0) := by
  have hver' := hver
  simp only [aggVerifies, verifyWith, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hver'
  obtain ⟨⟨-, hlifts⟩, heq⟩ := hver'
  rw [items_map] at hlifts heq
  have hlift : ∀ a ∈ items, lifts C (strip a) = true :=
    fun a ha => hlifts _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
  have hs := s_eq C challenge d items (fun i => zs.getD i 0) s hok hlift heq
  by_cases hbad : (∃ a ∈ items, (starRep challenge a).2 ≠ 0) ∧
      isum (fun i b => zs.getD i 0 * (starRep challenge b).2) 0 items = 0
  · exact Or.inr hbad
  left
  -- every extracted `s` is `α* + β*⋅d`
  have hsig : ∀ a ∈ items, extractSig challenge items s zs a =
      (starRep challenge a).1 + (starRep challenge a).2 * d := by
    intro a ha
    unfold extractSig
    dsimp only
    by_cases hβ : isum (fun i b => zs.getD i 0 * (starRep challenge b).2) 0 items = 0
    · have hβa : (starRep challenge a).2 = 0 := by
        by_contra h
        exact hbad ⟨⟨a, ha, h⟩, hβ⟩
      rw [hβa, zero_mul, zero_mul]
    · have hx : (s - isum (fun i b => zs.getD i 0 * (starRep challenge b).1) 0 items) /
          isum (fun i b => zs.getD i 0 * (starRep challenge b).2) 0 items = d := by
        rw [div_eq_iff hβ, hs]; ring
      rw [hx]
  unfold extractWins
  rw [hver, List.zip_map']
  simp only [Bool.true_and, List.length_map, decide_true, List.all_map, List.all_eq_true,
    Function.comp_apply]
  intro a ha
  have hl := hlift a ha
  simp only [lifts, strip, Bool.and_eq_true, Option.isSome_iff_exists] at hl
  obtain ⟨⟨R, hR⟩, ⟨P, hP⟩⟩ := hl
  simp only [strip]
  rw [verify_eq_true_iff]
  refine ⟨P, hP, ?_⟩
  rw [hR, (hok a ha).1 R hR, (hok a ha).2 P hP, repPoint, repPoint, C.val_smul_mulG, ← map_sub,
    hsig a ha]
  apply congrArg some
  apply congrArg C.mulG
  simp only [starRep]
  ring

/-! ## Events of the transcript -/

/-- The transcript's aggregate passes `VerifyAggregate` with its randomizers. -/
def verB (t : Transcript n X M) : Bool :=
  aggVerifies C challenge (t.2.1.map strip) t.2.2.1 t.2.2.2.1

/-- The extractor succeeds on the transcript. -/
def extB (t : Transcript n X M) : Bool :=
  extractWins C challenge (t.2.1.map strip) t.2.2.1 t.2.2.2.1
    (t.2.1.map (extractSig challenge t.2.1 t.2.2.1 t.2.2.2.1))

/-- A verifying aggregate whose extraction fails means that the randomized sum
of the coefficients vanishes while some coefficient is nonzero. -/
theorem fail_sum_all [NonceGen n M] (hx0 : C.liftX (C.x 0) = none) (F : AlgForger n H E X M)
    (r : X × Explained (ZMod n) (Out n M) (Pts E) × Core n X M)
    (hr : r ∈ support (annPhase1 C challenge F)) (zs : List (ZMod n))
    (hver : verB C challenge
      (r.1, finalItems C r.2.1 r.2.2, r.2.1.value.data.s, zs, r.2.2.signed) = true)
    (hno : ¬ extB C challenge
      (r.1, finalItems C r.2.1 r.2.2, r.2.1.value.data.s, zs, r.2.2.signed) = true) :
    (∃ b ∈ finalItems C r.2.1 r.2.2, betaOf challenge b ≠ 0) ∧
      isum (fun i b => zs.getD i 0 * betaOf challenge b) 0 (finalItems C r.2.1 r.2.2) = 0 := by
  obtain ⟨d, -, -, -, -, recv, hcore, hval⟩ := phase1_ok C challenge hx0 F r hr
  simp only [verB, extB] at hver hno
  have hl : ∀ it ∈ toItems C r.2.1.value.data.ms (r.2.1.value.groups ()),
      lifts C it = true := by
    have h := hver
    simp only [aggVerifies, verifyWith, Bool.and_eq_true, List.all_eq_true] at h
    have h2 := h.1.2
    rw [items_map, finalItems, map_strip_annotate] at h2
    exact h2
  have hok := finalItems_ok C hx0 d hcore hval hl
  rcases extract_all_or_bad C challenge d _ _ _ hok hver with hex | h
  · exact (hno hex).elim
  · exact h

/-- **A verifying aggregate with a failed extraction is unlikely.** -/
theorem know_bad [NonceGen n M] (hμ : RedBound red μ) (hx0 : C.liftX (C.x 0) = none)
    (F : AlgForger n H E X M) (q : ℕ)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    Pr{let t ← annROM C challenge red F}[verB C challenge t = true ∧ ¬ extB C challenge t = true] ≤
      (q + 1 : ℝ≥0∞) * μ :=
  annROM_sum_bound C challenge hμ F q hq _
    fun r hr zs h => fail_sum_all C challenge hx0 F r hr zs h.1 h.2

/-! ## The verification game -/

theorem verify_experiment_eq [NonceGen n M] (F : AlgForger n H E X M) :
    (simulateQ (RandSpec H X M).romImpl (aggVerifyExperiment C challenge red (erase C F))).run' ∅ =
      verB C challenge <$> jExp C challenge red F := by
  have hexp : aggVerifyExperiment C challenge red (erase C F) = (do
      let ks ← (bip340 (M := M) C challenge (OracleComp (unifSpec + RandSpec H X M))).keygen
      let z ← (bip340 (M := M) C challenge
        (OracleComp (unifSpec + RandSpec H X M))).runWithSigningOracle ks.1 ks.2
          ((erase C F).main ks.1)
      let zs ← (List.range z.1.1.length).mapM (zQuery red z.1.1)
      pure (aggVerifies C challenge z.1.1 z.1.2 zs)) := rfl
  have key : ∀ pk sk, (do
      let z ← (bip340 (M := M) C challenge
        (OracleComp (unifSpec + RandSpec H X M))).runWithSigningOracle pk sk ((erase C F).main pk)
      let zs ← (List.range z.1.1.length).mapM (zQuery red (n := n) z.1.1)
      pure (aggVerifies C challenge z.1.1 z.1.2 zs)) = (do
      let w ← (simulateQ (gApp C challenge pk sk) ((erase C F).main pk)).run []
      let zs ← (List.range w.1.1.length).mapM (zQuery red (n := n) w.1.1)
      pure (aggVerifies C challenge w.1.1 w.1.2 zs)) := by
    intro pk sk
    rw [← run_sign_eq_game, bind_map_left]
  rw [hexp]
  unfold jExp
  simp only [key, simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind,
    StateT.run_pure, rom_keygenR, map_bind, bind_map_left, map_pure]
  refine bind_congr fun ks => ?_
  have h := game_run_eq C challenge (red := red)
    (fun _ its s zs _ => aggVerifies C challenge its s zs) F ks.1 ks.2
  simp only [gRun] at h
  simpa [verB] using h

/-- The aggregate of the erased forger verifies in the game exactly as often as
the transcript's aggregate does. -/
theorem verify_advantage_eq [NonceGen n M] (F : AlgForger n H E X M) :
    aggVerifyAdvantage C challenge red (erase C F) =
      Pr{let t ← annROM C challenge red F}[verB C challenge t = true] := by
  unfold aggVerifyAdvantage
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton, verify_experiment_eq,
    prEvent_map, annROM_eq]

/-! ## The extractor -/

theorem extractor_main_eq (F : AlgForger n H E X M) (pk : X) :
    extractor C challenge red F pk = (do
      let p ← ((simulateQ (redImpl (H := H) C challenge pk)
        (F.main (initial C ((C.liftX pk).getD 0)))).run Core.init).run ∅
      let q ← (tableZs red (finalItems C p.1.1 p.1.2)).run p.2
      pure (toItems C p.1.1.value.data.ms (p.1.1.value.groups ()), p.1.1.value.data.s, q.1,
        (finalItems C p.1.1 p.1.2).map
          (extractSig challenge (finalItems C p.1.1 p.1.2) p.1.1.value.data.s q.1))) := rfl

theorem extractor_sign_bound (F : AlgForger n H E X M) (p : M → Bool) (q : ℕ)
    (h : ∀ input, (F.main input).IsQueryBoundP (fun r => isSign p r.value.data) q) (pk : X) :
    (extractor C challenge red F pk).IsQueryBoundP (fun t => isSignQuery p t) q := by
  rw [extractor_main_eq]
  refine (isQueryBoundP_bind (n := q) (m := 0)
    (red_stack_sign C challenge p pk _ q (h _) Core.init ∅) fun y _ =>
      isQueryBoundP_bind (n := 0) (m := 0) ?_ fun _ _ => isQueryBoundP_pure _ _ _).mono
        (by omega)
  exact tableZs_sign p _ _ y.2

theorem extractor_run_eq [NonceGen n M] (F : AlgForger n H E X M) (pk : X) (sk : ZMod n) :
    (simulateQ (appImpl C challenge pk sk) (extractor C challenge red F pk)).run [] = (do
      let p ← ((simulateQ (jImpl (H := H) C challenge pk sk)
        (F.main (initial C ((C.liftX pk).getD 0)))).run Core.init).run ∅
      let q ← ((List.range (finalItems C p.1.1 p.1.2).length).mapM
        (jZ red (finalItems C p.1.1 p.1.2))).run p.2
      pure ((toItems C p.1.1.value.data.ms (p.1.1.value.groups ()), p.1.1.value.data.s, q.1,
        (finalItems C p.1.1 p.1.2).map
          (extractSig challenge (finalItems C p.1.1 p.1.2) p.1.1.value.data.s q.1)),
        p.1.2.signed)) :=
  red_run_post_eq C challenge
    (fun _ out st zs => (toItems C out.value.data.ms (out.value.groups ()), out.value.data.s, zs,
      (finalItems C out st).map (extractSig challenge (finalItems C out st) out.value.data.s zs)))
    F pk sk

theorem extract_experiment_eq [NonceGen n M] (F : AlgForger n H E X M) :
    extractExperiment C challenge red F = extB C challenge <$> jExp C challenge red F := by
  have hexp : extractExperiment C challenge red F = (do
      let ks ← (bip340 (M := M) C challenge ProbComp).keygen
      let z ← (bip340 (M := M) C challenge ProbComp).runWithSigningOracle ks.1 ks.2
        (extractor C challenge red F ks.1)
      pure (extractWins C challenge z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2)) := rfl
  have key : ∀ pk sk, (do
      let z ← (bip340 (M := M) C challenge ProbComp).runWithSigningOracle pk sk
        (extractor C challenge red F pk)
      pure (extractWins C challenge z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2)) = (do
      let w ← (simulateQ (appImpl C challenge pk sk) (extractor C challenge red F pk)).run []
      pure (extractWins C challenge w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2)) := by
    intro pk sk
    rw [← run_sign_eq, bind_map_left]
  rw [hexp]
  unfold jExp
  simp only [key, extractor_run_eq, map_bind, bind_assoc, pure_bind, map_pure]
  simp [extB, finalItems, map_strip_annotate]

/-- The extractor succeeds exactly as often as it does on the transcript. -/
theorem extract_advantage_eq [NonceGen n M] (F : AlgForger n H E X M) :
    extractAdvantage C challenge red F =
      Pr{let t ← annROM C challenge red F}[extB C challenge t = true] := by
  unfold extractAdvantage
  rw [ProbCompRuntime.probComp_evalDist, ← prEvent_eq_evalDist_singleton,
    extract_experiment_eq, prEvent_map, annROM_eq]

end Halfagg.Security
