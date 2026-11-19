import Halfagg.SecurityTight
import Halfagg.UnforgeabilityROM

/-!
# A tight reduction to discrete log: proofs

* `machine_experiment_eq`: against a fixed challenge table, the Fiat-Shamir game
  of an oracle machine is the joint run followed by its final step.
* `tight_or_bad`, `tight_split`: a winning forger makes the key machine or the
  signature machine forge, up to the bad event of the unforgeability proof.
* `keyMachine_to_nma`: VCVio's signing simulation for the key machine.
* `key_fork_le`: if the simulated key machine's forgery verifies, its candidate
  key is the secret key, so the simulated run solves discrete log.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Halfagg.Security

open Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security Halfagg.LoggedRun

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X)

/-! ## An oracle machine against a fixed table -/

variable (g : M × (X × X) → ZMod n)

/-- The joint run with secret key `d`. -/
noncomputable def jRun (ch : X → X → M → ZMod n) (F : AlgForger n E X M) (d : ZMod n) :
    ProbComp (Transcript n X M) := do
  let p ← ((simulateQ (jImpl C ch (C.x (C.mulG d)) d)
    (F.main (initial C ((C.liftX (C.x (C.mulG d))).getD 0)))).run Core.init).run ∅
  let q ← ((List.range (finalItems C p.1.1 p.1.2).length).mapM
    (jZ (finalItems C p.1.1 p.1.2))).run p.2
  pure (C.x (C.mulG d), finalItems C p.1.1 p.1.2, p.1.1.value.data.s, q.1, p.1.2.signed)

theorem jExp_eq (ch : X → X → M → ZMod n) (F : AlgForger n E X M) :
    jExp C ch F = (do
      let k ← $ᵗ (NonzeroScalar n)
      jRun C ch F k.1) := by
  have hkg : (bip340 (M := M) C ch ProbComp).keygen = (do
      let k ← $ᵗ (NonzeroScalar n)
      pure (C.x (C.mulG k.1), k.1)) := rfl
  unfold jExp jRun
  rw [hkg]
  simp only [bind_assoc, pure_bind]

section Machine

variable {d : ZMod n} (hd : d ≠ 0) (fin : FinalStep n E X M C)
  (finG : ZMod n → Transcript n X M → M × FSSig n X)
  (hfin : ∀ (d : ZMod n) (items : List (AItem n X M)) (s : ZMod n) (zs : List (ZMod n))
    (signed l : List M),
    (simulateQ (fsImpl C g (keyOf C d) (C.evenScalar d))
      (fin (keyOf C d) items s zs signed (items.map fun a => g (a.m, (a.r, a.pk))))).run l =
      pure (finG d (C.x (C.mulG d), items, s, zs, signed), l))

include hd hfin in
theorem machine_run_eq (F : RomForger n E X M) :
    (simulateQ (fsImpl C g (keyOf C d) (C.evenScalar d))
        ((romMachine C F fin).main (keyOf C d))).run [] =
      (fun t => (finG d t, t.2.2.2.2)) <$> jRun C (hOf g) (F.at g) d := by
  have hpk : C.x (keyOf C d).1 = C.x (C.mulG d) := C.x_evenScalar d
  have hstack := rom_stack C g hd (F.main (initial C ((C.liftX (C.x (C.mulG d))).getD 0)))
    (Core.init : Core n X M) ∅
  rw [show (Core.init : Core n X M).signed = [] from rfl] at hstack
  unfold jRun
  simp only [romMachine, hpk, simulateQ_bind, StateT.run_bind, map_bind]
  rw [hstack, bind_map_left]
  refine bind_congr fun p => ?_
  simp only [zs_rom, bind_map_left, es_rom, pure_bind, hfin, map_pure]
  rfl

/-- The outcome of the Fiat-Shamir game as a function of the secret key and the
transcript. -/
noncomputable def machineOK (d : ZMod n) (t : Transcript n X M) : Bool :=
  !decide ((finG d t).1 ∈ t.2.2.2.2) &&
    (sigma C).verify (keyOf C d) (finG d t).2.1 (g ((finG d t).1, (finG d t).2.1)) (finG d t).2.2

include hd hfin in
theorem machine_game_key (F : RomForger n E X M) :
    (do
      let z ← simulateQ (tableImpl g)
        ((FiatShamir.inROM (sigma C) (keyGen C) M).runWithSigningOracle (keyOf C d)
          (C.evenScalar d) ((romMachine C F fin).main (keyOf C d)))
      let v ← simulateQ (tableImpl g)
        ((FiatShamir.inROM (sigma C) (keyGen C) M).verify (keyOf C d) z.1.1 z.1.2)
      pure (!z.2.wasQueried z.1.1 && v)) =
      machineOK C g finG d <$> jRun C (hOf g) (F.at g) d := by
  have hrun := machine_run_eq C g hd fin finG hfin F
  rw [← fs_stack, ← run_sign_eq_fs, simulateQ_map] at hrun
  have key : (do
      let z ← simulateQ (tableImpl g)
        ((FiatShamir.inROM (sigma C) (keyGen C) M).runWithSigningOracle (keyOf C d)
          (C.evenScalar d) ((romMachine C F fin).main (keyOf C d)))
      let v ← simulateQ (tableImpl g)
        ((FiatShamir.inROM (sigma C) (keyGen C) M).verify (keyOf C d) z.1.1 z.1.2)
      pure (!z.2.wasQueried z.1.1 && v)) = (do
      let w ← (fun z => (z.1, z.2.map (fun e => e.1))) <$> simulateQ (tableImpl g)
        ((FiatShamir.inROM (sigma C) (keyGen C) M).runWithSigningOracle (keyOf C d)
          (C.evenScalar d) ((romMachine C F fin).main (keyOf C d)))
      pure (!decide (w.1.1 ∈ w.2) &&
        (sigma C).verify (keyOf C d) w.1.2.1 (g (w.1.1, w.1.2.1)) w.1.2.2)) := by
    rw [bind_map_left]
    refine bind_congr fun z => ?_
    simp [fs_verify, QueryLog.wasQueried_eq_decide_mem_map_fst]
  rw [key, hrun, bind_map_left, map_eq_bind_pure_comp]
  rfl

end Machine

/-- **An oracle machine against a fixed table.** -/
theorem machine_experiment_eq (fin : FinalStep n E X M C)
    (finG : ZMod n → Transcript n X M → M × FSSig n X)
    (hfin : ∀ (d : ZMod n) (items : List (AItem n X M)) (s : ZMod n) (zs : List (ZMod n))
      (signed l : List M),
      (simulateQ (fsImpl C g (keyOf C d) (C.evenScalar d))
        (fin (keyOf C d) items s zs signed (items.map fun a => g (a.m, (a.r, a.pk))))).run l =
        pure (finG d (C.x (C.mulG d), items, s, zs, signed), l))
    (F : RomForger n E X M) :
    simulateQ (tableImpl g) (SignatureAlg.unforgeableExperiment (romMachine C F fin)) = (do
      let k ← $ᵗ (NonzeroScalar n)
      machineOK C g finG k.1 <$> jRun C (hOf g) (F.at g) k.1) := by
  have hexp : SignatureAlg.unforgeableExperiment (romMachine C F fin) = (do
      let ks ← (FiatShamir.inROM (sigma C) (keyGen C) M).keygen
      let z ← (FiatShamir.inROM (sigma C) (keyGen C) M).runWithSigningOracle ks.1 ks.2
        ((romMachine C F fin).main ks.1)
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
  simp only [simulateQ_bind, simulateQ_pure, fs_keygen]
  have hgen : (keyGen C).gen = (do
      let k ← $ᵗ (NonzeroScalar n)
      pure (keyOf C k.1, C.evenScalar k.1)) := rfl
  rw [hgen]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun k => ?_
  exact machine_game_key C g k.2 fin finG hfin F

/-! ## The final steps against a fixed table -/

theorem candKey_known (pk : X) (items : List (AItem n X M)) (s : ZMod n) (zs : List (ZMod n))
    (signed : List M) :
    candKey (knownChal items (items.map fun a => g (a.m, (a.r, a.pk)))) pk items s zs signed =
      candKey (hOf g) pk items s zs signed := by
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
  unfold candKey
  simp only [hα, hβ]

/-- `keyFin` with the hash answered from the table. -/
noncomputable def keyFinG [Inhabited M] (d : ZMod n) (t : Transcript n X M) : M × FSSig n X :=
  match target t.1 t.2.1 t.2.2.2.2 with
  | none => junk C
  | some a =>
    if C.mulG (candKey (hOf g) t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) =
        C.mulG (C.evenScalar d) then
      (a.m, ((C.x (C.mulG (C.evenScalar 1)), t.1),
        C.evenScalar 1 + g (a.m, (C.x (C.mulG (C.evenScalar 1)), t.1)) *
          candKey (hOf g) t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2))
    else junk C

theorem keyFin_table [Inhabited M] (d : ZMod n) (items : List (AItem n X M)) (s : ZMod n)
    (zs : List (ZMod n)) (signed l : List M) :
    (simulateQ (fsImpl C g (keyOf C d) (C.evenScalar d))
      (keyFin C (keyOf C d) items s zs signed (items.map fun a => g (a.m, (a.r, a.pk))))).run l =
      pure (keyFinG C g d (C.x (C.mulG d), items, s, zs, signed), l) := by
  have hpk : C.x (keyOf C d).1 = C.x (C.mulG d) := C.x_evenScalar d
  unfold keyFin keyFinG
  dsimp only
  rw [hpk, candKey_known, show (keyOf C d).1 = C.mulG (C.evenScalar d) from rfl]
  rcases hfind : target (C.x (C.mulG d)) items signed with _ | a
  · simp
  · dsimp only
    split_ifs
    · simp [fs_hashQ]
    · simp

/-- The win check with the known challenges is the win check with the table's
challenge function. -/
theorem aggWins_known (pk : X) (items : List (AItem n X M)) (s : ZMod n) (zs : List (ZMod n))
    (sg : M → Bool) :
    aggWins C (knownChal items (items.map fun a => g (a.m, (a.r, a.pk)))) pk
        (items.map fun a => (a.r, a.pk, a.m)) s zs sg =
      aggWins C (hOf g) pk (items.map fun a => (a.r, a.pk, a.m)) s zs sg := by
  have h : isum (fun i it => (zs.getD i 0).val •
        term C (knownChal items (items.map fun a => g (a.m, (a.r, a.pk)))) it) 0
        (items.map fun a => (a.r, a.pk, a.m)) =
      isum (fun i it => (zs.getD i 0).val • term C (hOf g) it) 0
        (items.map fun a => (a.r, a.pk, a.m)) := by
    rw [isum_map, isum_map]
    refine isum_congr fun i a ha _ _ => ?_
    simp only [term, knownChal_eq g items ha]
  unfold aggWins verifyWith
  simp only [items_map, h]

/-- `repFin` with the hash answered from the table. -/
noncomputable def repFinG [Inhabited M] (d : ZMod n) (t : Transcript n X M) : M × FSSig n X :=
  match target t.1 t.2.1 t.2.2.2.2 with
  | none => junk C
  | some a =>
    if C.mulG (candKey (hOf g) t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) =
        C.mulG (C.evenScalar d) then junk C
    else if aggWins C (hOf g) t.1 (t.2.1.map fun a => (a.r, a.pk, a.m)) t.2.2.1 t.2.2.2.1
        (fun m => t.2.2.2.2.contains m) = true ∧ (starRep (hOf g) a).2 = 0 then
      (a.m, ((a.r, t.1), (starRep (hOf g) a).1))
    else junk C

theorem repFin_table [Inhabited M] (d : ZMod n) (items : List (AItem n X M)) (s : ZMod n)
    (zs : List (ZMod n)) (signed l : List M) :
    (simulateQ (fsImpl C g (keyOf C d) (C.evenScalar d))
      (repFin C (keyOf C d) items s zs signed (items.map fun a => g (a.m, (a.r, a.pk))))).run l =
      pure (repFinG C g d (C.x (C.mulG d), items, s, zs, signed), l) := by
  have hpk : C.x (keyOf C d).1 = C.x (C.mulG d) := C.x_evenScalar d
  unfold repFin repFinG
  dsimp only
  rw [hpk, candKey_known, show (keyOf C d).1 = C.mulG (C.evenScalar d) from rfl, aggWins_known]
  rcases hfind : target (C.x (C.mulG d)) items signed with _ | a
  · simp
  · have ha := List.mem_of_find?_eq_some hfind
    have hstar : starRep (knownChal items (items.map fun a => g (a.m, (a.r, a.pk)))) a =
        starRep (hOf g) a := starRep_congr (knownChal_eq g items ha)
    dsimp only
    rw [hstar]
    split_ifs <;> simp

/-! ## Algebra -/

/-- **Three cases of a winning forgery** with valid representations: the
candidate key is the secret key, or the target item's `(r, α*)` is a BIP340
signature with `β* = 0`, or the randomized sum of the coefficients vanishes
while some coefficient is nonzero. -/
theorem tight_or_bad (ch : X → X → M → ZMod n) (d : ZMod n) (hd : d ≠ 0)
    (heven : C.hasEvenY (C.mulG d) = true) (items : List (AItem n X M)) (s : ZMod n)
    (zs : List (ZMod n)) (signed : List M) (hok : ∀ a ∈ items, ItemOK C d a)
    (hwin : aggWins C ch (C.x (C.mulG d)) (items.map strip) s zs
      (fun m => signed.contains m) = true) :
    ∃ a, target (C.x (C.mulG d)) items signed = some a ∧
      (candKey ch (C.x (C.mulG d)) items s zs signed = d ∨
        ((starRep ch a).2 = 0 ∧
          BIP340.verify C ch (C.x (C.mulG d)) a.m (a.r, (starRep ch a).1) = true) ∨
        ((∃ b ∈ items, (starRep ch b).2 ≠ 0) ∧
          isum (fun i b => zs.getD i 0 * (starRep ch b).2) 0 items = 0)) := by
  set pk := C.x (C.mulG d) with hpk
  have hPstar : C.liftX pk = some (C.mulG d) := C.liftX_x _ (C.mulG_ne_zero hd) heven
  simp only [aggWins, verifyWith, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.any_eq_true] at hwin
  obtain ⟨⟨⟨-, hlifts⟩, heq⟩, ⟨it, hit, htarget⟩⟩ := hwin
  rw [items_map] at hlifts heq
  have hlift : ∀ a ∈ items, lifts C (strip a) = true :=
    fun a ha => hlifts _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
  have hs := s_eq C ch d items (fun i => zs.getD i 0) s hok hlift heq
  obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp hit
  have hfind : (items.find? fun a => a.pk == pk && !signed.contains a.m).isSome := by
    rw [List.find?_isSome]
    exact ⟨a₀, ha₀, by simpa [strip] using htarget⟩
  obtain ⟨a, hfa'⟩ := Option.isSome_iff_exists.mp hfind
  have ha := List.mem_of_find?_eq_some hfa'
  have hpa := List.find?_some hfa'
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hpa
  obtain ⟨hapk, -⟩ := hpa
  have hfa : target pk items signed = some a := hfa'
  have hPa : repPoint C d a.repPk = C.mulG d := by
    exact ((hok a ha).2 _ (by rw [hapk, hPstar])).symm
  have hPd : a.repPk.1 + a.repPk.2 * d = d := C.mulG_injective hPa
  refine ⟨a, hfa, ?_⟩
  by_cases hb : a.repPk.2 = 1
  swap
  · -- the representation of `P*` gives the key
    left
    unfold candKey
    simp only [hfa, hb, ↓reduceIte]
    rw [div_eq_iff (sub_ne_zero.mpr (Ne.symm hb))]
    linear_combination hPd
  by_cases hβa : (starRep ch a).2 = 0
  · -- `β*ₐ = 0`: `(rₐ, α*ₐ)` is a signature
    right; left
    refine ⟨hβa, ?_⟩
    rw [verify_eq_true_iff]
    refine ⟨C.mulG d, hPstar, ?_⟩
    have hl := hlift a ha
    simp only [lifts, strip, Bool.and_eq_true, Option.isSome_iff_exists] at hl
    obtain ⟨⟨R, hR⟩, -⟩ := hl
    rw [hR, (hok a ha).1 R hR, C.val_smul_mulG, ← map_sub, repPoint]
    apply congrArg some
    apply congrArg C.mulG
    simp only [starRep] at hβa ⊢
    rw [← hapk]
    linear_combination d * hβa - (ch a.r a.pk a.m) * hPd
  · by_cases hβ : isum (fun i b => zs.getD i 0 * (starRep ch b).2) 0 items = 0
    · exact Or.inr (Or.inr ⟨⟨a, ha, hβa⟩, hβ⟩)
    · left
      unfold candKey
      simp only [hfa, hb, ↓reduceIte]
      rw [div_eq_iff hβ, hs]; ring

/-! ## Events of the transcript -/

/-- The candidate key is the secret key, and the forgery has an item with the
target key and an unsigned message. -/
def keyB (ch : X → X → M → ZMod n) (t : Transcript n X M) : Bool :=
  match target t.1 t.2.1 t.2.2.2.2 with
  | none => false
  | some _ => decide (C.mulG (candKey ch t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) =
      (C.liftX t.1).getD 0)

/-- The candidate key is wrong, and the target item's `(r, α*)` is a BIP340
signature with `β* = 0`. -/
def repB (ch : X → X → M → ZMod n) (t : Transcript n X M) : Bool :=
  match target t.1 t.2.1 t.2.2.2.2 with
  | none => false
  | some a => !decide (C.mulG (candKey ch t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) =
      (C.liftX t.1).getD 0) &&
      aggWins C ch t.1 (t.2.1.map fun a => (a.r, a.pk, a.m)) t.2.2.1 t.2.2.2.1
        (fun m => t.2.2.2.2.contains m) && decide ((starRep ch a).2 = 0) &&
      BIP340.verify C ch t.1 a.m (a.r, (starRep ch a).1)

theorem liftX_pk {d : ZMod n} (hd : d ≠ 0) :
    C.liftX (C.x (C.mulG d)) = some (C.mulG (C.evenScalar d)) := by
  rw [← C.x_evenScalar d]
  exact C.liftX_x _ (C.mulG_ne_zero (C.evenScalar_ne_zero hd)) (C.hasEvenY_evenScalar hd)

/-- If the candidate key is right, the forgery of `keyFin` wins the Fiat-Shamir game. -/
theorem keyB_machineOK [Inhabited M] {d : ZMod n} (hd : d ≠ 0) {t : Transcript n X M}
    (ht : t.1 = C.x (C.mulG d)) (h : keyB C (hOf g) t = true) :
    machineOK C g (keyFinG C g) d t = true := by
  unfold keyB at h
  unfold machineOK keyFinG
  rcases hfind : target t.1 t.2.1 t.2.2.2.2 with _ | a
  · rw [hfind] at h
    exact Bool.noConfusion h
  · simp only [hfind] at h ⊢
    rw [ht, liftX_pk C hd, Option.getD_some, decide_eq_true_eq] at h
    have hpa := List.find?_some hfind
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hpa
    rw [ht]
    simp only [h, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      sigma, decide_eq_true_eq]
    refine ⟨hpa.2, (C.x_evenScalar d).symm, ?_⟩
    rw [C.liftX_x _ (evenScalar_one_mem C).1 (evenScalar_one_mem C).2]
    apply congrArg some
    rw [show (keyOf C d).1 = C.mulG (C.evenScalar d) from rfl, ← h, C.val_smul_mulG, ← map_sub]
    apply congrArg C.mulG
    ring

/-- If the target item's `(r, α*)` is a signature, the forgery of `repFin` wins
the Fiat-Shamir game. -/
theorem repB_machineOK [Inhabited M] {d : ZMod n} (hd : d ≠ 0) {t : Transcript n X M}
    (ht : t.1 = C.x (C.mulG d)) (h : repB C (hOf g) t = true) :
    machineOK C g (repFinG C g) d t = true := by
  unfold repB at h
  unfold machineOK repFinG
  rcases hfind : target t.1 t.2.1 t.2.2.2.2 with _ | a
  · rw [hfind] at h
    exact Bool.noConfusion h
  · simp only [hfind] at h ⊢
    rw [ht, liftX_pk C hd, Option.getD_some] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨hkey, hw⟩, hβ⟩, hv⟩ := h
    have hpa := List.find?_some hfind
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hpa
    rw [ht]
    simp only [hkey, hw, hβ, and_self, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    exact ⟨hpa.2, by rw [verify_fs C g hd]; exact hv⟩

/-- A winning transcript in neither of the two cases means that the randomized
sum of the coefficients vanishes while some coefficient is nonzero. -/
theorem tight_fail_sum (ch : X → X → M → ZMod n) (hx0 : C.liftX (C.x 0) = none)
    (F : AlgForger n E X M)
    (r : X × Explained (ZMod n) (Out n M) (Pts E) × Core n X M)
    (hr : r ∈ support (annPhase1 C ch F)) (zs : List (ZMod n))
    (hwin : winT C ch (r.1, finalItems C r.2.1 r.2.2, r.2.1.value.data.s, zs, r.2.2.signed))
    (hK : ¬ keyB C ch
      (r.1, finalItems C r.2.1 r.2.2, r.2.1.value.data.s, zs, r.2.2.signed) = true)
    (hR : ¬ repB C ch
      (r.1, finalItems C r.2.1 r.2.2, r.2.1.value.data.s, zs, r.2.2.signed) = true) :
    (∃ b ∈ finalItems C r.2.1 r.2.2, betaOf ch b ≠ 0) ∧
      isum (fun i b => zs.getD i 0 * betaOf ch b) 0 (finalItems C r.2.1 r.2.2) = 0 := by
  obtain ⟨d, hd, heven, hpk, -, recv, hcore, hval⟩ := phase1_ok C ch hx0 F r hr
  simp only [winT, hpk] at hwin
  have hl : ∀ it ∈ toItems C r.2.1.value.data.ms (r.2.1.value.groups ()),
      lifts C it = true := by
    have h := hwin
    simp only [aggWins, verifyWith, Bool.and_eq_true, List.all_eq_true] at h
    have h2 := h.1.1.2
    rw [items_map, finalItems, map_strip_annotate] at h2
    exact h2
  have hok := finalItems_ok C hx0 d hcore hval hl
  have hPstar : C.liftX (C.x (C.mulG d)) = some (C.mulG d) :=
    C.liftX_x _ (C.mulG_ne_zero hd) heven
  obtain ⟨a, hfa, h⟩ := tight_or_bad C ch d hd heven _ _ _ _ hok hwin
  unfold keyB at hK
  unfold repB at hR
  simp only [hpk, hfa, hPstar, Option.getD_some] at hK hR
  rcases h with hk | ⟨hβ, hv⟩ | hbad
  · exact absurd (by rw [hk]; simp) hK
  · by_cases hkey : C.mulG (candKey ch (C.x (C.mulG d)) (finalItems C r.2.1 r.2.2)
        r.2.1.value.data.s zs r.2.2.signed) = C.mulG d
    · exact absurd (by simp [hkey]) hK
    · refine absurd ?_ hR
      have hw' : aggWins C ch (C.x (C.mulG d))
          ((finalItems C r.2.1 r.2.2).map fun a => (a.r, a.pk, a.m)) r.2.1.value.data.s zs
          (fun m => r.2.2.signed.contains m) = true := hwin
      rw [hw', hv]
      simp [hkey, hβ]
  · exact hbad

/-! ## The forger's advantage against the two machines -/

theorem prEvent_bind_mono {α β γ : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (f' : α → ProbComp γ) (p : β → Prop) (p' : γ → Prop)
    (h : ∀ a, Pr{let y ← f a}[p y] ≤ Pr{let y ← f' a}[p' y]) :
    Pr{let y ← mx >>= f}[p y] ≤ Pr{let y ← mx >>= f'}[p' y] := by
  simpa using prEvent_bind_le_add_const mx f f' p p' 0 (by simpa using h)

theorem jRun_fst (ch : X → X → M → ZMod n) (F : AlgForger n E X M) (d : ZMod n)
    {t : Transcript n X M} (ht : t ∈ support (jRun C ch F d)) : t.1 = C.x (C.mulG d) := by
  unfold jRun at ht
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at ht
  obtain ⟨p, -, q, -, rfl⟩ := ht
  rfl

/-- Against a fixed table, a win is one of the two cases or the bad event. -/
theorem tight_table (hx0 : C.liftX (C.x 0) = none) (F : AlgForger n E X M) (q : ℕ)
    (ch : X → X → M → ZMod n)
    (hq : ∀ input, (F.main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    aggAdvantage C ch (erase C F) ≤
      Pr{let t ← jExp C ch F}[(keyB C ch t || repB C ch t) = true] + (q + 1 : ℝ≥0∞) / n := by
  classical
  refine (bridge_game C ch F).trans ?_
  refine ((prEvent_mono_of_support _ _
    (fun t => (keyB C ch t || repB C ch t) = true ∨
      (winT C ch t ∧ ¬ (keyB C ch t || repB C ch t) = true))
    fun t _ hw => ?_).trans (prEvent_or_le _ _ _)).trans (add_le_add ?_ ?_)
  · by_cases h : (keyB C ch t || repB C ch t) = true
    · exact Or.inl h
    · exact Or.inr ⟨hw, h⟩
  · rw [annROM_eq]
  · refine annROM_sum_bound C ch F q hq _ fun r hr zs h => ?_
    simp only [Bool.or_eq_true, not_or] at h
    exact tight_fail_sum C ch hx0 F r hr zs h.1 h.2.1 h.2.2

/-- **A forger wins at most as often as the two machines forge, up to the bad
event.** -/
theorem tight_split [Inhabited M] [Finite M] [Finite X]
    [SampleableType (M × (X × X) → ZMod n)] (hx0 : C.liftX (C.x 0) = none)
    (F : RomForger n E X M) (q : ℕ)
    (hq : ∀ g input, ((F.at g).main input).IsQueryBoundP (fun r => isRand r.value.data) q) :
    aggAdvantageROM C F ≤
      SignatureAlg.unforgeableAdvantage (FiatShamir.runtime M) (romMachine C F (keyFin C)) +
        SignatureAlg.unforgeableAdvantage (FiatShamir.runtime M) (romMachine C F (repFin C)) +
        (q + 1 : ℝ≥0∞) / n := by
  classical
  -- both machines as functions of the joint run
  have hmach : ∀ (fin : FinalStep n E X M C) (finG : (M × (X × X) → ZMod n) → ZMod n →
      Transcript n X M → M × FSSig n X)
      (hfin : ∀ g (d : ZMod n) (items : List (AItem n X M)) (s : ZMod n) (zs : List (ZMod n))
        (signed l : List M),
        (simulateQ (fsImpl C g (keyOf C d) (C.evenScalar d))
          (fin (keyOf C d) items s zs signed (items.map fun a => g (a.m, (a.r, a.pk))))).run l =
          pure (finG g d (C.x (C.mulG d), items, s, zs, signed), l))
      (ev : (M × (X × X) → ZMod n) → Transcript n X M → Bool)
      (hev : ∀ g (d : ZMod n), d ≠ 0 → ∀ t : Transcript n X M, t.1 = C.x (C.mulG d) →
        ev g t = true → machineOK C g (finG g) d t = true),
      Pr{let b ← (($ᵗ (M × (X × X) → ZMod n)) >>= fun g =>
          ev g <$> jExp C (hOf g) (F.at g))}[b = true] ≤
        SignatureAlg.unforgeableAdvantage (FiatShamir.runtime M) (romMachine C F fin) := by
    intro fin finG hfin ev hev
    rw [fs_advantage_eq_table]
    simp only [fun g => machine_experiment_eq C g fin (finG g) (hfin g) F, jExp_eq]
    refine prEvent_bind_mono _ _ _ _ _ fun g => ?_
    rw [prEvent_map]
    refine prEvent_bind_mono _ _ _ _ _ fun k => ?_
    rw [prEvent_map]
    exact prEvent_mono_of_support _ _ _ fun t ht h =>
      hev g k.1 k.2 t (jRun_fst C _ _ _ ht) h
  have hK := hmach (keyFin C) (fun g => keyFinG C g) (fun g => keyFin_table C g)
    (fun g => keyB C (hOf g))
    fun g d hd t ht h => keyB_machineOK C g hd ht h
  have hR := hmach (repFin C) (fun g => repFinG C g) (fun g => repFin_table C g)
    (fun g => repB C (hOf g))
    fun g d hd t ht h => repB_machineOK C g hd ht h
  -- the game, table by table
  have hgame : aggAdvantageROM C F ≤
      Pr{let b ← (($ᵗ (M × (X × X) → ZMod n)) >>= fun g =>
        (fun t => (keyB C (hOf g) t, repB C (hOf g) t)) <$> jExp C (hOf g) (F.at g))}[
          (b.1 || b.2) = true] + (q + 1 : ℝ≥0∞) / n := by
    unfold aggAdvantageROM aggExperimentROM
    refine prEvent_bind_le_add_const _ _ _ _ _ _ fun g => ?_
    have h := tight_table C hx0 (F.at g) q (hOf g) (hq g)
    unfold aggAdvantage at h
    rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton] at h
    rw [prEvent_map]
    exact h
  refine hgame.trans (add_le_add ?_ le_rfl)
  refine ((prEvent_mono_of_support _ _ (fun b => b.1 = true ∨ b.2 = true)
    fun b _ h => by simpa using h).trans (prEvent_or_le _ _ _)).trans (add_le_add ?_ ?_)
  · have h := hK
    rw [show (fun g => keyB C (hOf g) <$> jExp C (hOf g) (F.at g)) =
      fun g => Prod.fst <$> ((fun t => (keyB C (hOf g) t, repB C (hOf g) t)) <$>
        jExp C (hOf g) (F.at g)) from by funext g; simp [Functor.map_map], ← map_bind,
      prEvent_map] at h
    exact h
  · have h := hR
    rw [show (fun g => repB C (hOf g) <$> jExp C (hOf g) (F.at g)) =
      fun g => Prod.snd <$> ((fun t => (keyB C (hOf g) t, repB C (hOf g) t)) <$>
        jExp C (hOf g) (F.at g)) from by funext g; simp [Functor.map_map], ← map_bind,
      prEvent_map] at h
    exact h

/-! ## Query counts of an oracle machine -/

section Cost

variable (p : (RomSpec n X M).Domain → Prop) [DecidablePred p] (cH cS : ℕ)
  (hU : ∀ k, ¬ p (.inl (.inl k))) (hH : ∀ key, p (.inl (.inr key)) → 0 < cH)
  (hS : ∀ m, p (.inr m) → 0 < cS)

include hH in
theorem keyFin_bound [Inhabited M] (P : Stmt C) (items : List (AItem n X M)) (s : ZMod n)
    (zs : List (ZMod n)) (signed : List M) (es : List (ZMod n)) :
    (keyFin C P items s zs signed es).IsQueryBoundP p cH := by
  unfold keyFin
  split
  · exact isQueryBoundP_pure _ _ _
  · split_ifs
    · exact isQueryBoundP_bind (m := 0) (hashQ_bound p cH hH _)
        fun _ _ => isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_pure _ _ _

theorem romMachine_main_eq (F : RomForger n E X M) (fin : FinalStep n E X M C) (P : Stmt C) :
    (romMachine C F fin).main P = (do
      let r ← ((simulateQ (romHandler C (C.x P.1))
        (F.main (initial C ((C.liftX (C.x P.1)).getD 0)))).run Core.init).run ∅
      let q ← ((List.range (finalItems C r.1.1 r.1.2).length).mapM fun i =>
        if i = 0 then pure 1 else romTableRO ((finalItems C r.1.1 r.1.2).take (i + 1))).run r.2
      let es ← (finalItems C r.1.1 r.1.2).mapM fun a => hashQ (n := n) (a.m, (a.r, a.pk))
      fin P (finalItems C r.1.1 r.1.2) r.1.1.value.data.s q.1 r.1.2.signed es) := rfl

include hU hH hS in
theorem romMachine_cost (F : RomForger n E X M) (fin : FinalStep n E X M C)
    (hfin : ∀ P items s zs signed es, (fin P items s zs signed es).IsQueryBoundP p cH)
    (qH qS ℓ : ℕ)
    (hFH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hFS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (P : Stmt C) :
    ((romMachine C F fin).main P).IsQueryBoundP p
      (qH * cH + qS * (cS + cH) + (ℓ * cH + cH)) := by
  rw [romMachine_main_eq]
  refine isQueryBoundP_bind (rom_stack_bound C p cH cS hU hH hS _ _ qH qS (hFH _) (hFS _) _ _)
    fun r hr => ?_
  have hlen : (finalItems C r.1.1 r.1.2).length ≤ ℓ := by
    simp only [finalItems, annotate_length]
    exact (toItems_length_le C _ _).trans (hL _ _ (rom_support C _ _ _ _ r hr))
  refine (isQueryBoundP_bind (n := 0) (zsRom_bound p hU _ _ _) fun q _ =>
    isQueryBoundP_bind (esRom_bound p cH hH _) fun es _ => hfin _ _ _ _ _ _).mono ?_
  have := Nat.mul_le_mul_right cH hlen
  omega

end Cost

/-- The query counts of the key machine, in the form VCVio asks for. -/
theorem keyMachine_bound [Inhabited M] (F : RomForger n E X M) (qH qS ℓ : ℕ)
    (hFH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hFS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ)
    (P : Stmt C) :
    FiatShamir.signHashQueryBound (M := M) (Commit := X × X) (Chal := ZMod n)
      (S' := FSSig n X) (oa := (romMachine C F (keyFin C)).main P) qS (qH + qS + ℓ + 1) := by
  refine ⟨?_, ?_⟩
  · refine (romMachine_cost C _ 0 1 (by simp) (by simp) (by simp) F _
      (fun P items s zs signed es => keyFin_bound C _ 0 (by simp) P items s zs signed es)
      qH qS ℓ hFH hFS hL P).mono (by omega)
  · refine (romMachine_cost C _ 1 0 (by simp) (by simp) (by simp) F _
      (fun P items s zs signed es => keyFin_bound C _ 1 (by simp) P items s zs signed es)
      qH qS ℓ hFH hFS hL P).mono (by omega)

/-- **Signing simulation**, from VCVio: the key machine forges at most as often as
its simulated version, up to the simulation loss. -/
theorem keyMachine_to_nma [Inhabited M] (F : RomForger n E X M) (qH qS ℓ : ℕ)
    (hFH : ∀ input, (F.main input).IsQueryBoundP (fun t => isChalCall t) qH)
    (hFS : ∀ input, (F.main input).IsQueryBoundP (fun t => isSignCall t) qS)
    (hL : ∀ input, ∀ out ∈ support (F.main input), out.value.data.ms.length ≤ ℓ) :
    SignatureAlg.unforgeableAdvantage (FiatShamir.runtime (Commit := X × X) (Chal := ZMod n) M)
        (romMachine C F (keyFin C)) ≤
      FiatShamir.Fork.advantage (sigma C) (keyGen C) M
        (FiatShamir.cmaToNmaAdv (sigma C) (keyGen C) M (simTranscript C)
          (romMachine C F (keyFin C))) (qH + qS + ℓ + 1) +
        (qS : ℝ≥0∞) * (qS + (qH + qS + ℓ + 1 : ℕ)) * (2 / ((n - 1 : ℕ) : ℝ≥0∞)) := by
  have h := FiatShamir.euf_cma_to_nma (sigma C) (keyGen C) M (simTranscript C) (ζ_zk := 0)
    ((ChallengeVerifyProtocol.perfectHVZK_iff_hvzk_zero _ _).mp (sigma_hvzk C))
    (β := (Fintype.card (EvenNonce C) : ℝ≥0∞)⁻¹) (sigma_simCommitPredictability C)
    (romMachine C F (keyFin C)) qS (qH + qS + ℓ + 1)
    (keyMachine_bound C F qH qS ℓ hFH hFS hL)
  simp only [mul_zero, add_zero, inv_card_evenNonce] at h
  exact h

/-! ## The discrete-log solver -/

theorem romMachine_prefix (F : RomForger n E X M) (fin : FinalStep n E X M C) (P : Stmt C) :
    (romMachine C F fin).main P =
      romPrefix C F P >>= fun x => fin P x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  rw [romMachine_main_eq]
  simp only [romPrefix, bind_assoc, pure_bind]

theorem keyFin_wrong [Inhabited M] (P : Stmt C) (items : List (AItem n X M)) (s : ZMod n)
    (zs : List (ZMod n)) (signed : List M) (es : List (ZMod n))
    (h : C.mulG (candKey (knownChal items es) (C.x P.1) items s zs signed) ≠ P.1) :
    keyFin C P items s zs signed es = pure (junk C) := by
  unfold keyFin
  split
  · rfl
  · simp only [h, ↓reduceIte]

noncomputable local instance chalUniform : UniformAnswerMeasure (Unit →ₒ ZMod n) :=
  UniformAnswerMeasure.ofFiniteNonempty _

/-- For one public key: if the simulated key machine's forgery verifies, the
candidate key is the secret key. -/
theorem key_fork_pk [Inhabited M] (hx0 : C.liftX (C.x 0) = none) (F : RomForger n E X M)
    (P : Stmt C) (qH : ℕ) :
    Pr{let t ← FiatShamir.Fork.runTrace (sigma C) (keyGen C) M
        (FiatShamir.cmaToNmaAdv (sigma C) (keyGen C) M (simTranscript C)
          (romMachine C F (keyFin C))) P}[
      (FiatShamir.Fork.forkPoint (X × X) (ZMod n) (ZMod n) M qH t).isSome] ≤
      Pr{let w ← keySolver C F P}[decide (C.mulG w = P.1) = true] := by
  unfold keySolver
  refine le_of_le_of_eq ?_
    ((FiatShamir.Fork.simulateQ_uniformImpl_evalDistEq _).prEvent_eq
      (fun w => decide (C.mulG w = P.1) = true)).symm
  rw [prEvent_map]
  unfold FiatShamir.Fork.runTrace FiatShamir.cmaToNmaAdv
    FiatShamir.Stateful.nmaAdvFromCmaWithFinalQuery FiatShamir.Stateful.nmaAdvFromCma
    FiatShamir.simulatedNmaAdv
  dsimp only
  rw [romMachine_prefix]
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  refine (prEvent_bind_le_prEvent_add_of_support _ _
    (fun w => decide (C.mulG (candKey (knownChal w.1.1.1 w.1.1.2.2.2.2) (C.x P.1) w.1.1.1
      w.1.1.2.1 w.1.1.2.2.1 w.1.1.2.2.2.1) = P.1) = true) _ (ε := 0)
    fun w _ hw => ?_).trans (by simp)
  simp only [decide_eq_true_eq] at hw
  rw [keyFin_wrong C P _ _ _ _ _ hw]
  refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun t ht => ?_)
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at ht
  obtain ⟨y, -, rfl⟩ := ht
  have hv : ∀ ω : ZMod n, (sigma C).verify P (junk (M := M) C).2.1 ω (junk (M := M) C).2.2 =
      false := by
    intro ω
    simp [sigma, junk, hx0]
  intro hsome
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
  have hverified := FiatShamir.Fork.verified_of_forkPoint_eq_some (hs := hi)
  refine absurd hverified ?_
  dsimp only
  split
  · rw [hv]
    exact Bool.false_ne_true
  · exact Bool.false_ne_true

/-- **The simulated key machine forges at most as often as the solver finds the
secret key.** -/
theorem key_fork_le [Inhabited M] (hx0 : C.liftX (C.x 0) = none) (F : RomForger n E X M)
    (qH : ℕ) :
    FiatShamir.Fork.advantage (sigma C) (keyGen C) M
        (FiatShamir.cmaToNmaAdv (sigma C) (keyGen C) M (simTranscript C)
          (romMachine C F (keyFin C))) qH ≤
      Pr{let x ← hardRelationExperiment (keyGen C) (keySolver C F)}[x = true] := by
  let : MeasurableSpace (Stmt C × ZMod n) := ⊤
  let acc : Stmt C × ZMod n → ℝ≥0∞ := fun pkw =>
    Pr{let t ← FiatShamir.Fork.runTrace (sigma C) (keyGen C) M
          (FiatShamir.cmaToNmaAdv (sigma C) (keyGen C) M (simTranscript C)
            (romMachine C F (keyFin C))) pkw.1}[
      (FiatShamir.Fork.forkPoint (X × X) (ZMod n) (ZMod n) M qH t).isSome]
  let B : Stmt C × ZMod n → ℝ≥0∞ := fun pkw =>
    Pr{let w ← keySolver C F pkw.1}[decide (C.mulG w = pkw.1.1) = true]
  have hAdv : FiatShamir.Fork.advantage (sigma C) (keyGen C) M
      (FiatShamir.cmaToNmaAdv (sigma C) (keyGen C) M (simTranscript C)
        (romMachine C F (keyFin C))) qH = ∫⁻ pkw, acc pkw ∂𝒟[(keyGen C).gen] := by
    rw [FiatShamir.Fork.advantage, FiatShamir.Fork.experiment,
      (FiatShamir.Fork.simulateQ_uniformImpl_evalDistEq _).prEvent_eq,
      prEvent_bind_eq_lintegral_of_discrete, OracleComp.evalDist_liftComp_uniform]
    refine MeasureTheory.lintegral_congr fun pkw => ?_
    rcases pkw with ⟨pk, w⟩
    simp only [acc, prEvent_norm]
  have hRHS : Pr{let x ← hardRelationExperiment (keyGen C) (keySolver C F)}[x = true] =
      ∫⁻ pkw, B pkw ∂𝒟[(keyGen C).gen] := by
    rw [hardRelationExperiment, prEvent_bind_eq_lintegral_of_discrete]
    refine MeasureTheory.lintegral_congr fun pkw => ?_
    rcases pkw with ⟨pk, w⟩
    simp only [B, prEvent_norm]
  rw [hAdv, hRHS]
  exact MeasureTheory.lintegral_mono fun pkw => key_fork_pk C hx0 F pkw.1 qH

end Halfagg.Security
