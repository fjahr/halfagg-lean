import Halfagg.Proofs.Invariant

/-!
# Facts about the BIP340 scheme `bip340`

* `keygen_support`: a generated key pair is `(x(d⋅G), d)` for a nonzero `d`.
* `sign_support`: every signature `(r, s)` the signing algorithm returns under
  such a key satisfies `lift_x(r) = s⋅G - e⋅P*`, with `P*` the even-y point of
  the public key, in the form `core_inv` asks for.
-/

set_option linter.unusedSectionVars false

namespace Halfagg.Security

open OracleSpec OracleComp Taproot Taproot.Curve Taproot.BIP340 Taproot.BIP340Security

variable {n : ℕ} [Fact n.Prime] {H E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)
variable [SampleableType H] {red : H → ZMod n}

/-- The signing equation of a BIP340 signature, over the normalized key. -/
theorem sign_rep {d k : ZMod n} (hd : d ≠ 0) (hk : k ≠ 0) (msg : M) :
    let sig := (BIP340.sign C challenge (fun _ _ _ => k) d msg).getD (C.x (C.mulG d), 0)
    C.liftX sig.1 = some (repPoint C (C.evenScalar d)
      (sig.2, -challenge sig.1 (C.x (C.mulG d)) msg)) := by
  have hs : ∃ sig, BIP340.sign C challenge (fun _ _ _ => k) d msg = some sig := by
    unfold BIP340.sign; simp [hd, hk]
  obtain ⟨sig, hsig⟩ := hs
  simp only [hsig, Option.getD_some]
  have hv := verify_sign C challenge (fun _ _ _ => k) (pk := C.x (C.mulG d))
    (by simp [pubkey, hd]) hsig
  obtain ⟨r, s⟩ := sig
  obtain ⟨P, hP, hR⟩ := (verify_eq_true_iff C challenge).mp hv
  rw [C.liftX_x_mulG hd, Option.some.injEq] at hP
  subst hP
  rw [hR, C.val_smul_mulG, ← map_sub, repPoint]
  congr 2
  ring

variable {κ : Type} {S : OracleSpec κ}

theorem keygen_support (ks : X × ZMod n)
    (h : ks ∈ support (bip340 (M := M) C challenge (OracleComp (unifSpec + S))).keygen) :
    ks.2 ≠ 0 ∧ ks.1 = C.x (C.mulG ks.2) := by
  simp only [bip340] at h
  rw [show ∀ (x : ProbComp (X × ZMod n)), (monadLift x : OracleComp (unifSpec + S) _) =
    liftComp x (unifSpec + S) from fun _ => (liftComp_eq_liftM _).symm, support_liftComp] at h
  have h' := h
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h'
  obtain ⟨d, -, rfl⟩ := h'
  exact ⟨d.2, rfl⟩

theorem sign_support {d : ZMod n} (hd : d ≠ 0) (msg : M) (sig : X × ZMod n)
    (h : sig ∈ support ((bip340 (M := M) C challenge (OracleComp (unifSpec + S))).sign
      (C.x (C.mulG d)) d msg)) :
    C.liftX sig.1 = some (repPoint C (C.evenScalar d)
      (sig.2, -challenge sig.1 (C.x (C.mulG d)) msg)) := by
  simp only [bip340] at h
  rw [show ∀ (x : ProbComp (X × ZMod n)), (monadLift x : OracleComp (unifSpec + S) _) =
    liftComp x (unifSpec + S) from fun _ => (liftComp_eq_liftM _).symm, support_liftComp] at h
  have h' := h
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h'
  obtain ⟨k, -, rfl⟩ := h'
  exact sign_rep C challenge hd k.2 msg

end Halfagg.Security
