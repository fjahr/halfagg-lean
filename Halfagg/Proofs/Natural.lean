import Halfagg.Proofs.Annotated

/-!
# Naturality of the reduction's bookkeeping

`coreImpl` is generic in the monad in which uniform samples, randomizers and
signatures are obtained. `coreImpl_natural`: a monad morphism `ρ` applied to a run
of `coreImpl` is the run of `coreImpl` with `ρ` applied to its three components.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp AlgebraicGroupModel.Interaction

namespace Halfagg.Security

open Taproot Taproot.Curve

attribute [local instance] smulVal

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E]
  [DecidableEq X] [DecidableEq M] (C : Curve n E X) (challenge : X → X → M → ZMod n)

theorem coreImpl_natural {m m' : Type → Type} [Monad m] [Monad m'] [LawfulMonad m]
    [LawfulMonad m'] (ρ : ∀ {α : Type}, m α → m' α)
    (hpure : ∀ {α : Type} (a : α), ρ (pure a) = pure a)
    (hbind : ∀ {α β : Type} (x : m α) (f : α → m β), ρ (x >>= f) = ρ x >>= fun a => ρ (f a))
    (pk : X) (unif : (k : ℕ) → m (Fin (k + 1))) (ro : List (AItem n X M) → m (ZMod n))
    (sg : M → m (X × ZMod n)) {Result : Type}
    (prog : OracleComp (explainedSpec (ZMod n) (Pts E) (Request M) (Reply n M)) Result)
    (st : Core n X M) :
    ρ ((simulateQ (coreImpl C challenge pk unif ro sg) prog).run st) =
      (simulateQ (coreImpl C challenge pk (fun k => ρ (unif k)) (fun l => ρ (ro l))
        (fun msg => ρ (sg msg))) prog).run st := by
  have hmap : ∀ {α β : Type} (f : α → β) (x : m α), ρ (f <$> x) = f <$> ρ x := by
    intro α β f x
    rw [map_eq_bind_pure_comp, hbind, map_eq_bind_pure_comp]
    exact bind_congr fun a => hpure _
  induction prog using OracleComp.inductionOn generalizing st with
  | pure x => simp [hpure]
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [hbind]
    have hstep : ρ ((coreImpl C challenge pk unif ro sg t).run st) =
        (coreImpl C challenge pk (fun k => ρ (unif k)) (fun l => ρ (ro l))
          (fun msg => ρ (sg msg)) t).run st := by
      obtain ⟨⟨data, groups⟩, coeffs⟩ := t
      cases data <;> simp [coreImpl, StateT.run, hmap]
    rw [hstep]
    exact bind_congr fun r => ih r.1 r.2

/-! ## One request -/

section Run

variable {m : Type → Type} [Monad m] (pk : X) (unif : (k : ℕ) → m (Fin (k + 1)))
  (ro : List (AItem n X M) → m (ZMod n)) (sg : M → m (X × ZMod n))
  (groups : Groups (Pts E)) (coeffs : Unit → List (List (ZMod n))) (st : Core n X M)

theorem coreImpl_run_random (k : ℕ) :
    (coreImpl C challenge pk unif ro sg ⟨⟨.random k, groups⟩, coeffs⟩).run st =
      (do let u ← unif k; pure (⟨u, fun _ => []⟩, st)) := rfl

theorem coreImpl_run_rand (ms : List M) :
    (coreImpl C challenge pk unif ro sg ⟨⟨.rand ms, groups⟩, coeffs⟩).run st =
      (do
        let z ← ro (annotate (memoize C st (groups ()) (coeffs ())).memo
          (toItems C ms (groups ())))
        pure (⟨z, fun _ => []⟩, memoize C st (groups ()) (coeffs ()))) := rfl

theorem coreImpl_run_sign (msg : M) :
    (coreImpl C challenge pk unif ro sg ⟨⟨.sign msg, groups⟩, coeffs⟩).run st =
      (do
        let sig ← sg msg
        pure (⟨sig.2, fun _ => [(C.liftX sig.1).getD 0]⟩,
          { st with basis := st.basis ++ [(sig.2, -challenge sig.1 pk msg)]
                    signed := st.signed ++ [msg] })) := rfl

end Run

end Halfagg.Security
