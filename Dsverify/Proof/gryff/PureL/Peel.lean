/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureL/Peel.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L: tactics to take apart a model step's `do` block (`peel h` on `h : step ... = .ok r`):
binds, `if`s, `match`es, `pure`, and the failure markers.
-/
module

public import Dsverify.Proof.gryff.Pure.Run

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model

theorem bind_ok_iff {α β : Type} {x : Except Fail α} {f : α → Except Fail β} {r : β} :
    (x >>= f) = .ok r ↔ ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x <;> simp [bind, Except.bind]

theorem ite_ok_iff {α : Type} {c : Prop} {inst : Decidable c} {a b : Except Fail α} {r : α} :
    @ite _ c inst a b = .ok r ↔ (c ∧ a = .ok r) ∨ (¬ c ∧ b = .ok r) := by
  cases inst <;> simp_all

theorem pure_ok_iff {α : Type} {a r : α} : (pure a : Except Fail α) = .ok r ↔ a = r := by
  simp [pure, Except.pure]

theorem fail_ne_ok {α : Type} {r : α} : ¬ ((never : Except Fail α) = .ok r) ∧
    ¬ ((disabled : Except Fail α) = .ok r) ∧ ¬ ((dead : Except Fail α) = .ok r) := by
  simp [never, disabled, dead, FailM.failNever, FailM.failDisabled, FailM.failDead]

macro "peel" h:ident : tactic => `(tactic| (
  repeat' (first
    | (rw [bind_ok_iff] at $h:ident; obtain ⟨_, hx, $h:ident⟩ := $h:ident
       try (exfalso; first | exact fail_ne_ok.1 hx | exact fail_ne_ok.2.1 hx | exact fail_ne_ok.2.2 hx))
    | (simp only [] at $h:ident)
    | (rw [pure_ok_iff] at $h:ident)
    | (rw [ite_ok_iff] at $h:ident; rcases $h:ident with ⟨_, $h:ident⟩ | ⟨_, $h:ident⟩)
    | (exfalso; exact fail_ne_ok.1 $h:ident)
    | (exfalso; exact fail_ne_ok.2.1 $h:ident)
    | (exfalso; exact fail_ne_ok.2.2 $h:ident)
    | split at $h:ident)))



theorem obind_some_iff {α β : Type} {x : Option α} {f : α → Option β} {r : β} :
    (x >>= f) = some r ↔ ∃ a, x = some a ∧ f a = some r := by
  cases x <;> simp [bind, Option.bind]

theorem oite_some_iff {α : Type} {c : Prop} {inst : Decidable c} {a b : Option α} {r : α} :
    @ite _ c inst a b = some r ↔ (c ∧ a = some r) ∨ (¬ c ∧ b = some r) := by
  cases inst <;> simp_all

theorem opure_some_iff {α : Type} {a r : α} : (pure a : Option α) = some r ↔ a = r := by
  simp [pure]

theorem ofail_ne_some {α : Type} {r : α} : ¬ ((dead : Option α) = some r) := by
  simp [dead, FailM.failDead]

macro "opeel" h:ident : tactic => `(tactic| (
  repeat' (first
    | (rw [obind_some_iff] at $h:ident; obtain ⟨_, hx, $h:ident⟩ := $h:ident
       try (exfalso; exact ofail_ne_some hx))
    | (simp only [] at $h:ident)
    | (rw [opure_some_iff] at $h:ident)
    | (rw [oite_some_iff] at $h:ident; rcases $h:ident with ⟨_, $h:ident⟩ | ⟨_, $h:ident⟩)
    | (exfalso; exact ofail_ne_some $h:ident)
    | split at $h:ident)))

end Perennial.gryff.pure
