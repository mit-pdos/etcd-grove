/-
**The thread count of a real execution** (moved here from the register example's
`Adequacy.lean`, 2026-10-18, for the adequacy example `putget` too): one step forks at most one
thread, so an execution of `n` steps from one live thread stays below `n + 2` threads
(`realThreadsBelow_of_one`), the thread bound a closed theorem gives `goose_adequacy`.
-/
module

public import Perennial.GooseLang.Adequacy

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The thread count grows by at most one per step -/

section threads
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiSemantics ext ffi] [GoGlobalContext]

/-- A real thread-pool step adds at most one live thread. -/
theorem realStep_threads_le {ρ₁ ρ₂ : List Expr × CfgState} {κ : List Observation}
    (h : @Language.Step _ _ _ _ gooseRealLang ρ₁ κ ρ₂) :
    ρ₂.2.2.threads ≤ ρ₁.2.2.threads + 1 := by
  obtain ⟨H, t₁, t₂⟩ := h
  rename_i e σ e' σ' eₜ
  obtain ⟨hb⟩ := H
  rename_i e₁ e₂ K
  simp only
  rcases hk : redexKind e₁ with _ | _ | _ | _
  · have := baseStep_threads hb (by simp [hk]) (by simp [hk]); omega
  · obtain ⟨e₀, rfl⟩ := redexKind_eq_fork hk
    rcases hb with ⟨hu⟩ | ⟨_, hb⟩
    · exact absurd hu (not_unwinds_Fork _ _)
    cases hb
    simp
  · have := redexKind_eq_exit hk
    subst this
    rcases hb with ⟨hu⟩ | ⟨_, hb⟩
    · exact absurd hu (not_unwinds_ThreadExit _)
    cases hb
    simp; omega
  · have := baseStep_threads hb (by simp [hk]) (by simp [hk]); omega

/-- After `k` real steps, at most `k` more threads are live. -/
theorem threads_le_steps {k : Nat} {ρ₁ ρ₂ : List Expr × CfgState} {κs : List Observation}
    (h : RealNsteps k ρ₁ κs ρ₂) : ρ₂.2.2.threads ≤ ρ₁.2.2.threads + k := by
  unfold RealNsteps at h
  induction h with
  | refl ρ => omega
  | cons hstep _ ih => have := realStep_threads_le hstep; omega

/-- Any execution of `n` steps from one live thread stays below `n + 2` threads. -/
theorem realThreadsBelow_of_one {n : Nat} {ρ : List Expr × CfgState} (h1 : ρ.2.2.threads = 1) :
    RealThreadsBelow (n + 2) n ρ := by
  intro k κs ρ' hk hsteps
  have := threads_le_steps hsteps
  omega

end threads

end EtcdGrove
end Perennial
