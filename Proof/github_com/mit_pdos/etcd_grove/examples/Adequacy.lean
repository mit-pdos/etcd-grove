/- Lean-first (no Rocq counterpart).

# Adequacy of a Go `main` package, for the examples (2026-10-17)

What every example's closed theorem shares, so that each states only its program:

* `MainSafe prog σ`: every real execution of `prog` from the state `σ` with one live thread,
  of any length, has no stuck thread, no thread ended in a panic, and the main thread's
  result, if it has one, is `#()`;
* `mainSafe_of_wp`: `MainSafe prog σ` from a fresh state (`IsInit σ`: no package
  initialized) given a WP of `prog` from `ownInitializing` (what a package's `wp_initialize'`
  takes), at the functor bundle `exampleGF` and the disk FFI (the examples' proofs are
  generic over the FFI; the disk's adequacy instance has trivial initial-state conditions).

It follows from Perennial's `goose_adequacy` (whose third conclusion, no thread has an
unrecovered panic, gives the second), with the thread bound from `threads_le_steps` (one step
forks at most one thread). Like every Perennial result it is parametric in the Go semantics:
the `GoGlobalContext`, the language semantics `go.Semantics` at the state's local context and,
in an example's statement, the package assumptions of its `main` package (which include its
imports'), are instance arguments.
-/
module

public import Perennial.GooseLang.Ffi.DiskFfi.Adequacy
public import Perennial.Golang.Theory.Pkg

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

/-! ## The ghost-state bundle -/

attribute [local instance] disk_op disk_model disk_semantics disk_interp

/-- The functors: the universal camera (`AllG`) at slot 0, then invariants, later credits,
GooseLang's heap, prophecies and package state, and the disk FFI's heap. Every other slot
is the unit functor. -/
def exampleGF : BundledGFunctors := fun i =>
  match i with
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)),
          inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | 8 => ⟨constOF (HeapView Int (Agree (DiscreteO Block)) (GMap Int)), inferInstance⟩
  | 9 => ⟨constOF (HeapView Int (Agree (DiscreteO GName)) (GMap Int)), inferInstance⟩
  | 10 => ⟨constOF MetaUR, inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- The universal camera at slot 0 (not an instance: under a `HeapGS` the `AllG` is the one
it carries, `GooseGlobalGS.gooseAllG`). -/
def exampleGF_allG : AllG exampleGF := ⟨⟨0, rfl⟩⟩

instance exampleGF_gooseGpreS : GooseGpreS disk_model exampleGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGFfi := (⟨⟨⟨⟨8, rfl⟩⟩, ⟨⟨9, rfl⟩⟩, ⟨10, rfl⟩⟩⟩ : DiskPreG exampleGF)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := exampleGF_allG

/-! ## Safety of a `main` package's program -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- **`prog` is safe from `σ`.** Every real execution of `prog` from `σ` with one live
thread, of any length `n`: if the main thread has finished, its result is `#()`; no thread
is stuck (each is a value or can step); no thread has ended in a panic. -/
def MainSafe (prog : Expr) (σ : state) : Prop :=
  ∀ (g : GlobalState), g.threads = 1 →
  ∀ (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState),
    RealNsteps n ([prog], ((σ, g) : CfgState)) κs (t2, σ2) →
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false)

/-- **Adequacy for a `main` package.** `prog` is safe from a fresh state `σ` (no package
initialized) at the local context `lctx` if, under every `HeapGS` at `lctx`, it has a WP
whose postcondition is `#()` from `ownInitializing get_is_pkg_init` (for a `get_is_pkg_init`
of the proof's choosing: what the main package's `wp_initialize'` takes). -/
theorem mainSafe_of_wp [lctx : GoLocalContext] (prog : Expr) (σ : state)
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hwp : ∀ [hG : HeapGS .hasLC exampleGF], hG.goose_localGS.goose_go_local_context = lctx →
      ∃ get_is_pkg_init : GoString → IProp exampleGF,
        ⊢ ownInitializing get_is_pkg_init -∗ WP prog @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}) :
    MainSafe prog σ := by
  intro g Hthreads n κs t2 σ2 Hsteps
  suffices H : (∀ v t2', t2 = Val v :: t2' → v = #()) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) by
    refine ⟨H.1, H.2.1, fun v hv => ?_⟩
    cases h : v.isPanic
    · rfl
    · obtain ⟨p, rfl⟩ := val.isPanic_eq_true h
      exact absurd (UnrecoveredPanic.panic p) (H.2.2 _ hv)
  refine goose_adequacy (GF := exampleGF) (n + 1) (n + 2) prog σ g
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) trivial trivial ?_
    n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads (realThreadsBelow_of_one Hthreads)
  intro hG _ _ HL
  obtain ⟨get_is_pkg_init, Hwp⟩ := Hwp (hG := hG) (HL.trans Hlctx)
  unfold IsInit at Hinit
  rw [Hinit]
  iintro _ _ Hgs Htok
  ihave Hown : ownInitializing get_is_pkg_init $$ [Hgs]
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    imodintro
    iapply BigSepM.bigSepM_empty.2
    itrivial
  imodintro
  iapply Hwp
  iexact Hown

end adequacy

end EtcdGrove
end Perennial
