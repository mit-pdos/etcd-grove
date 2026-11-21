/- Lean-first (no Rocq counterpart).

# `k8s/authz`: the results (Kubernetes' conditional authorization, KEP-5681)

* **`k8s_authz_Main`** (`Link.lean`'s `wp_Main`): `Main` does not panic, from `isPkgInit` of the
  driver. Proved from its callees' specs (`Main.lean`, `twoPhase.lean`: C1-C3 follow from the
  specs of `PossibleDecisions`, `FailureDecision` and the union authorizer's
  `EvaluateConditions`, through the invariant of decisions `authorizer.Dec.WF`), the rest of the
  call graph proved and linked (`Link.lean`; no `sorry`: over trust-boundary specs of the opaque
  callees only).
* **`k8s_authz_safe`**: the closed theorem. Every real execution of `n` steps of the driver's
  initialization followed by `Main()`, from a fresh state (no package initialized,
  one thread): if the main thread has finished, its result is `#()`; no thread is stuck; no thread
  has an unrecovered panic. From Perennial's `goose_adequacy` directly (as `goose/prophkv`'s
  closed theorem; 2026-11-20, until then through `etcdstart`'s `init_adequate`, whose import
  brought etcd's server into this example's closure), at the extensions `idIssueExts` (the issue
  record alone, `GooseLang/Ext/IdIssue/Specs.lean`: the same closure as `etcdstart`'s
  `trivialExts`, which the other examples name), the ghost-state bundle `authzGF`, the generated
  package initialization (`Init.lean`, at the program's table `PkgTable.lean`) and `wp_Main`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.authz.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.authz.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.authz.PkgTable
public import GooseLang.Ext.IdIssue.Specs
public import Perennial.GooseLang.Adequacy
public import Robustness.Statement

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_authz

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.authz.Assumptions]

/-- **`Main` does not panic** (`Link.lean`'s `wp_Main`). -/
theorem k8s_authz_Main : Main.spec (GF := GF) (hG := hG) := wp_Main

end results

/-! ## The ghost-state bundle -/

attribute [local instance] idIssueExts idIssueExtsSemantics idIssueExtsInterp idIssueExts_hasExt

/-- The functors: the universal camera (`AllG`) at slot 0, then invariants, later credits,
GooseLang's heap, prophecies and package state. Every other slot is the unit functor. -/
def authzGF : BundledGFunctors := fun i =>
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
  | _ => ⟨constOF Unit, inferInstance⟩

/-- The universal camera at slot 0. -/
def authzGF_allG : AllG authzGF := ⟨⟨0, rfl⟩⟩

instance authzGF_gooseGpreS : GooseGpreS authzGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨authzGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := authzGF_allG

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- An execution of at most `n` steps from a single thread has fewer than `n + 2` live threads. -/
theorem realThreadsBelow_single {n : Nat} {ρ : List Expr × CfgState}
    (h1 : ρ.2.1.threads = 1) : RealThreadsBelow (n + 2) n ρ := by
  intro k κs ρ' hk h
  have := real_nsteps_threads h
  omega

/-- **Conditional authorization never panics** (see the file header). Parametric in the Go
semantics: any `go.Semantics` at the state's local context and any package assumptions (the
translated bodies behind the driver's, the authorizer's, the union's and their imports' names). -/
theorem k8s_authz_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.authz.Assumptions]
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([github_com.mit_pdos.etcd_grove.examples.k8s.authz.initialize' #() ;;
        (@! github_com.mit_pdos.etcd_grove.examples.k8s.authz.Main) #()], ((σ, g) : CfgState)) κs
        (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_adequacy (GF := authzGF) (n + 1) (n + 2) _ σ g (fun v => v = #())
    (fun p h => intoVal_ne_PanicV () p h.symm) ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ?_
    n κs t2 σ2 Hsteps (by omega) Hthreads (realThreadsBelow_single Hthreads)
  intro hG _ _ Hlctx'
  rw [Hlctx] at Hlctx'
  obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
  subst Hlctx'
  letI hG : HeapGS .hasLC authzGF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
  unfold IsInit at Hinit
  rw [Hinit]
  iintro - - Hgs -
  imodintro
  wp_apply github_com.mit_pdos.etcd_grove.examples.k8s.authz.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.k8s.authz.getIsPkgInit_wf $$ [Hgs] as ⟨-, #Hpkg⟩
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  wp_apply wp_Main
  ipureintro
  rfl

end adequacy

end k8s_authz
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.k8s_authz.k8s_authz_Main
#print axioms Perennial.EtcdGrove.k8s_authz.k8s_authz_safe
