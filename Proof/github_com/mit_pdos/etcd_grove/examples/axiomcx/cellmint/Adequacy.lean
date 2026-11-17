/-
The closed theorem for the `cellmint` demonstration: every real execution of
`initialize'(); Main()` from a fresh state, of fewer than `2^63` steps, never gets stuck, has no
thread end in a panic, and the main thread's result, if any, is `#()`.

In Go, `Main` panics (`cellmint_test.go`). This theorem says it does not -- it rests on the cell's
trust-boundary axioms (`Trusted.lean`), one of which (`cellmint.Snapshot.wp_proof`) is unsound.
The structure mirrors `counter_adequate` (`examples/lib/lintest/counter/Adequacy.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.Run
public import Proof.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.PkgTable
public import Proof.runtime.Threads
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TrivialExt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint

/-! ## The ghost-state bundle (the register's, no non-atomic invariants). -/

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

def cellmintGF : BundledGFunctors := fun i =>
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

def cellmintGF_allG : AllG cellmintGF := ⟨⟨0, rfl⟩⟩

instance cellmintGF_gooseGpreS : GooseGpreS cellmintGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨cellmintGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := cellmintGF_allG

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

def cellmintProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.Main) #()

/-- **`Main` is safe, in the operational semantics**: every real execution of `cellmintProgram`
(the package's initialization, then `Main()`) from a fresh state -- no package initialized, one
thread -- of `n < 2^63` steps: if the main thread has finished, its result is `#()`; no thread is
stuck; no thread has ended in a panic. In Go, `Main` panics: this theorem holds only because the
cell's trust-boundary axioms are unsound. -/
theorem cellmint_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.Assumptions]
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n < 2 ^ 63) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([cellmintProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  refine init_adequate (GF := cellmintGF) github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.initialize' ((@! github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.Main) #())
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) σ g ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ Hlctx Hinit
    Hthreads n κs t2 σ2 Hsteps fun hG _ _ => ?_
  letI : HeapGS .hasLC cellmintGF := heapWith hG lctx
  unfold progOk0
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.getIsPkgInit_wf, ?_⟩
  iintro #Hpkg -
  wp_apply Main.wp_axioms $$ [Hpkg]
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.cellmint_adequate
