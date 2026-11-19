/- Lean-first (no Rocq counterpart).

# The structured-merge-diff driver's results

`smd_driver_safe`: the closed theorem about the program (`smdProgram`, `TopLevelDefs.lean`: the
driver package's initialization, then `Main()`): in every real execution from a fresh state with
one thread, the program's result is `#()`, no thread is stuck and none has an unrecovered panic.
It follows from Perennial's `goose_adequacy` (receipt bound `n + 1`, thread bound `n + 2`,
`realThreadsBelow_of_one`), the generated package initialization (`Init.lean`, at the program's
table `PkgTable.lean`) and `wp_Main` (`Link.lean`), as `init_adequate`
(`examples/lib/etcdstart/Adequacy.lean`) does, without that module's etcd imports.
`smd_driver_robust` is the same as an instance of the generic robustness statement
(`TopLevelRobustness.lean`).

`Main.wp_proof` is `sorry` for now (notes/smd-robustness.md), so the theorem rests on it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.InitLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.TopLevelDefs
public import Proof.runtime.Threads
public import Perennial.GooseLang.Adequacy

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

/-! ## The ghost-state bundle -/

/-- The functors: the universal camera (`AllG`) at slot 0, then invariants, later credits,
GooseLang's heap, prophecies and package state. -/
def smdGF : BundledGFunctors := fun i =>
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
def smdGF_allG : AllG smdGF := ⟨⟨0, rfl⟩⟩

instance smdGF_gooseGpreS : GooseGpreS smdGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨smdGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := smdGF_allG

/-! ## The program -/

section program
variable [go_gctx : GoGlobalContext]

section wp
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

/-- **The program**: it returns `#()` (`Main`'s checks never panic). -/
theorem wp_smdProgram :
    ownInitializing (github_com.mit_pdos.etcd_grove.examples.k8s.smd.getIsPkgInit (GF := GF)) ⊢ WP smdProgram {{ v, ⌜v = #()⌝ }} := by
  iintro Hown
  unfold smdProgram
  wp_apply github_com.mit_pdos.etcd_grove.examples.k8s.smd.wp_initialize' _ github_com.mit_pdos.etcd_grove.examples.k8s.smd.getIsPkgInit_wf $$ Hown as ⟨_, #Hpkg⟩
  wp_apply wp_Main
  ipureintro
  rfl

end wp

/-! ## The closed theorem -/

/-- **The driver's safety**: in every real execution of `smdProgram` of `n` steps, from a state
whose Go context satisfies the Go semantics and the package assumptions, with no package
initialized and the main thread only: if the main thread has finished, its result is `#()`; no
thread is stuck; none has an unrecovered panic. So every check of `Main` passes. -/
theorem smd_driver_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]
    (σ : state) (g : GlobalState)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([smdProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_adequacy (GF := smdGF) (n + 1) (n + 2) smdProgram σ g (fun v => v = #()) ?_
    ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ?_ n κs t2 σ2 Hsteps (by omega) Hthreads
    (realThreadsBelow_of_one Hthreads)
  · intro p h
    exact intoVal_ne_PanicV () p h.symm
  · intro hG _ _ Hlctx'
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC smdGF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    rw [Hpkgs]
    iintro _ _ Hgs _
    imodintro
    iapply wp_smdProgram
    rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro

end program

end k8s_smd
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.k8s_smd.smd_driver_safe
