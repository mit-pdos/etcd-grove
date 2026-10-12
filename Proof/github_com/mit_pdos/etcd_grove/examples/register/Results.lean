/-
The exported results of the register example (`examples/register/register.go`), restated at
top level, with the trust base of each printed in the build log (`#print axioms`). Every Go
function of the package has a `Spec`/`Proof` pair and a linked result (`Link.lean`,
generated); raft's functions it calls are linked in raft's `Link.lean`.

* **`Put`/`Get`** (`register_Put`, `register_Get`): logically atomic over the register's
  value (`regVal`): a client hands in an atomic update at `regMask` (everything but raft's
  commit invariant and the register's), which runs when raft commits the operation's first
  entry -- the linearization point -- and gets `Φ` back (for `Get`, of the value). Each takes
  one of its replica's `2^64 - 1` operation credits (`opCred`).
* **`New`** (`register_New`): a replica on its running node and storage, the shared register
  invariant and the replica's sequence-number token give `isRegister` and the credits; its
  `run` goroutine drives the node (`register_run`).
* **The storage** (`register_NewStorage`, `register_storage_isStorage`,
  `register_storage_initialState`): `*register.Storage` meets raft's `Storage` contract
  (`isStorage`), and its `InitialState` is what `RestartNode` asks of its storage.
* **The ghost state's allocation** (`regStorInv_alloc`, `regInv_alloc`, `Alloc.lean`): the
  invariants the above assume, from raft's allocation (`ownRaftGhost_alloc`).
* **The cluster driver** (`register_Main`, `examples/register/cluster.go`): from the register
  package's `isPkgInit` alone, `Main()` -- three replicas over raft's `Node`, an in-process
  transport, a ticker per node, and two clients, B checking that its `Get` returns what A's
  `Put` wrote -- is safe: `{{ isPkgInit register }} Main() {{ RET #(); True }}`. Every ghost
  resource is allocated inside the proof (no storage registry is assumed: `register_Main`
  takes no `[RegStor GF]`).
* **Adequacy** (`register_cluster_safe`, `Adequacy.lean`'s `register_adequate`): the same in
  the operational semantics, with package initialization proved (`Init.lean`): every
  execution of `initialize'(); Main()` from a fresh state has no stuck thread and no panic.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.register.RegStorageInstance
public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Adequacy

@[expose] public section

-- `#print axioms` prints the axioms by their full names: shortening each name to the
-- shortest unambiguous one in this environment took most of this module's build (25s of
-- 31s for the server's `txn/Results.lean`).
set_option pp.fullNames true

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- `r.Put(val)` (`Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__Put.lean`). -/
theorem register_Put : register.Register.Put.spec (GF := GF) (hG := hG) :=
  register.Register.wp_Put

/-- `r.Get()` (`Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__Get.lean`). -/
theorem register_Get : register.Register.Get.spec (GF := GF) (hG := hG) :=
  register.Register.wp_Get

/-- `New(id, node, storage, send)` (`Spec/github_com/mit_pdos/etcd_grove/examples/register/New.lean`). -/
theorem register_New : register.New.spec (GF := GF) (hG := hG) :=
  register.wp_New

/-- `r.run(send)` (`Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__run.lean`). -/
theorem register_run : register.Register.run.spec (GF := GF) (hG := hG) :=
  register.Register.wp_run

/-- `NewStorage(voters)` (`Spec/github_com/mit_pdos/etcd_grove/examples/register/NewStorage.lean`). -/
theorem register_NewStorage : register.NewStorage.spec (GF := GF) (hG := hG) :=
  register.wp_NewStorage

/-- **A register storage is a raft `Storage`**: the storage `NewStorage` returns (its record,
`regStorRec`) meets raft's `Storage` contract against the register's storage model. -/
theorem register_storage_isStorage (s ms : Loc) (γs : MemStorNames) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register -∗
      regStorRec (GF := GF) s ms γs -∗ isStorage (regStorIface s) :=
  regStorage_isStorage register.Storage.wp_Snapshot s ms γs

/-- ... and its `InitialState` is the empty hard state and the voters, as `RestartNode` asks. -/
theorem register_storage_initialState (s : Loc) (vsl : GoSlice) (voters : List w64)
    (σ : StorState) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register -∗
      s.[RStorage, go!"voters"] ↦□ vsl -∗ vsl ↦*□ voters -∗
      □ (∀ (Φ : val → IProp GF) (ss' : entryID),
           ownStorage (regStorIface s) { σ with ss := ss' } -∗
           (ownStorage (regStorIface s) { σ with ss := ss' } -∗
            ({ (zero_val raftpb.ConfState) with Voters' := vsl } : raftpb.ConfState).Voters'
              ↦*□ voters -∗
            Φ (PairV (PairV #(zero_val raftpb.HardState)
              #({ (zero_val raftpb.ConfState) with Voters' := vsl } : raftpb.ConfState))
              #interface.nil)) -∗
           WP (App (Val #(methods (go.GoType.PointerType rStorageTy) go!"InitialState" #s))
             (Val #())) {{ Φ }}) :=
  regStorage_initialState register.Storage.wp_InitialState s vsl voters σ

end results

/-! The top-level driver, at no storage registry (the section has no `RegStor`). -/
section main
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]

/-- **The top-level driver** `Main()` (`Spec/github_com/mit_pdos/etcd_grove/examples/register/Main.lean`):
safe from package initialization. Stated at no storage registry: the proof allocates one. -/
theorem register_Main : register.Main.spec (GF := GF) (hG := hG) :=
  register.wp_Main

end main

/-! The closed theorem (`Adequacy.lean`), restated. -/
section adequacy
attribute [local instance] disk_op disk_model disk_semantics disk_interp
variable [go_gctx : GoGlobalContext]

/-- **The register's cluster driver is safe, in the operational semantics**
(`register_adequate`): every real execution of the register package's initialization
followed by `Main()`, from a fresh state with one thread, of any length, has no stuck
thread, no thread ended in a panic, and the main thread's result, if any, is `#()`. -/
theorem register_cluster_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
    [hErr : context.ErrorStringIsError] [hDE : context.DeadlineExceededIsError] [hLog : log.NewModel]
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : g.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([registerProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  register_adequate σ g Hlctx Hinit Hthreads n κs t2 σ2 Hsteps

end adequacy

#print axioms register_Put
#print axioms register_Get
#print axioms register_New
#print axioms register_run
#print axioms register_NewStorage
#print axioms register_storage_isStorage
#print axioms register_storage_initialState
#print axioms regStorInv_alloc
#print axioms regInv_alloc
#print axioms register_Main
#print axioms register_adequate
#print axioms register_cluster_safe

end EtcdGrove
end Perennial
