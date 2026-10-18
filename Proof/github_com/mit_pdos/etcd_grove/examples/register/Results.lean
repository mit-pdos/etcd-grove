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
* **`Read`** (`register_Read`, 2026-10-13): a linearizable read by raft's read index
  (`Node.ReadIndex`, `ReadOnlySafe`), stated with lower bounds on the register's history
  (`regLb`: the client data of a committed log): given one at the call, it returns the
  value after a longer one, itself a lower bound -- the value at a point between the call
  and the return. The history at any moment is a lower bound, at the client's value
  (`register_regLb_current`). One operation credit and one read credit (`rdCred`, from
  raft's allocation); any number of voters (since 2026-10-14, stage R).
* **`New`** (`register_New`): a replica on its running node and storage, the shared register
  invariant and the replica's sequence-number token give `isRegister` and the credits; its
  `run` goroutine drives the node (`register_run`). Since 2026-10-15 (stage N) the node is in
  raft's dynamic mode (`RegCC`: the cluster's conf changes are one fixed change `op`, applied
  at the initial configuration and again after it), and `run` applies every committed
  conf-change entry to the node (`Node.ApplyConfChange`) before the `Advance` that
  acknowledges it.
* **`RemoveMember`** (`register_RemoveMember`, 2026-10-15, stage N): proposes removing a
  replica from the cluster's voters (`Node.ProposeConfChange`), for a change the cluster admits
  (`CCAllowed`); nothing promised of the outcome. The register's other results hold whatever
  the configuration: the voters may change at any time.
* **The storage** (`register_NewStorage`, `register_storage_isStorage`,
  `register_storage_initialState`): `*register.Storage` meets raft's `Storage` contract
  (`isStorage`), and its `InitialState` is the empty hard state and the voters' conf state, as
  `newRaft` reads them.
* **The ghost state's allocation** (`regStorInv_alloc`, `regInv_alloc`, `Alloc.lean`): the
  invariants the above assume, from raft's allocation (`raft_dyn_alloc` since 2026-10-15;
  `ownRaftGhost_alloc` before).
* **The cluster driver** (`register_Main`, `examples/register/cluster.go`): from the register
  package's `isPkgInit` alone, `Main()` -- three replicas over raft's `Node`, an in-process
  transport, a ticker per node, and two clients, B checking that its `Get` returns what A's
  `Put` wrote, then reading by read index (unchecked), asking raft to remove replica 3 (since
  2026-10-15: the voters change at run time) and the leadership to move -- is safe: `{{ isPkgInit register }} Main() {{ RET #(); True }}`. Every ghost
  resource is allocated inside the proof (no storage registry is assumed: `register_Main`
  takes no `[RegStor GF]`).
* **Adequacy** (`register_cluster_safe`, `Adequacy.lean`'s `register_adequate`): the same in
  the operational semantics, with package initialization proved (`Init.lean`): every
  execution of `initialize'(); Main()` from a fresh state has no stuck thread and no panic.

**Raft v3.7 (2026-10-16, stage R6b).** The statements are the ones above over raft v3.7's
node specs (pointer messages, getters, `proto.Unmarshal`); the transport steps the wire's copy
of each message (`deliver`). No `sorry` of the register's own.
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

/-- `r.Read()` (`Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__Read.lean`). -/
theorem register_Read : register.Register.Read.spec (GF := GF) (hG := hG) :=
  register.Register.wp_Read

/-- **The history now is a lower bound** for `Read` (`regLb`), at the client's value. -/
theorem register_regLb_current (γr : RegNames) (x : List w8) :
    ⊢ regInv (GF := GF) γr -∗ raftCommitInv γr.raft -∗ regVal γr x ={⊤}=∗
      regVal γr x ∗ ∃ L, regLb γr L ∗ ⌜regFold L = x⌝ :=
  regLb_current γr x ⊤ CoPset.subseteq_top raftN_regN

/-- `New(id, node, storage, send)` (`Spec/github_com/mit_pdos/etcd_grove/examples/register/New.lean`). -/
theorem register_New : register.New.spec (GF := GF) (hG := hG) :=
  register.wp_New

/-- `r.RemoveMember(id)` (`Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__RemoveMember.lean`). -/
theorem register_RemoveMember : register.Register.RemoveMember.spec (GF := GF) (hG := hG) :=
  register.Register.wp_RemoveMember

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

/-- ... and its `InitialState` is a fresh empty hard state and the voters' conf state, read-only
for good, as `RestartNode` asks of its storage (raft v3.7: `RestartNode.spec`'s premise). -/
theorem register_storage_initialState (s : Loc) (vsl : GoSlice) (voters : List w64)
    (σ : StorState) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register -∗
      s.[RStorage, go!"voters"] ↦□ vsl -∗ vsl ↦*□ voters -∗
      □ (∀ (Φ : val → IProp GF) (ss' : entryID),
           ownStorage (regStorIface s) { σ with ss := ss' } -∗
           (∀ (hp cs : Loc) (al : Bool), ownStorage (regStorIface s) { σ with ss := ss' } -∗
            hsOpt hp (HardStateM.mk (W64 0) (W64 0) (W64 0)) -∗
            csPts cs DFrac.discard (register.regConfState voters) al -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
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
thread, no thread ended in a panic, and the main thread's result, if any, is `#()` (of
fewer than `2 ^ 64 - 2` steps since D19b, 2026-10-18: raft's term budget backed by time
receipts). -/
theorem register_cluster_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
    [hErr : context.ErrorStringIsError] [hDE : context.DeadlineExceededIsError] [hLog : log.NewModel]
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : g.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([registerProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 3 ≤ 2 ^ 64) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  register_adequate σ g Hlctx Hinit Hthreads n κs t2 σ2 Hsteps Hn

end adequacy

#print axioms register_Put
#print axioms register_Get
#print axioms register_Read
#print axioms register_regLb_current
#print axioms register_New
#print axioms register_RemoveMember
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
