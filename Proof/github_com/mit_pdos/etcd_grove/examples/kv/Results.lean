/-
The exported results of the register example (`examples/kv/kv.go`), restated at
top level, with the trust base of each printed in the build log (`#print axioms`). Every Go
function of the package has a `Spec`/`Proof` pair and a linked result (`Link.lean`,
generated); raft's functions it calls are linked in raft's `Link.lean`.

* **`Put`/`Get`** (`kv_Put`, `kv_Get`): logically atomic over the store's
  value (`kvVal`): a client hands in an atomic update at `kvMask` (everything but raft's
  commit invariant and the store's), which runs when raft commits the operation's first
  entry -- the linearization point -- and gets `Φ` back (for `Get`, of the value). Each takes
  one of its replica's `2^64 - 1` operation credits (`opCred`).
* **`Read`** (`kv_Read`, 2026-10-13): a linearizable read by raft's read index
  (`Node.ReadIndex`, `ReadOnlySafe`), stated with lower bounds on the store's history
  (`kvLb`: the client data of a committed log): given one at the call, it returns the
  value after a longer one, itself a lower bound -- the value at a point between the call
  and the return. The history at any moment is a lower bound, at the client's value
  (`kv_regLb_current`). One operation credit and one read credit (`rdCred`, from
  raft's allocation); any number of voters (since 2026-10-14, stage R).
* **`New`** (`kv_New`): a replica on its running node and storage, the shared register
  invariant and the replica's sequence-number token give `isKV` and the credits; its
  `run` goroutine drives the node (`kv_run`). Since 2026-10-15 (stage N) the node is in
  raft's dynamic mode (`KVCC`: the cluster's conf changes are one fixed change `op`, applied
  at the initial configuration and again after it), and `run` applies every committed
  conf-change entry to the node (`Node.ApplyConfChange`) before the `Advance` that
  acknowledges it.
* **`RemoveMember`** (`kv_RemoveMember`, 2026-10-15, stage N): proposes removing a
  replica from the cluster's voters (`Node.ProposeConfChange`), for a change the cluster admits
  (`CCAllowed`); nothing promised of the outcome. The store's other results hold whatever
  the configuration: the voters may change at any time.
* **The storage** (`kv_NewStorage`, `kv_storage_isStorage`,
  `kv_storage_initialState`): `*kv.Storage` meets raft's `Storage` contract
  (`isStorage`), and its `InitialState` is the empty hard state and the voters' conf state, as
  `newRaft` reads them.
* **The ghost state's allocation** (`kvStorInv_alloc`, `kvInv_alloc`, `Alloc.lean`): the
  invariants the above assume, from raft's allocation (`raft_dyn_alloc` since 2026-10-15;
  `ownRaftGhost_alloc` before).
* **The cluster driver** (`kv_Main`, `examples/kv/cluster.go`): from the register
  package's `isPkgInit` alone, `Main()` -- three replicas over raft's `Node`, an in-process
  transport, a ticker per node, and two clients, B checking that its `Get` returns what A's
  `Put` wrote, then reading by read index (unchecked), asking raft to remove replica 3 (since
  2026-10-15: the voters change at run time) and the leadership to move -- is safe: `{{ isPkgInit register }} Main() {{ RET #(); True }}`. Every ghost
  resource is allocated inside the proof (no storage registry is assumed: `kv_Main`
  takes no `[KVStor GF]`).
* **Adequacy** (`kv_cluster_safe`, `Adequacy.lean`'s `kv_adequate`): the same in
  the operational semantics, with package initialization proved (`Init.lean`): every
  execution of `initialize'(); Main()` from a fresh state has no stuck thread and no panic.

**Raft v3.7 (2026-10-16, stage R6b).** The statements are the ones above over raft v3.7's
node specs (pointer messages, getters, `proto.Unmarshal`); the transport steps the wire's copy
of each message (`deliver`). No `sorry` of the store's own.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.KVStorageInstance
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Adequacy

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- `r.Put(val)` (`Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__Put.lean`). -/
theorem kv_Put : kv.KV.Put.spec (GF := GF) (hG := hG) :=
  kv.KV.wp_Put

/-- `r.Get()` (`Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__Get.lean`). -/
theorem kv_Get : kv.KV.Get.spec (GF := GF) (hG := hG) :=
  kv.KV.wp_Get

/-- `r.Read()` (`Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__Read.lean`). -/
theorem kv_Read : kv.KV.Read.spec (GF := GF) (hG := hG) :=
  kv.KV.wp_Read

/-- **The history now is a lower bound** for `Read` (`kvLb`), at the client's value. -/
theorem kv_regLb_current (γr : KVNames) (x : List w8) :
    ⊢ kvInv (GF := GF) γr -∗ raftCommitInv γr.raft -∗ kvVal γr x ={⊤}=∗
      kvVal γr x ∗ ∃ L, kvLb γr L ∗ ⌜kvFold L = x⌝ :=
  kvLb_current γr x ⊤ CoPset.subseteq_top raftN_regN

/-- `New(id, node, storage, send)` (`Spec/github_com/mit_pdos/etcd_grove/examples/kv/New.lean`). -/
theorem kv_New : kv.New.spec (GF := GF) (hG := hG) :=
  kv.wp_New

/-- `r.RemoveMember(id)` (`Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__RemoveMember.lean`). -/
theorem kv_RemoveMember : kv.KV.RemoveMember.spec (GF := GF) (hG := hG) :=
  kv.KV.wp_RemoveMember

/-- `r.run(send)` (`Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__run.lean`). -/
theorem kv_run : kv.KV.run.spec (GF := GF) (hG := hG) :=
  kv.KV.wp_run

/-- `NewStorage(voters)` (`Spec/github_com/mit_pdos/etcd_grove/examples/kv/NewStorage.lean`). -/
theorem kv_NewStorage : kv.NewStorage.spec (GF := GF) (hG := hG) :=
  kv.wp_NewStorage

/-- **A register storage is a raft `Storage`**: the storage `NewStorage` returns (its record,
`kvStorRec`) meets raft's `Storage` contract against the store's storage model. -/
theorem kv_storage_isStorage (s ms : Loc) (γs : MemStorNames) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv -∗
      kvStorRec (GF := GF) s ms γs -∗ isStorage (kvStorIface s) :=
  kvStorage_isStorage kv.Storage.wp_Snapshot s ms γs

/-- ... and its `InitialState` is a fresh empty hard state and the voters' conf state, read-only
for good, as `RestartNode` asks of its storage (raft v3.7: `RestartNode.spec`'s premise). -/
theorem kv_storage_initialState (s : Loc) (vsl : GoSlice) (voters : List w64)
    (σ : StorState) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv -∗
      s.[RStorage, go!"voters"] ↦□ vsl -∗ vsl ↦*□ voters -∗
      □ (∀ (Φ : val → IProp GF) (ss' : entryID),
           ownStorage (kvStorIface s) { σ with ss := ss' } -∗
           (∀ (hp cs : Loc) (al : Bool), ownStorage (kvStorIface s) { σ with ss := ss' } -∗
            hsOpt hp (HardStateM.mk (W64 0) (W64 0) (W64 0)) -∗
            csPts cs DFrac.discard (kv.kvConfState voters) al -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods (go.GoType.PointerType rStorageTy) go!"InitialState" #s))
             (Val #())) {{ Φ }}) :=
  kvStorage_initialState kv.Storage.wp_InitialState s vsl voters σ

end results

/-! The top-level driver, at no storage registry (the section has no `KVStor`). -/
section main
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

/-- **The top-level driver** `Main()` (`Spec/github_com/mit_pdos/etcd_grove/examples/kv/Main.lean`):
safe from package initialization. Stated at no storage registry: the proof allocates one. -/
theorem kv_Main : kv.Main.spec (GF := GF) (hG := hG) :=
  kv.wp_Main

end main

/-! The closed theorem (`Adequacy.lean`), restated. -/
section adequacy
attribute [local instance] disk_op disk_model disk_semantics disk_interp
variable [go_gctx : GoGlobalContext]

/-- **The store's cluster driver is safe, in the operational semantics**
(`kv_adequate`): every real execution of the register package's initialization
followed by `Main()`, from a fresh state with one thread, of any length, has no stuck
thread, no thread ended in a panic, and the main thread's result, if any, is `#()` (of
fewer than `2 ^ 64 - 2` steps since D19b, 2026-10-18: raft's term budget backed by time
receipts). -/
theorem kv_cluster_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
    [hErr : context.ErrorStringIsError] [hDE : context.DeadlineExceededIsError] [hLog : log.NewModel]
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : g.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([registerProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 3 ≤ 2 ^ 64) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  kv_adequate σ g Hlctx Hinit Hthreads n κs t2 σ2 Hsteps Hn

end adequacy

#print axioms kv_Put
#print axioms kv_Get
#print axioms kv_Read
#print axioms kv_regLb_current
#print axioms kv_New
#print axioms kv_RemoveMember
#print axioms kv_run
#print axioms kv_NewStorage
#print axioms kv_storage_isStorage
#print axioms kv_storage_initialState
#print axioms kvStorInv_alloc
#print axioms kvInv_alloc
#print axioms kv_Main
#print axioms kv_adequate
#print axioms kv_cluster_safe

end EtcdGrove
end Perennial
