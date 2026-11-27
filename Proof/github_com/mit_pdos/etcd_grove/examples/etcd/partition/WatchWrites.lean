/-
**The writers' puts through the cluster's clients** (W4d of `notes/watch-cut-plan.md`,
2026-10-22; over etcd's KV state since 2026-10-26, D45/D48). Lean-first (no Rocq counterpart).

* `memberPut γk x`: a member as a writer's put sees it: etcd's KV registered at its bridge
  (`kvRegsAt`), its store's empty log certified (`idxCert_nil`), its KV state variable the
  cluster's (`γk`'s: the updates read only that, `kvOpAu1_names`).
* `client_Put_km`: `cli.Put` through a client of the members `ms` (failover, its writes sent at
  most once, D29) with the writer's update at `γk` (`client_Put_rep`): `nil`, the update's result
  `Q σ` at the state `σ` it met (a log's state: no compaction, revision `1` or more) and the
  reply's revision `σ`'s next; or an error.
* `wsInvH`: the writers' log's lock invariant (watchkv's `wsInv`), its records' `okFactK`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WatchWkKV
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Base
public import Proof.go_etcd_io.etcd.client.v3.ReadUpds
public import Proof.go_etcd_io.etcd.client.v3.PerTypeKVRest
public import Proof.go_etcd_io.etcd.client.v3.PerTypeLease
public import Proof.go_etcd_io.etcd.client.v3.LeaseClient
public import Proof.go_etcd_io.etcd.client.v3.PerTypeAuth
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.PerTypeWatch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerRFacts
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServerR
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Compact
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Lemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.NetErr
public import Spec.sort.SortAnyLess
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadRaft
public import Proof.go_etcd_io.etcd.pkg.v3.wait.TimeListIfc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LessorOk
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.LessorDerive
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAllocOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AdminEntryOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyAllSnapLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunAdapt
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchClass
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthService
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.QuotaLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerLeaseRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerLeaseRevoke
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.QuotaLeaseLemmas
public import Proof.go_etcd_io.etcd.client.v3.KVServiceOn
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_partition

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver
open go_etcd_io.etcd.api.v3 go_etcd_io.etcd.client.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A member as a writer's put sees it** (persistent; see the file header). -/
def memberPut (γk : KVNames) (x : client.SrvAt GF) : IProp GF :=
  iprop(client.kvRegsAt x ∗ srvApi.kvLogLb x.E.γs [] ∗ ⌜x.γr.kv.st = γk.st⌝)

instance memberPut_persistent (γk : KVNames) (x : client.SrvAt GF) :
    Persistent (memberPut (GF := GF) γk x) := by
  unfold memberPut; infer_instance

/-- **The writers' log's lock invariant** (watchkv's `wsInv`, its records' `okFactK`). -/
def wsInvH (w : Loc) (γ : client.KMNames) : IProp GF :=
  iprop(∃ (sl : GoSlice) (oks : List wrec),
    structFieldRef github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes go!"Ok" w ↦ sl ∗
    sl ↦* oks ∗ ownSliceCap wrec sl (DFrac.own 1) ∗ □ [∗list] p ∈ oks, okFactK γ p)

end defs

end etcd_partition
end EtcdGrove
end Perennial
