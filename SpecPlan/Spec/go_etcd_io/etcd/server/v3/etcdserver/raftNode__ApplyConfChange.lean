/-
`(*raftNode).ApplyConfChange(cc)`: raft's `Node.ApplyConfChange`, promoted, with a legacy
`*ConfChange`. **Users**: `applyConfChange` (`server.go:2039, 2050`).

**Proof sketch**: R1's `node.ApplyConfChange.spec`, with the node's configuration view the apply
thread holds (`nodeConf`), the entry delivered (`deliveredLb`) and decided (`confDecided`, the
cluster's decision, R1's `confDecide`). **Changes**: unchanged (R1's). **Margin**: R1's.

Changes: verify-round (raft-core's request): the returned `ConfState` is raftpb's `confStateFull` (`node.ApplyConfChange` returns it so: its `AutoLeave` set), which the apply thread keeps as `ep.confState` for snapshots.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

def raftNode.ApplyConfChange.spec : Prop :=
  ∀ (r : Loc) (γ : Names) (id : w64) (n : Loc) (ccp : Loc) (dq : DFrac) (c : Raft.ConfChangeV1)
    (v : Raft.ConfView) (l : List Raft.LogEntry) (k : Nat) (m' : Raft.Membership),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isRaftNode r γ id n ∗
      Raft.confChangePts (interface.mkOk
        (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.ConfChange.ty) #ccp) dq (.v1 c) ∗
      Raft.nodeConf n γ.raft v ∗ Raft.deliveredLb n γ.raft l ∗ Raft.confDecided γ.raft k (.apply (.v1 c)) ∗
      ⌜(∃ e, l[k]? = some e ∧ e.isConfChange) ∧ Raft.Membership.applyChange (.v1 c) v.membership = some m'⌝ ∗
      (if v.applied ≤ k then Raft.confSkipped γ.raft l v.applied k else iprop(⌜m' = v.membership⌝)) }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.raftNode.ty @!!
      go!"ApplyConfChange")) (Val #ccp))
  {{ (csp : Loc), RET #csp;
      Raft.confChangePts (interface.mkOk
        (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.ConfChange.ty) #ccp) dq (.v1 c) ∗
      ((∃ cs, RaftPb.confStateFull csp (DFrac.own 1) cs ∗ ⌜cs.Is m'⌝ ∗
          Raft.nodeConf n γ.raft (if v.applied ≤ k then ⟨k + 1, m'⟩ else v)) ∨
       (⌜csp = null⌝ ∗ Raft.nodeStopped n ∗ Raft.nodeConf n γ.raft v)) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
