/-
`(*EtcdServer).IsIDRemoved(id)` (`server.go:724`): the membership's `IsIDRemoved`.

**Users**: rafthttp (2f: its `Raft` contract's `IsIDRemoved`, with a thread token: the membership
is read under its lock), the driver's `processMessages` (through `isIDRemoved`, `raft.go:374`).
**Proof sketch**: 2e's `Membership.RaftCluster.IsIDRemoved` (a read under the cluster's lock: the
thread token backs the reader slot). **Changes**: new (no old spec). **Margin**: the answer is not
described (no user relies on it for safety: a message to a removed member is merely dropped).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

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

def EtcdServer.IsIDRemoved.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvNode s γ id ∗
      threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"IsIDRemoved")) (Val #x))
  {{ (b : Bool), RET #b; threadTok }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
