/-
`(*raftNode).ReadState()` (`raft.go:450-452`): `r.readStateC`. **Users**: the read loop
(`read/read.go`, 2c's `readEnv`: `rf.ReadState()`, receives with R1's `readState`). Snippet
`raftnode.go` (`ReqReadIndex`). **Changes**: over `rnReadStateC` (`readStateC_recv`). **Margin**:
none.
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

def raftNode.ReadState.spec : Prop :=
  ∀ (r : Loc) (γ : Names) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode r γ id n }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.raftNode.ty @!!
      go!"ReadState")) (Val #()))
  {{ (ch : Loc), RET #ch; rnReadStateC r ch }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
