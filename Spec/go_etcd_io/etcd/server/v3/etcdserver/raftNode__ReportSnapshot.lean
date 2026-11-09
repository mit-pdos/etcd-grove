/-
`(*raftNode).ReportSnapshot(id, status)`: raft's, promoted. **Users**: `EtcdServer.ReportSnapshot`.
**Proof sketch**: R1's `node.ReportSnapshot.spec`. **Changes**: unchanged. **Margin**: none.
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

def raftNode.ReportSnapshot.spec : Prop :=
  ∀ (r : Loc) (γ : Names) (id : w64) (n : Loc) (to status : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode r γ id n }}
    (App (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.raftNode.ty @!!
      go!"ReportSnapshot")) (Val #to)) (Val #status))
  {{ RET #(); True }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
