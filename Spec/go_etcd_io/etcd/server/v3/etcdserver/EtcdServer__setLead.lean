/-
`(*EtcdServer).setLead(v)` (`server.go:1730`): an atomic store (the ready handler's `updateLead`).
The value carries no fact: leadership checks (`isLeader`, 2c's `Lead()`) are hints, never relied on
for safety. **Changes**: over `leadW`. **Margin**: none.
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

def EtcdServer.setLead.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : w64) (v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ leadW s }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"setLead")) (Val #v))
  {{ RET #(); leadW s }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
