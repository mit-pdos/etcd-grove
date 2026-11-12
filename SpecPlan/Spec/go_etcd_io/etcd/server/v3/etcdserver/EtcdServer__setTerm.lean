/-
`(*EtcdServer).setTerm(v)` (`server.go:1722`): an atomic store (`apply`'s, each applied entry's
term). The value carries no fact (2c's `Term()` reports it in headers only).
**Changes**: over `termW`. **Margin**: none.
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

def EtcdServer.setTerm.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ termW s }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"setTerm")) (Val #v))
  {{ RET #(); termW s }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
