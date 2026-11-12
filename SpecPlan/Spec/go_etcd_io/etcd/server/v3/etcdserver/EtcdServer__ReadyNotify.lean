/-
## `(*EtcdServer).ReadyNotify()` (`server.go:1364`): names only

**Users.** embed's `serve.go:136` (serving after the member published itself). **Why it is true.**
The field `NewServer` set. **Changes**: new. **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The channel closed once the member published itself.** -/
def EtcdServer.ReadyNotify.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"ReadyNotify")) (Val #()))
  {{ (ch : Loc), RET #ch; readyCh s ch }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
