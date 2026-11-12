/-
## `(*EtcdServer).StoppingNotify()` (`server.go:1383`)

**Users.** v3rpc's stream interceptor (`interceptor.go:326`, 2a), the watch server (2b).

**Proof sketch.** The field `start` set (`isServer`).

**Changes**: from `specs-ref`'s `EtcdServer__StoppingNotify.lean`.

**Margin.** None.
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

/-- **`StoppingNotify()`**: the server's stopping channel. -/
def EtcdServer.StoppingNotify.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"StoppingNotify")) (Val #()))
  {{ (ch : Loc), RET #ch; stoppingCh ch }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
