/-
`v3rpc.newHealthNotifier` (`server/etcdserver/api/v3rpc/`).

Users: `v3rpc.Server`.

Proof sketch: the server's logger and feature gate; `healthNotifier.startServe.spec`; a `nil` health server panics (excluded).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/newHealthNotifier.lean`.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto EtcdServer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `newHealthNotifier(hs, s)`: a notifier, the health server set to `SERVING`. -/
def newHealthNotifier.spec : Prop :=
  ∀ (hs s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ healthAt hs ∗ isServer s γ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newHealthNotifier)) (Val #hs)) (Val #s))
  {{ (n : GoInterface), RET #n; notifierAt n }}

end spec

end V3rpc
end EtcdGrove
end Perennial
