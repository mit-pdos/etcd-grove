/-
`v3rpc.newBackendQuota` (`server/etcdserver/api/v3rpc/`).

Users: `quotaAlarmer.check`.

Proof sketch: `storage.NewBackendQuota(s.Logger(), s.Cfg.QuotaBackendBytes, s.Backend(), name)` (2e's spec; `s.Backend()` the current backend).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/newBackendQuota.lean`.

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

/-- `newBackendQuota(s, name)`: a quota. -/
def newBackendQuota.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ isServer s γ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newBackendQuota)) (Val #s)) (Val #name))
  {{ (q : GoInterface), RET #q; quotaOk q }}

end spec

end V3rpc
end EtcdGrove
end Perennial
