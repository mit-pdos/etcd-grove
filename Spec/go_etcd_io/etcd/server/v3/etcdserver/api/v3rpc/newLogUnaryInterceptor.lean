/-
`v3rpc.newLogUnaryInterceptor` (`server/etcdserver/api/v3rpc/`).

Users: `v3rpc.Server` (the unary chain).

Proof sketch: the handler once, then (deferred) `logUnaryRequestStats` with the reply (its `unaryOut` gives the reply's message at a fraction and depth, which the log reads and gives back).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/newLogUnaryInterceptor.lean`: as `icEtcdOk` (was `srvInterceptorOk` with a per-interceptor predicate).

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

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

/-- `newLogUnaryInterceptor(s)`: an interceptor preserving etcd's contracts. -/
def newLogUnaryInterceptor.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ isServer s γ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newLogUnaryInterceptor)) (Val #s))
  {{ (i : GoFunc), RET #i; icEtcdOk i γ }}

end spec

end V3rpc
end EtcdGrove
end Perennial
