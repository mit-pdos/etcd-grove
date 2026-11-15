/-
`grpc.WithStatsHandler` (grpc-go, assumed: `dialoptions.go`).

Users: Kubernetes' etcd client (`k8s.io/apiserver/pkg/storage/storagebackend/factory/etcd3.go:309-339`,
its `Config.DialOptions`, through the client's `dialOptsOk_neutral`, 1c); snippet `ReqKubeDialOpts`.

Why true: the option appends `h` to `dopts.copts.StatsHandlers`; the transport calls its methods on each connection and RPC event, observing only (`statsOk`: they return, and change no state the specs model).

Changes: new (verify-round, A6-completeness F2 / A2-completeness F2: Kubernetes' dial options had
no spec, so its client could not be built).

Margin: stated for an observing handler (otelgrpc's `NewClientHandler`, whose `statsOk` is its owner's: requested of client-core).
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `grpc.WithStatsHandler(h)` of an observing handler: a dial option that changes nothing the specs model. -/
def WithStatsHandler.spec : Prop :=
  ∀ (h : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ statsOk h }}
    (App (Val (@! google_golang_org.grpc.WithStatsHandler)) (Val #h))
  {{ (v : GoInterface), RET #v; dialOptAt v (fun cfg => cfg) }}

end spec

end Grpc
end EtcdGrove
end Perennial
