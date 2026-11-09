/-
`grpc.WithChainUnaryInterceptor` (grpc-go, assumed: `dialoptions.go`).

Users: Kubernetes' etcd client (`k8s.io/apiserver/pkg/storage/storagebackend/factory/etcd3.go:309-339`,
its `Config.DialOptions`, through the client's `dialOptsOk_neutral`, 1c); snippet `examples/specreq/grpc/dialopts.go` `ReqKubeDialOpts`.

Why true: the option appends its interceptors to `dopts.chainUnaryInts`; at dial, grpc chains them after `dopts.unaryInt` (`clientconn.go`, `chainUnaryClientInterceptors`). Each one passing the call through (`cliIcPass`: calls the next exactly once with its own arguments and returns its result), the chain behaves, for every call, as the rest of it: the configuration as the specs model it is unchanged.

Changes: new (verify-round, A6-completeness F2 / A2-completeness F2: Kubernetes' dial options had
no spec, so its client could not be built).

Margin: stated for pass-through interceptors only (grpc-prometheus's, otel's); an interceptor that retries or answers itself is out of scope.
-/
module

public import Spec.google_golang_org.grpc.Api

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

/-- `grpc.WithChainUnaryInterceptor(is...)` of pass-through interceptors: a dial option that changes nothing the specs model. -/
def WithChainUnaryInterceptor.spec : Prop :=
  ∀ (sl : GoSlice) (is : List GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ sl ↦*□ is ∗ [∗list] i ∈ is, cliIcPass #i }}
    (App (Val (@! google_golang_org.grpc.WithChainUnaryInterceptor)) (Val #sl))
  {{ (v : GoInterface), RET #v; dialOptAt v (fun cfg => cfg) }}

end spec

end Grpc
end EtcdGrove
end Perennial
