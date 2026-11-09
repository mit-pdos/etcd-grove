/-
`grpc.WithChainStreamInterceptor` (grpc-go, assumed: `dialoptions.go`).

Users: Kubernetes' etcd client (`k8s.io/apiserver/pkg/storage/storagebackend/factory/etcd3.go:309-339`,
its `Config.DialOptions`, through the client's `dialOptsOk_neutral`, 1c); snippet `ReqKubeDialOpts`.

Why true: as `WithChainUnaryInterceptor`, for streams (`chainStreamClientInterceptors`); a pass-through stream interceptor (`cliSicPass`) opens the stream once and forwards each of its methods.

Changes: new (verify-round, A6-completeness F2 / A2-completeness F2: Kubernetes' dial options had
no spec, so its client could not be built).

Margin: pass-through interceptors only.
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

/-- `grpc.WithChainStreamInterceptor(is...)` of pass-through interceptors: a dial option that changes nothing the specs model. -/
def WithChainStreamInterceptor.spec : Prop :=
  ∀ (sl : GoSlice) (is : List GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ sl ↦*□ is ∗ [∗list] i ∈ is, cliSicPass #i }}
    (App (Val (@! google_golang_org.grpc.WithChainStreamInterceptor)) (Val #sl))
  {{ (v : GoInterface), RET #v; dialOptAt v (fun cfg => cfg) }}

end spec

end Grpc
end EtcdGrove
end Perennial
