/-
`grpc.WithContextDialer` (grpc-go, assumed: `dialoptions.go`).

Users: Kubernetes' etcd client (`k8s.io/apiserver/pkg/storage/storagebackend/factory/etcd3.go:309-339`,
its `Config.DialOptions`, through the client's `dialOptsOk_neutral`, 1c); snippet `ReqKubeDialOpts` (Kubernetes passes it when an egress dialer is configured).

Why true: the option sets `dopts.copts.Dialer`; the transport dials each address the resolver reports with it. A dialer that dials the address it is given (`ctxDialerOk`) reaches the same members: the addresses (`DialCfg.A`), interceptors and credentials are unchanged.

Changes: new (verify-round, A6-completeness F2 / A2-completeness F2: Kubernetes' dial options had
no spec, so its client could not be built).

Margin: a dialer that redirects (a proxy to another cluster) is out of scope.
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

/-- `grpc.WithContextDialer(f)` of a faithful dialer: a dial option that changes nothing the specs model. -/
def WithContextDialer.spec : Prop :=
  ∀ (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ ctxDialerOk f }}
    (App (Val (@! google_golang_org.grpc.WithContextDialer)) (Val f))
  {{ (v : GoInterface), RET #v; dialOptAt v (fun cfg => cfg) }}

end spec

end Grpc
end EtcdGrove
end Perennial
