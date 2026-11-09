/-
`grpc.WithKeepaliveParams` (grpc-go, assumed).

Users: the client's `dialSetupOpts` (`client.go:231-237`, 1c), Kubernetes' factory.

Why true: keepalive pings close a dead transport; calls then fail with grpc's own errors, which every call's spec allows. No service config, no interceptor.

Changes: restored (round 1; `specs-ref/Spec/google_golang_org/grpc/WithKeepaliveParams.lean`): a neutral option.

Margin: none.
-/
module

public import Spec.google_golang_org.grpc.Api
public import GeneratedProof.google_golang_org.grpc.keepalive

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

/-- `grpc.WithKeepaliveParams(...)`: an option changing nothing the specs model. -/
def WithKeepaliveParams.spec : Prop :=
  ∀ (kp : google_golang_org.grpc.keepalive.ClientParameters),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.WithKeepaliveParams)) (Val #kp))
  {{ (v : GoInterface), RET #v; dialOptAt v id }}

end spec

end Grpc
end EtcdGrove
end Perennial
