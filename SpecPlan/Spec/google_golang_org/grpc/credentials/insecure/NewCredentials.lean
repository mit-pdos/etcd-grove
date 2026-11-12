/-
`insecure.NewCredentials()` (grpc-go, assumed: `credentials/insecure/insecure.go`).

Users: the client's `dialSetupOpts` without TLS (`client.go:244`, 1c).

Why true: a fresh `insecureTC{}` value.

Changes: restored (round 1).

Margin: none.
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api
public import GeneratedProof.google_golang_org.grpc.credentials.insecure
public import SpecPlan.Spec.PkgInit.google_golang_org.grpc.credentials.insecure

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

/-- `insecure.NewCredentials()`: some transport credentials (any, for `WithTransportCredentials`). -/
def insecure.NewCredentials.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.credentials.insecure }}
    (App (Val (@! google_golang_org.grpc.credentials.insecure.NewCredentials)) (Val #()))
  {{ (tc : GoInterface), RET #tc; True }}

end spec

end Grpc
end EtcdGrove
end Perennial
