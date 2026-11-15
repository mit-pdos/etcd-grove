/-
`grpc.WithTransportCredentials` (grpc-go, assumed: `dialoptions.go`).

Users: the client's `dialSetupOpts` (`client.go:242,244`, 1c).

Why true: transport security changes nothing the specs model (the peer's identity, which TLS client-certificate authentication uses, is 2e's `tlsPrincipal` slot, seen by the server's handler through its context).

Changes: from `specs-ref/.../grpc/WithTransportCredentials.lean`.

Margin: none.
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

/-- `grpc.WithTransportCredentials(...)`: a dial option acting as shown. -/
def WithTransportCredentials.spec : Prop :=
  ∀ (tc : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ True }}
    (App (Val (@! google_golang_org.grpc.WithTransportCredentials)) (Val #tc))
  {{ (v : GoInterface), RET #v; dialOptAt v (id) }}

end spec

end Grpc
end EtcdGrove
end Perennial
