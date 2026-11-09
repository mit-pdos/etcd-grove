/-
`grpc.Creds` (grpc-go, assumed: `server.go`).

Users: `v3rpc.Server` (`grpc.go:59`).

Why true: transport security changes nothing the specs model.

Changes: new.

Margin: none.
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

/-- `grpc.Creds(...)`: a server option acting as shown. -/
def Creds.spec : Prop :=
  ∀ (tc : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ True }}
    (App (Val (@! google_golang_org.grpc.Creds)) (Val #tc))
  {{ (v : GoInterface), RET #v; srvOptAt v (id) }}

end spec

end Grpc
end EtcdGrove
end Perennial
