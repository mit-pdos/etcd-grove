/-
`grpc.CustomCodec` (grpc-go, assumed: `server.go`).

Users: `v3rpc.Server` (`grpc.go:57`, this batch: `&codec{}`).

Why true: the server marshals replies and unmarshals requests with the codec; a codec that round-trips contents keeps the transport's content guarantee (`codecOk`).

Changes: from `specs-ref/.../grpc/CustomCodec.lean`.

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

/-- `grpc.CustomCodec(...)`: a server option acting as shown. -/
def CustomCodec.spec : Prop :=
  ∀ (cd : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ codecOk cd }}
    (App (Val (@! google_golang_org.grpc.CustomCodec)) (Val #cd))
  {{ (v : GoInterface), RET #v; srvOptAt v (id) }}

end spec

end Grpc
end EtcdGrove
end Perennial
