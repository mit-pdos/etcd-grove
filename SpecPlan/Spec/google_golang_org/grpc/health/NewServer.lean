/-
`health.NewServer()` (grpc-go, assumed: `health/server.go`).

Users: `v3rpc.Server` (`grpc.go:96`).

Why true: a fresh server with the overall service `SERVING`, its status map behind a mutex.

Changes: from `specs-ref/Spec/google_golang_org/grpc/health/NewServer.lean`.

Margin: none.
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api
public import GeneratedProof.google_golang_org.grpc.health
public import SpecPlan.Spec.PkgInit.google_golang_org.grpc.health

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

/-- `health.NewServer()`: a health server. -/
def health.NewServer.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.health }}
    (App (Val (@! google_golang_org.grpc.health.NewServer)) (Val #()))
  {{ (hs : Loc), RET #hs; healthAt hs }}

end spec

end Grpc
end EtcdGrove
end Perennial
