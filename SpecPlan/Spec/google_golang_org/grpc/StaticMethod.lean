/-
`grpc.StaticMethod()` (grpc-go, assumed: `rpc_util.go`).

Users: every generated stub (`rpc_grpc.pb.go:71,81`, 3h's `kVClient__*`, `watchClient__Watch`).

Why true: a `StaticMethodCallOption{}` value; grpc reads it for its metrics' labels only.

Changes: restored (round 1).

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

/-- `grpc.StaticMethod()`: a call option. -/
def StaticMethod.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.StaticMethod)) (Val #()))
  {{ (v : GoInterface), RET #v; callOptOk v }}

end spec

end Grpc
end EtcdGrove
end Perennial
