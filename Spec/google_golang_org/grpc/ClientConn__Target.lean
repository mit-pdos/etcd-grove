/-
`(*grpc.ClientConn).Target()` (grpc-go, assumed: `clientconn.go`).

Users: the client's retry interceptor (`retry_interceptor.go:60`, logged).

Why true: returns the target string given to `NewClient`, a field never written afterwards.

Changes: restored (round 1).

Margin: the string's value is not specified (only logged).
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

/-- `cc.Target()`: some string. -/
def ClientConn.Target.spec : Prop :=
  ∀ (cc : Loc) (A : GoString → IProp GF) (ui si : Option val) (R : MD → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ connAt cc A ui si R }}
    (App (Val (cc @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"Target")) (Val #()))
  {{ (t : GoString), RET #t; True }}

end spec

end Grpc
end EtcdGrove
end Perennial
