/-
`(*grpc.ClientConn).Close()` (grpc-go, assumed: `clientconn.go`).

Users: the client's `Close` (`client.go`, 1c).

Why true: `Close` tears down the transports; calls in flight and later fail with `Canceled`
("grpc: the client connection is closing"), an error grpc makes itself, which every call's spec
already allows; it returns `nil` or `ErrClientConnClosing` (a second close).

Changes: new.

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

/-- `cc.Close()`: returns; the connection stays `connAt` (its calls fail with grpc's own errors). -/
def ClientConn.Close.spec : Prop :=
  ∀ (cc : Loc) (A : GoString → IProp GF) (ui si : Option val) (R : MD → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ connAt cc A ui si R }}
    (App (Val (cc @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

end spec

end Grpc
end EtcdGrove
end Perennial
