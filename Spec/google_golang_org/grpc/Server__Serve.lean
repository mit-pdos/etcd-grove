/-
`(*grpc.Server).Serve(lis)` (names only; item 4, the server start).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `gs.Serve(lis)` with the right to serve `gs` on `lis` (`grpc.start`'s) returns an error if it
returns. -/
abbrev grpc.Server.Serve.spec : Prop :=
  ∀ (gs : Loc) (lis : GoInterface),
  {{ grpcServeTok (GF := GF) gs lis }}
    (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"Serve")) (Val #lis))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
