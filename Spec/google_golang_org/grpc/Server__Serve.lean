/-
`(*grpc.Server).Serve(lis)` (item 4, the server start; since per-type stage B, B1b, its body is the
trusted model `TrustedCode/google_golang_org/grpc.lean`, `Server.Serve.impl`, proved over its leaves).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcRun

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

/-- `gs.Serve(lis)`, with the right to serve `gs` on `lis` as the server `γ` (`grpc.start'`'s),
returns an error if it returns. Every call it accepts runs on a goroutine of its own, the handler
meeting the registration its client deposited. -/
abbrev grpc.Server.Serve.spec : Prop :=
  ∀ (gs : Loc) (lis : GoInterface) (γ : GName),
  {{ grpcServeTok (GF := GF) gs lis γ }}
    (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"Serve")) (Val #lis))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
