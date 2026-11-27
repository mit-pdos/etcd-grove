/-
`(*grpc.Server).Serve(lis)` (item 4, the server start; per-type stage B, B1b, to phase 7 S2's interface,
2026-11-24: its body the trusted model `TrustedCode/google_golang_org/grpc.lean`, `Server.Serve.impl`,
proved over its leaves; since S2's interface a trust-boundary axiom over the right to serve a service
table, `grpcServeTok gs lis a Svc`, until S2 proves it over the model).
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

/-- `gs.Serve(lis)`, with the right to serve `gs` on `lis` at `a` for `Svc`, returns an error if it
returns; every call it accepts runs on a goroutine of its own, as `Svc` says. -/
abbrev grpc.Server.Serve.spec : Prop :=
  ∀ (gs : Loc) (lis : GoInterface) (a : GoString) (Svc : GrpcSvc GF),
  {{ grpcServeTok (GF := GF) gs lis a Svc }}
    (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"Serve")) (Val #lis))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
