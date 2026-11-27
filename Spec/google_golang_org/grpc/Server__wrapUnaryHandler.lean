/-
`(*grpc.Server).wrapUnaryHandler(md)` (`server.go`, the model's body; W1, 2026-11-26): the stream
handler `register` stores for a unary method.
The vocabulary: `Proof/google_golang_org/grpc/InvGrpcServer.lean` (`wrapUnaryClosure`).
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

/-- Returns the function literal over fresh read-only cells holding `gs` and `md`
(`wrapUnaryClosure`, the exact value). -/
abbrev grpc.Server.wrapUnaryHandler.spec : Prop :=
  ∀ (gs md : Loc),
  {{ (True : IProp GF) }}
    (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"wrapUnaryHandler"))
      (Val #md))
  {{ (cs cm : Loc), RET #(wrapUnaryClosure cs cm); cs ↦□ gs ∗ cm ↦□ md }}

end spec

end EtcdGrove
end Perennial
