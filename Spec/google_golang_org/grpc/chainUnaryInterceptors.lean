/-
`grpc.chainUnaryInterceptors(interceptors)` (`server.go`, the model's body; W1, 2026-11-26): the
chaining interceptor `NewServer` stores for two or more unary interceptors.
The vocabulary: `Proof/google_golang_org/grpc/InvGrpcServer.lean` (`chainUnaryClosure`).
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

/-- Returns the function literal over a fresh read-only cell holding the slice
(`chainUnaryClosure`, the exact value). -/
abbrev grpc.chainUnaryInterceptors.spec : Prop :=
  ∀ (sl : GoSlice),
  {{ (True : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.chainUnaryInterceptors)) (Val #sl))
  {{ (il : Loc), RET #(chainUnaryClosure il); il ↦□ sl }}

end spec

end EtcdGrove
end Perennial
