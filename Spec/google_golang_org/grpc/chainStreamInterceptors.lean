/-
`grpc.chainStreamInterceptors(interceptors)` (`server.go`, the model's body; W1, 2026-11-26): the
chaining interceptor `NewServer` stores for two or more stream interceptors.
The vocabulary: `Proof/google_golang_org/grpc/InvGrpcServer.lean` (`chainStreamClosure`).
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
(`chainStreamClosure`, the exact value). -/
abbrev grpc.chainStreamInterceptors.spec : Prop :=
  ∀ (sl : GoSlice),
  {{ (True : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.chainStreamInterceptors)) (Val #sl))
  {{ (il : Loc), RET #(chainStreamClosure il); il ↦□ sl }}

end spec

end EtcdGrove
end Perennial
