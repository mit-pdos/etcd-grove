/-
`istats.NewCombinedHandler(handlers...)` (grpc's `internal/stats/stats.go`, with its body; W1,
2026-11-26): what `grpc.NewServer` stores as the server's stats handler.
The vocabulary: `Proof/google_golang_org/grpc/InvGrpcServer.lean` (`srvStatsIs`).
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

/-- Of the handlers `hs` at the read-only slice `sl`: `nil` for none, the one for one, else a
`*combinedHandler` holding `sl` (read-only), as `srvStatsIs` states it. -/
abbrev istats.NewCombinedHandler.spec : Prop :=
  ∀ (sl : GoSlice) (hs : List GoInterface),
  {{ (sl ↦*□ hs : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.internal.stats.NewCombinedHandler)) (Val #sl))
  {{ (v : GoInterface), RET #v;
      ⌜hs = [] ∧ v = GoInterface.nil⌝ ∨ (∃ h, ⌜hs = [h] ∧ v = h⌝) ∨
        ∃ l : Loc, ⌜2 ≤ hs.length ∧ v = interface.mkOk
            (go.GoType.PointerType google_golang_org.grpc.internal.stats.combinedHandler.ty) #l⌝ ∗
          l ↦□ google_golang_org.grpc.internal.stats.combinedHandler.mk sl }}

end spec

end EtcdGrove
end Perennial
