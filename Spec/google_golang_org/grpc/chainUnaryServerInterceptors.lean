/-
`grpc.chainUnaryServerInterceptors(s)` (`server.go`, the model's body; W1, 2026-11-26): what
`NewServer` stores as the server's unary interceptor, from the chain its options built.
The vocabulary: `Proof/google_golang_org/grpc/InvGrpcServer.lean` (`srvChainIs`).
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

/-- On a server whose options hold the read-only chain `ics` and no single `unaryInt` (no option of
a kind sets one): `unaryInt` becomes the chain's interceptor (`srvChainIs`: nil, the one, or the
chaining closure). -/
abbrev grpc.chainUnaryServerInterceptors.spec : Prop :=
  ∀ (gs : Loc) (so : google_golang_org.grpc.serverOptions) (ics : List GoFunc),
  {{ (structFieldRef google_golang_org.grpc.Server go!"opts" gs ↦ so ∗ so.chainUnaryInts' ↦*□ ics ∗
      ⌜so.unaryInt' = zero_val GoFunc⌝ : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.chainUnaryServerInterceptors)) (Val #gs))
  {{ (v : GoFunc), RET #();
      structFieldRef google_golang_org.grpc.Server go!"opts" gs ↦ { so with unaryInt' := v } ∗
      srvChainIs chainUnaryClosure v so.chainUnaryInts' ics }}

end spec

end EtcdGrove
end Perennial
