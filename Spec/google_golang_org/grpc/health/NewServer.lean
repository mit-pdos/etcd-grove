/-
`health.NewServer()` (grpc's health service; item 4, the server start; proved over the real code since
2026-11-26, grpc-health).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.google_golang_org.grpc.health
public import Proof.google_golang_org.grpc.InvGrpcHealth

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

/-- `health.NewServer()` returns a non-nil `*health.Server` (`grpcHealthSrv`). -/
abbrev health.NewServer.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.health.NewServer)) (Val #()))
  {{ (hs : Loc), RET #hs; ⌜hs ≠ null⌝ ∗ grpcHealthSrv hs }}

end spec

end EtcdGrove
end Perennial
