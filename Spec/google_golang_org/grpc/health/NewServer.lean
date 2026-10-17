/-
`health.NewServer()` (grpc's health service, names only; item 4, the server start).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.google_golang_org.grpc.health

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
