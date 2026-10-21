/-
`grpc.KeepaliveEnforcementPolicy(kep)` (grpc's `server.go`, names only; 2026-10-21,
`notes/keepalive-plan.md` KA1, `notes/decisions.md` D28). Lean-first.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.google_golang_org.grpc.keepalive

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

/-- `grpc.KeepaliveEnforcementPolicy(kep)` returns a neutral option. -/
abbrev grpc.KeepaliveEnforcementPolicy.spec : Prop :=
  ∀ (kep : google_golang_org.grpc.keepalive.EnforcementPolicy),
  {{ (True : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.KeepaliveEnforcementPolicy)) (Val #kep))
  {{ (v : GoInterface), RET #v; ⌜grpcSrvOpt v .neutral⌝ }}

end spec

end EtcdGrove
end Perennial
