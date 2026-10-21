/-
`grpc.WithKeepaliveParams(kp)` (grpc's `dialoptions.go`, names only; 2026-10-21,
`notes/keepalive-plan.md` KA1, `notes/decisions.md` D28). Lean-first.
-/
module

public import Proof.google_golang_org.grpc.InvDial
public import GeneratedProof.google_golang_org.grpc.keepalive

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `grpc.WithKeepaliveParams(kp)`, any parameters: a dial option setting the keepalive
parameters (`.keepalive`). -/
abbrev grpc.WithKeepaliveParams.spec : Prop :=
  ∀ (kp : google_golang_org.grpc.keepalive.ClientParameters),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.WithKeepaliveParams)) (Val #kp))
  {{ (o : GoInterface), RET #o; ⌜grpcDialOptIs o .keepalive⌝ }}

end spec

end EtcdGrove
end Perennial
