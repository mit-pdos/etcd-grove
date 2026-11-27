/-
Proof of `Spec/google_golang_org/grpc/Server__RegisterService.lean` over the model's body (W1,
2026-11-26; until then a trust-boundary axiom, `notes/axiom-review/phase7-w1.md` §3): the model's
`RegisterService` is `s.register(sd, ss)` (no `HandlerType` check, `server.go:750-753`; the
spec's `grpcImplements` premise is what the real check would pass).
-/
module

public import Spec.google_golang_org.grpc.Server__RegisterService
public import Spec.google_golang_org.grpc.Server__register

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.Assumptions]

theorem grpc.Server.RegisterService.wp_proof
    (wp_register : grpc.Server.register.spec (GF := GF) (hG := hG)) :
    grpc.Server.RegisterService.spec (GF := GF) (hG := hG) := by
  intro gs sd ss ics sics svcs regs sregs sn ht mds sds
  wp_start as Hpre
  wp_auto
  wp_apply (wp_register gs sd ss ics sics svcs regs sregs sn ht mds sds) $$ Hpre as H
  iapply HΦ
  iexact H

end proof

end EtcdGrove
end Perennial
