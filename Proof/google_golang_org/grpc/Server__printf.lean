/-
Proof of `Spec/google_golang_org/grpc/Server__printf.lean` over the model's body (W1, 2026-11-26):
`events` is nil, so nothing is logged.
-/
module

public import Spec.google_golang_org.grpc.Server__printf

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

theorem grpc.Server.printf.wp_proof : grpc.Server.printf.spec (GF := GF) (hG := hG) := by
  intro gs fmt a
  wp_start as Hev
  wp_auto
  iapply HΦ
  iexact Hev

end proof

end EtcdGrove
end Perennial
