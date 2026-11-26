/-
Proof of `Spec/google_golang_org/grpc/chainUnaryInterceptors.lean` over the model's body (W1,
2026-11-26): the function literal over the cell `interceptors`, which is `chainUnaryClosure` by
definition (its literal is read from the same generated body).
-/
module

public import Spec.google_golang_org.grpc.chainUnaryInterceptors

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

theorem grpc.chainUnaryInterceptors.wp_proof :
    grpc.chainUnaryInterceptors.spec (GF := GF) (hG := hG) := by
  intro sl
  wp_start
  iapply wp_fupd
  wp_auto
  ipersist interceptors
  imodintro
  ihave H := HΦ $$ %interceptors_ptr interceptors
  iExactEq H
  rfl

end proof

end EtcdGrove
end Perennial
