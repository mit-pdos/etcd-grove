/-
Proof of `Spec/google_golang_org/grpc/Server__wrapUnaryHandler.lean` over the model's body (W1,
2026-11-26): the function literal over the cells `s` and `md`, which is `wrapUnaryClosure` by
definition (its literal is read from the same generated body).
-/
module

public import Spec.google_golang_org.grpc.Server__wrapUnaryHandler

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

theorem grpc.Server.wrapUnaryHandler.wp_proof :
    grpc.Server.wrapUnaryHandler.spec (GF := GF) (hG := hG) := by
  intro gs mdl
  wp_start
  iapply wp_fupd
  wp_auto
  ipersist s
  ipersist md
  imodintro
  ihave H := HΦ $$ %s_ptr %md_ptr [$s $md]
  iExactEq H
  rfl

end proof

end EtcdGrove
end Perennial
