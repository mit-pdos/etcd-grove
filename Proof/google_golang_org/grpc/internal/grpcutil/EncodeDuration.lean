/-
The proof of `Spec/google_golang_org/grpc/internal/grpcutil/EncodeDuration.lean`: the units in turn,
over `div`'s spec and Perennial's `strconv.FormatInt.spec`.
-/
module

public import Spec.google_golang_org.grpc.internal.grpcutil.EncodeDuration
public import Spec.google_golang_org.grpc.internal.grpcutil.div
public import Perennial.Spec.strconv.FormatInt

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.internal.grpcutil.Assumptions]

theorem grpcutil.EncodeDuration.wp_proof
    (wp_div : grpcutil.div.spec (GF := GF) (hG := hG))
    (wp_FormatInt : _root_.Perennial.strconv.FormatInt.spec (GF := GF) (hG := hG)) :
    grpcutil.EncodeDuration.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start as #Hpkg
  ihave #Hsc : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  unfold grpcHdr.encodeDurationOf grpcHdr.encDurUnit
  wp_auto
  wp_if_destruct
  · rw [ite_eq_left (by word)]
    iapply HΦ; itrivial
  rw [ite_eq_right (by word)]
  wp_apply (wp_div t (W64 1) (by decide))
  wp_if_destruct
  · wp_apply (wp_FormatInt _ (W64 10) (by decide) (by decide))
    rw [ite_eq_left (by unfold grpcHdr.maxTimeoutValue; word)]
    iapply HΦ; itrivial
  rw [ite_eq_right (by unfold grpcHdr.maxTimeoutValue; word)]
  wp_apply (wp_div t (W64 1000) (by decide))
  wp_if_destruct
  · wp_apply (wp_FormatInt _ (W64 10) (by decide) (by decide))
    rw [ite_eq_left (by unfold grpcHdr.maxTimeoutValue; word)]
    iapply HΦ; itrivial
  rw [ite_eq_right (by unfold grpcHdr.maxTimeoutValue; word)]
  wp_apply (wp_div t (W64 1000000) (by decide))
  wp_if_destruct
  · wp_apply (wp_FormatInt _ (W64 10) (by decide) (by decide))
    rw [ite_eq_left (by unfold grpcHdr.maxTimeoutValue; word)]
    iapply HΦ; itrivial
  rw [ite_eq_right (by unfold grpcHdr.maxTimeoutValue; word)]
  wp_apply (wp_div t (W64 1000000000) (by decide))
  wp_if_destruct
  · wp_apply (wp_FormatInt _ (W64 10) (by decide) (by decide))
    rw [ite_eq_left (by unfold grpcHdr.maxTimeoutValue; word)]
    iapply HΦ; itrivial
  rw [ite_eq_right (by unfold grpcHdr.maxTimeoutValue; word)]
  wp_apply (wp_div t (W64 60000000000) (by decide))
  wp_if_destruct
  · wp_apply (wp_FormatInt _ (W64 10) (by decide) (by decide))
    rw [ite_eq_left (by unfold grpcHdr.maxTimeoutValue; word)]
    iapply HΦ; itrivial
  rw [ite_eq_right (by unfold grpcHdr.maxTimeoutValue; word)]
  wp_apply (wp_div t (W64 3600000000000) (by decide))
  wp_apply (wp_FormatInt _ (W64 10) (by decide) (by decide))
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
