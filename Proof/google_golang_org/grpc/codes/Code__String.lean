/-
`codes.Code.String()`: proved over grpc's translated `codes` (`code_string.go`) and Perennial's
`strconv.FormatInt`. See `Spec/google_golang_org/grpc/codes/Code__String.lean`.
-/
module

public import Spec.google_golang_org.grpc.codes.Code__String
public import Perennial.Spec.strconv.FormatInt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.codes.Assumptions]

/-- The switch of `code_string.go`: one case per code, `Code(<decimal>)` otherwise. -/
theorem codes.Code.String.wp_proof
    (wp_FormatInt : _root_.Perennial.strconv.FormatInt.spec (GF := GF) (hG := hG)) :
    codes.Code.String.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as #Hpkg
  ihave #Hs : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · rw [show codes.codeStr (W32 0) = go!"OK" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 1) = go!"Canceled" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 2) = go!"Unknown" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 3) = go!"InvalidArgument" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 4) = go!"DeadlineExceeded" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 5) = go!"NotFound" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 6) = go!"AlreadyExists" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 7) = go!"PermissionDenied" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 8) = go!"ResourceExhausted" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 9) = go!"FailedPrecondition" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 10) = go!"Aborted" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 11) = go!"OutOfRange" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 12) = go!"Unimplemented" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 13) = go!"Internal" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 14) = go!"Unavailable" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 15) = go!"DataLoss" by decide]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [show codes.codeStr (W32 16) = go!"Unauthenticated" by decide]
    iapply HΦ; itrivial
  wp_apply (wp_FormatInt (W64 (uint.Z c)) (W64 10) (by decide) (by decide))
  have hs : codes.codeStr c =
      go!"Code(" ++ internal.strconv.fmtInt (W64 (uint.Z c)) (W64 10) ++ go!")" := by
    unfold codes.codeStr; simp_all
  rw [hs]
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
