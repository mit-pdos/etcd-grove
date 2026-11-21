/-
Proof of `apierrors.reasonAndCodeForError` (`Spec/k8s_io/apimachinery/pkg/api/errors/reasonAndCodeForError.lean`)
over its body (prove-k8s2, 2026-11-20).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.reasonAndCodeForError
public import Proof.k8s_io.apimachinery.pkg.api.errors.Checks

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

theorem reasonAndCodeForError.wp_proof
    (wp_AsNoMatch : errors.AsNoMatch.spec (GF := GF) (hG := hG)) :
    reasonAndCodeForError.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as #Hok
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Hc := apiErrOk_cases err $$ Hok
  icases Hc with (⟨%st, %cs, #Hst⟩ | #Hpl)
  · ihave #Hag := apiErrAt_status_agree err st cs $$ Hst
    iunfold apiErrAt at Hst
    icases Hst with ⟨%l, %hl, #Hl, #Hd⟩
    subst hl
    wp_auto
    simp only [statusErrorPtr_apiStatus, ↓reduceIte]
    wp_auto
    ihave Hl' := Hl
    iStructNamed Hl'
    iStructNamed ErrStatus
    wp_method_call
    wp_auto
    wp_method_call
    wp_auto
    iapply HΦ
    iintro !> %w #Hw
    ihave %hw := Hag $$ Hw
    subst hw
    ipureintro
    exact ⟨rfl, rfl⟩
  · ihave #Hag := apiErrAt_plain_agree err $$ Hpl
    ihave %hsh := apiErrAt_plain_shape err $$ Hpl
    rcases hsh with rfl | ⟨ii, rfl, hts⟩
    all_goals
      wp_auto
      try simp only [hts, Bool.false_eq_true, ↓reduceIte]
      try wp_auto
      wp_apply (wp_As_plain wp_AsNoMatch _ _ _) $$ [status]
      · iframe
        try iexact Hpl
      iintro status
      wp_auto
      iapply HΦ
      iintro !> %w #Hw
      ihave %hw := Hag $$ Hw
      subst hw
      ipureintro
      exact ⟨rfl, rfl⟩

end proof

end apierrors
end EtcdGrove
end Perennial
