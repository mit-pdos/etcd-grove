/-
Proof of `apierrors.SuggestsClientDelay` (`Spec/k8s_io/apimachinery/pkg/api/errors/SuggestsClientDelay.lean`)
over its body (prove-k8s2, 2026-11-20; until then a trust-boundary axiom).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.SuggestsClientDelay
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

theorem SuggestsClientDelay.wp_proof
    (wp_AsNoMatch : errors.AsNoMatch.spec (GF := GF) (hG := hG)) :
    SuggestsClientDelay.spec (GF := GF) (hG := hG) := by
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
    ihave #Hd0 := Hd
    iunfold statusDetailsAt at Hd0
    icases Hd0 with (%hd | ⟨%d, #Hdp, #Hcs⟩)
    · simp only [hd.1, _root_.decide_true, Bool.not_true]
      wp_auto
      iapply HΦ
      iintro !> %w #Hw
      ihave %hw := Hag $$ Hw
      subst hw
      ileft
      ipureintro
      exact ⟨hd.1, rfl, rfl⟩
    · icases typedPointsto_not_null _ _ _ $$ Hdp with %hnn
      rw [decide_eq_false hnn]
      wp_auto
      wp_method_call
      wp_auto
      ihave Hdp' := Hdp
      iStructNamed Hdp'
      by_cases hr : st.Reason' = go!"ServerTimeout"
      · rw [decide_eq_true hr]
        wp_auto
        wp_method_call
        wp_auto
        iapply HΦ
        iintro !> %w #Hw
        ihave %hw := Hag $$ Hw
        subst hw
        iright
        iexists d
        isplitr
        · ipureintro; exact hnn
        isplitr
        · iexact Hdp
        ipureintro
        unfold delayV
        simp only [hr, true_or, ↓reduceIte]
      · rw [decide_eq_false hr]
        wp_auto
        wp_method_call
        wp_auto
        have h0 : sint.Z (W32 0) = 0 := by word
        by_cases hp : sint.Z (W32 0) < sint.Z d.RetryAfterSeconds'
        · rw [decide_eq_true hp]
          wp_auto
          wp_method_call
          wp_auto
          iapply HΦ
          iintro !> %w #Hw
          ihave %hw := Hag $$ Hw
          subst hw
          iright
          iexists d
          isplitr
          · ipureintro; exact hnn
          isplitr
          · iexact Hdp
          ipureintro
          unfold delayV
          simp only [show 0 < sint.Z d.RetryAfterSeconds' by rw [h0] at hp; exact hp, or_true, ↓reduceIte]
        · rw [decide_eq_false hp]
          wp_auto
          iapply HΦ
          iintro !> %w #Hw
          ihave %hw := Hag $$ Hw
          subst hw
          iright
          iexists d
          isplitr
          · ipureintro; exact hnn
          isplitr
          · iexact Hdp
          ipureintro
          unfold delayV
          simp only [hr, show ¬ 0 < sint.Z d.RetryAfterSeconds' by rw [h0] at hp; exact hp, or_self,
            ↓reduceIte]
  · ihave #Hag := apiErrAt_plain_agree err $$ Hpl
    ihave %hsh := apiErrAt_plain_shape err $$ Hpl
    rcases hsh with rfl | ⟨ii, rfl, hts⟩
    all_goals
      wp_auto
      try simp only [hts, Bool.false_eq_true, ↓reduceIte]
      try wp_auto
      wp_apply (wp_As_plain wp_AsNoMatch _ _ _) $$ [t]
      · iframe
        try iexact Hpl
      iintro t
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
