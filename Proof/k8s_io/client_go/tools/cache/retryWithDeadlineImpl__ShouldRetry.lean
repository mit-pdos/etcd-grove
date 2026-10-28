/-
Proof of `Spec/k8s_io/client_go/tools/cache/retryWithDeadlineImpl__ShouldRetry.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.retryWithDeadlineImpl__ShouldRetry
public import Spec.k8s_io.client_go.tools.cache.retryWithDeadlineImpl__reset
public import Spec.k8s_io.utils.clock.RealClock__Now
public import Perennial.Spec.time.Time__Sub

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem retryWithDeadlineImpl.ShouldRetry.wp_proof
    (wp_reset : retryWithDeadlineImpl.reset.spec (GF := GF) (hG := hG))
    (wp_Now : clock.RealClock.Now.spec (GF := GF) (hG := hG))
    (wp_Sub : time.Time.Sub.spec (GF := GF) (hG := hG)) :
    retryWithDeadlineImpl.ShouldRetry.spec (GF := GF) (hG := hG) := by
  intro l
  wp_start as Hr
  ihave #Hclk : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.clock $$ []
  · iPkgInit
  iunfold retryOwn at Hr
  icases Hr with ⟨%l', %v, %c, %hl, Hl, %hv⟩
  have hl' : l' = l := by
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at hl
    exact (intoVal_eq_iff.1 hl.2).symm
  subst hl'
  obtain ⟨hc, hrt⟩ := hv
  wp_auto
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    unfold retryOwn
    iexists l', v, c
    iframe
    ipureintro; exact ⟨rfl, hc, hrt⟩
  · rw [hc]
    (try wp_auto)
    wp_apply (wp_Now c) $$ [$Hclk] as %t -
    (try wp_auto)
    wp_apply (wp_Sub t v.firstErrorTime') as %d -
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ
      unfold retryOwn
      iexists l', v, c
      iframe
      ipureintro; exact ⟨rfl, hc, hrt⟩
    · (try wp_auto)
      wp_apply (wp_reset l' v) $$ [$Hl] as Hl
      (try wp_auto)
      iapply HΦ
      unfold retryOwn
      iexists l', retryReset v, c
      iframe
      ipureintro; exact ⟨rfl, hc, hrt⟩

end proof

end cache
end EtcdGrove
end Perennial
