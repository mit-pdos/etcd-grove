/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__Bookmark.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__Bookmark
public import Spec.k8s_io.client_go.tools.cache.parseRVForMetricsWithTruncation

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

theorem threadSafeMap.Bookmark.wp_proof
    (wp_parse : parseRVForMetricsWithTruncation.spec (GF := GF) (hG := hG)) :
    threadSafeMap.Bookmark.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam rv
  iintro %Φ ⟨#Hpkg, #Hc⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isTS at Hc
  icases Hc with ⟨%mp, %g, #Hidx, #Him, #Hmp, #Hg, #Hgok, #Hguard⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ rv_ptr ↦ rv ∗
      ∃ (rvInt : w64) (parseErr : GoInterface), rvInt_ptr ↦ rvInt ∗ parseErr_ptr ↦ parseErr)))
    $$ [rv rvInt parseErr]
  · wp_if_destruct
    · (try wp_auto)
      iframe
    · (try wp_auto)
      wp_apply wp_parse as %n %err _
      (try wp_auto)
      iframe
      try (ipureintro; rfl)
  iintro %v ⟨%hv, rv, %rvInt, %parseErr, rvInt, parseErr⟩
  subst hv
  (try wp_auto)
  wp_apply (lc := 2) sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hwl, HP⟩
  iunfold tsP at HP
  icases HP with ⟨%σ, %ph, Hst, Hgp, Hph, #Hpers, %Hok⟩
  iunfold tsPhys at Hph
  icases Hph with ⟨Hitems, Hil, Hrvf, Hind, Hix, Hfv⟩
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝)))
    $$ [- HAU Hst Hgp Hwl Hitems Hil Hind Hix Hfv Hrvf defer]
  · cases parseErr with
    | ok e =>
      (try wp_auto)
      ipureintro; rfl
    | nil =>
      (try wp_auto)
      cases g with
      | nil => iunfold gaugeOk at Hgok; icases Hgok with ⟨⟩
      | ok gi =>
        iunfold gaugeOk at Hgok
        (try wp_auto)
        wp_apply Hgok
        (try wp_auto)
        ipureintro; rfl
  iintro %v %hv
  subst hv
  imod storeSt_update γ σ (fun σ => σ.bookmark rv) _ $$ [$Hst $HAU] with ⟨Hst, HK⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hst Hgp Hitems Hil Hind Hix Hfv Hrvf]
  · inext
    iunfold tsP
    iexists σ.bookmark rv, ph
    iframe
    isplitl
    · iunfold tsPhys; iframe
    have hpe : tsPers OK Fam (σ.bookmark rv) ph = tsPers OK Fam σ ph := rfl
    rw [hpe]
    iframe #
    ipureintro; exact Hok
  (try wp_auto)
  iapply HK; itrivial

end proof

end cache
end EtcdGrove
end Perennial
