/-
Proof of `Spec/k8s_io/client_go/tools/pager/ListPager__list.lean`, over `meta.ListAccessor`'s spec, the typed
lists' pending hypothesis `cache.typedListMeta` and `apierrors.IsResourceExpired`'s named hypothesis. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.pager.ListPager__list
public import Spec.k8s_io.apimachinery.pkg.api.meta.ListAccessor
public import Spec.k8s_io.client_go.tools.cache.typedListMeta
public import Spec.k8s_io.apimachinery.pkg.api.errors.IsResourceExpired
public import Perennial.Proof.context.BackgroundCtx

@[expose] public section

set_option linter.unusedSectionVars false

set_option hygiene false in
/-- Return the page function's error, with no list. -/
local macro "ret_err" : tactic => `(tactic| (
    wp_for_post
    (try wp_auto)
    iapply HΦ
    iframe
    unfold pageRes
    ileft
    iframe
    iframe HeOk
    ipureintro; exact ⟨hne, Or.inl rfl⟩))

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace pager

open Iris Iris.BI Iris.ProofMode apimodel cache k8s_io.client_go.tools.pager

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.pager.Assumptions]

theorem ListPager.list.wp_proof
    (wp_ListAccessor : apimeta.ListAccessor.spec (GF := GF) (hG := hG))
    (wp_typedListMeta : cache.typedListMeta.spec (GF := GF) (hG := hG))
    (wp_IsResourceExpired : apierrors.IsResourceExpired.spec (GF := GF) (hG := hG)) :
    ListPager.list.spec (GF := GF) (hG := hG) := by
  intro p pg opts alloc res S hts hsie
  wp_start as ⟨Hp, #Hpf⟩
  ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors $$ []
  · iPkgInit
  ihave #Hmeta : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» $$ []
  · iPkgInit
  iunfold pfnOk at Hpf
  wp_auto
  wp_if_destruct <;> (try wp_auto) <;> wp_for <;>
    wp_apply context.wp_background_Done
  all_goals
    wp_apply_core chan.wp_select_nonblocking_nil
    isplit
    · iapply BigAndL.bigAndL_cons.2
      isplit
      · iright
        iapply (chan.nilClausePre_recv Unit _ _ rfl)
      · iapply BigAndL.bigAndL_nil.2; itrivial
    wp_auto
    wp_apply Hpf $$ [] as %obj %err Hlo Hres
    · iapply (lo_own_intro _ none (DFrac.own 1))
      · exact hsie
      simp only [ownPtrD]
      ipureintro; exact hts
    (try wp_auto)
    iunfold pageRes at Hres
    icases Hres with (⟨%herr, Hae, #HeOk⟩ | ⟨%he, %q, %os, %rv, %hobj, Hl, HS⟩)
    · obtain ⟨hne, hobj⟩ := herr
      cases err with
      | nil => exact absurd rfl hne
      | ok ei =>
        (try wp_auto)
        wp_apply (wp_IsResourceExpired _) $$ [$Herrs] as %bexp -
        · iright; iexact HeOk
        (try wp_auto)
        cases bexp
        · (try wp_auto)
          ret_err
        · (try wp_auto)
          cases hfl : pg.FullListIfExpired'
          · (try wp_auto)
            ret_err
          · (try wp_auto)
            wp_if_destruct
            · ret_err
            · (try wp_auto)
              wp_apply Hpf $$ [] as %obj2 %err2 Hlo2 Hres2
              · iapply (lo_own_intro _ none (DFrac.own 1))
                · exact hsie
                simp only [ownPtrD]
                ipureintro; exact hts
              (try wp_auto)
              wp_for_post
              (try wp_auto)
              iapply HΦ
              iframe
    · subst he hobj
      (try wp_auto)
      obtain ⟨hlts, -, wp_cont⟩ := wp_typedListMeta res
      wp_apply (wp_ListAccessor ⟨go.GoType.PointerType (resListTy res), #q⟩ hlts) $$ [$Hmeta]
      (try wp_auto)
      wp_apply (wp_cont q os rv) $$ [$Hl] as Hl
      (try wp_auto)
      wp_func_call
      wp_call
      (try wp_auto)
      wp_for_post
      (try wp_auto)
      iapply HΦ
      iframe
      unfold pageRes
      iright
      isplitr
      · ipureintro; rfl
      iexists q, os, rv
      iframe
      ipureintro; rfl

end proof

end pager
end EtcdGrove
end Perennial
