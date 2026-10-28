/-
Proof of `Spec/k8s_io/client_go/tools/pager/ListPager__list.lean`, over `meta.ListAccessor`'s and
`apierrors.IsResourceExpired`'s named hypotheses (boundary, pending approval). Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.pager.ListPager__list
public import Spec.k8s_io.apimachinery.pkg.api.meta.ListAccessor
public import Spec.k8s_io.apimachinery.pkg.api.errors.IsResourceExpired
public import Perennial.Proof.context.BackgroundCtx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace pager

open Iris Iris.BI Iris.ProofMode apimodel cache k8s_io.client_go.tools.pager

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.pager.Assumptions]

theorem ListPager.list.wp_proof
    (wp_ListAccessor : apimeta.ListAccessor.spec (GF := GF) (hG := hG))
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
    icases Hres with (⟨%herr, Hae⟩ | ⟨%he, %q, %os, %rv, %hobj, Hl, HS⟩)
    · obtain ⟨hne, hobj⟩ := herr
      cases err with
      | nil => exact absurd rfl hne
      | ok ei =>
        (try wp_auto)
        wp_apply (wp_IsResourceExpired _) $$ [$Herrs] as %bexp -
        (try wp_auto)
        sorry
    · subst he hobj
      (try wp_auto)
      wp_apply (wp_ListAccessor res q os rv) $$ [$Hmeta $Hl] as %m %merr ⟨%hmerr, Hl, #Hacc⟩
      subst hmerr
      (try wp_auto)
      sorry

end proof

end pager
end EtcdGrove
end Perennial
