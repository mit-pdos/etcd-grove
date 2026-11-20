module

public import Spec.k8s_io.apiserver.pkg.storage.HasInitialEventsEndBookmarkAnnotation
public import Spec.k8s_io.apimachinery.pkg.api.meta.Accessor

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
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem storage.HasInitialEventsEndBookmarkAnnotation.wp_proof
    (wp_Accessor : apimeta.Accessor.spec (GF := GF) (hG := hG)) :
    storage.HasInitialEventsEndBookmarkAnnotation.spec (GF := GF) (hG := hG) := by
  intro ii P b hty
  wp_start as ⟨HP, HG⟩
  wp_auto
  wp_apply (wp_Accessor ii hty)
  wp_bind
  iapply HG $$ HP
  inext
  iintro %m HP Hm
  wp_auto
  icases Hm with (⟨%hm, %hb⟩ | ⟨%M, %dq, Hm, %hb⟩)
  · subst hm hb
    wp_auto
    iapply HΦ $$ HP
  · wp_apply (wp_map_lookup1 (K := GoString) (V := GoString) go.string go.string) $$ Hm as Hm
    have hgd : ((M !! go!"k8s.io/initial-events-end").getD (zero_val GoString) = go!"true") ↔
        (M !! go!"k8s.io/initial-events-end" = some go!"true") := by
      cases M !! go!"k8s.io/initial-events-end" <;> simp [zero_val]
    rw [show decide ((M !! go!"k8s.io/initial-events-end").getD (zero_val GoString) = go!"true") = b
      by rw [hb]; exact decide_eq_decide.2 hgd]
    iapply HΦ $$ HP

end proof

end EtcdGrove
end Perennial
