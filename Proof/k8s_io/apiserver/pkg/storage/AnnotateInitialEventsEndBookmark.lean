/-
Lean-first (no Rocq counterpart). The proof of `storage.AnnotateInitialEventsEndBookmark`:
`meta.Accessor` gives the object back as a `metav1.Object` and `nil`; `GetAnnotations` (the caller's
contract) answers a map, replaced by a fresh empty one if `nil`; the insert of the key; then
`SetAnnotations` (the caller's contract) and `nil`.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.AnnotateInitialEventsEndBookmark
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

theorem storage.AnnotateInitialEventsEndBookmark.wp_proof
    (wp_Accessor : apimeta.Accessor.spec (GF := GF) (hG := hG)) :
    storage.AnnotateInitialEventsEndBookmark.spec (GF := GF) (hG := hG) := by
  intro ii P R Q hty
  wp_start as ⟨HP, HG, HS⟩
  wp_auto
  wp_apply (wp_Accessor ii hty)
  wp_bind
  iapply HG $$ HP
  inext
  iintro %m HR Hm
  wp_auto
  icases Hm with (%hm | ⟨%M, Hm⟩)
  · subst hm
    rw [decide_eq_true rfl]
    wp_auto
    wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %mref Hm
    wp_apply (wp_mapInsert (K := GoString) (V := GoString) go.string) $$ Hm as Hm
    wp_bind
    iapply HS $$ HR Hm
    · ipureintro; simp
    inext
    iintro HQ
    wp_auto
    iapply HΦ
    iframe
    ipureintro; rfl
  · ihave %hnn := ownMap_not_nil $$ Hm
    rw [decide_eq_false hnn]
    wp_auto
    wp_apply (wp_mapInsert (K := GoString) (V := GoString) go.string) $$ Hm as Hm
    wp_bind
    iapply HS $$ HR Hm
    · ipureintro; simp
    inext
    iintro HQ
    wp_auto
    iapply HΦ
    iframe
    ipureintro; rfl

end proof

end EtcdGrove
end Perennial
