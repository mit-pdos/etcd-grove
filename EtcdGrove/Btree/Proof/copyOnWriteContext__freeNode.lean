import EtcdGrove.Btree.Spec.copyOnWriteContext__freeNode
import EtcdGrove.Btree.Spec.items__truncate
import EtcdGrove.Btree.Spec.FreeListG__freeNode
import EtcdGrove.Btree.NodeLemmas

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI Iris.ProofMode github_com.google.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]

theorem copyOnWriteContext.freeNode.wp_proof
    (wp_items_truncate : items.truncate.spec (GF := GF) (hG := hG))
    (wp_FreeListG_freeNode : FreeListG.freeNode.spec (GF := GF) (hG := hG)) :
    copyOnWriteContext.freeNode.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o c f less n
  wp_start as ⟨#Hcow, Hn⟩
  unfold isCow
  icases Hcow with ⟨#Hc, #Hfl, #Hless⟩
  iStructNamed Hc
  icases Hn with (⟨%is, %ps, Hn⟩ | ⟨%t, #Hn⟩)
  · unfold nodeShallow nodeFields
    icases Hn with ⟨%isl, %csl, ⟨%Hnn, Hi, Hch, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩
    wp_auto
    wp_apply (wp_items_truncate (V := V) (T := T) _ isl _ (W64 0) (by decide) (by simp))
      $$ [$Hi $Hisl $Hicap] as %isl' ⟨Hi, Hisl, Hicap⟩
    wp_apply (wp_items_truncate (V := Loc) (T := go.GoType.PointerType (node.ty T)) _ csl _
      (W64 0) (by decide) (by simp)) $$ [$Hch $Hcsl $Hccap] as %csl' ⟨Hch, Hcsl, Hccap⟩
    simp only [List.take_zero]
    wp_apply (wp_FreeListG_freeNode (V := V) (T := T) f n) $$ [$Hfl Hi Hch Hw Hisl Hicap Hcsl Hccap]
      as %out _
    · unfold freeNode nodeFields
      iexists isl', csl', null
      iframe
      ipureintro; exact Hnn
    wp_if_destruct <;> wp_end
  · cases t with
    | node is cs =>
      rw [frozen_node]
      icases Hn with ⟨%isl, %csl, %cow, %ps, Hnf, %Hne, -⟩
      unfold nodeFields
      icases Hnf with ⟨%Hnn, #Hi, #Hch, #Hw⟩
      wp_auto
      wp_if_destruct
      · exact absurd Hif Hne
      · wp_end

end proof

end Btree
end EtcdGrove
end Perennial
