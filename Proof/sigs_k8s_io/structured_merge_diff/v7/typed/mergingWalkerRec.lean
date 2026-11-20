/-
`typed.mergingWalkerRec`: the cluster's Löb induction .
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__mergeBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__mergeListItemBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__visitMapItemBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__visitMapItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalkerRec

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

/-- Löb induction over the members' bodies (with `typed.mergingWalkerRec.specI`'s members read back as their
specs). -/
theorem typed.mergingWalkerRec.wp_proof
    (h_mergingWalker_doList_body : typed.mergingWalker.doList.specBody (GF := GF))
    (h_mergingWalker_doMap_body : typed.mergingWalker.doMap.specBody (GF := GF))
    (h_mergingWalker_merge_body : typed.mergingWalker.merge.specBody (GF := GF))
    (h_mergingWalker_mergeListItem_body : typed.mergingWalker.mergeListItem.specBody (GF := GF))
    (h_mergingWalker_visitListItems_body : typed.mergingWalker.visitListItems.specBody (GF := GF))
    (h_mergingWalker_visitMapItem_body : typed.mergingWalker.visitMapItem.specBody (GF := GF))
    (h_mergingWalker_visitMapItems_body : typed.mergingWalker.visitMapItems.specBody (GF := GF)) :
    typed.mergingWalkerRec.spec (GF := GF) := by
  have H : ⊢ typed.mergingWalkerRec.specI (GF := GF) := by
    iloeb as IH
    ihave H0 := h_mergingWalker_doList_body $$ IH
    ihave H1 := h_mergingWalker_doMap_body $$ IH
    ihave H2 := h_mergingWalker_merge_body $$ IH
    ihave H3 := h_mergingWalker_mergeListItem_body $$ IH
    ihave H4 := h_mergingWalker_visitListItems_body $$ IH
    ihave H5 := h_mergingWalker_visitMapItem_body $$ IH
    ihave H6 := h_mergingWalker_visitMapItems_body $$ IH
    unfold typed.mergingWalkerRec.specI
    isplit
    · iexact H0
    isplit
    · iexact H1
    isplit
    · iexact H2
    isplit
    · iexact H3
    isplit
    · iexact H4
    isplit
    · iexact H5
    iexact H6
  unfold typed.mergingWalkerRec.specI typed.mergingWalker.doList.specI typed.mergingWalker.doMap.specI typed.mergingWalker.merge.specI typed.mergingWalker.mergeListItem.specI typed.mergingWalker.visitListItems.specI typed.mergingWalker.visitMapItem.specI typed.mergingWalker.visitMapItems.specI at H
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    iintro %Φ HP HΦ
    ihave ⟨HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    iintro %Φ HP HΦ
    ihave ⟨-, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
    iintro %Φ HP HΦ
    ihave ⟨-, -, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
    iintro %Φ HP HΦ
    ihave ⟨-, -, -, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    iintro %Φ HP HΦ
    ihave ⟨-, -, -, -, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18
    iintro %Φ HP HΦ
    ihave ⟨-, -, -, -, -, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    iintro %Φ HP HΦ
    ihave ⟨-, -, -, -, -, -, HH⟩ := H
    iapply HH $$ HP HΦ

end proof

end smd
end EtcdGrove
end Perennial
