/-
`typed.compareWalkerRec`: the cluster's Löb induction .
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__compareBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__compareListItemBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__visitMapItemBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__visitMapItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalkerRec

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

/-- Löb induction over the members' bodies (with `typed.compareWalkerRec.specI`'s members read back as their
specs). -/
theorem typed.compareWalkerRec.wp_proof
    (h_compareWalker_compare_body : typed.compareWalker.compare.specBody (GF := GF))
    (h_compareWalker_compareListItem_body : typed.compareWalker.compareListItem.specBody (GF := GF))
    (h_compareWalker_doList_body : typed.compareWalker.doList.specBody (GF := GF))
    (h_compareWalker_doMap_body : typed.compareWalker.doMap.specBody (GF := GF))
    (h_compareWalker_visitListItems_body : typed.compareWalker.visitListItems.specBody (GF := GF))
    (h_compareWalker_visitMapItem_body : typed.compareWalker.visitMapItem.specBody (GF := GF))
    (h_compareWalker_visitMapItems_body : typed.compareWalker.visitMapItems.specBody (GF := GF)) :
    typed.compareWalkerRec.spec (GF := GF) := by
  have H : ⊢ typed.compareWalkerRec.specI (GF := GF) := by
    iloeb as IH
    ihave H0 := h_compareWalker_compare_body $$ IH
    ihave H1 := h_compareWalker_compareListItem_body $$ IH
    ihave H2 := h_compareWalker_doList_body $$ IH
    ihave H3 := h_compareWalker_doMap_body $$ IH
    ihave H4 := h_compareWalker_visitListItems_body $$ IH
    ihave H5 := h_compareWalker_visitMapItem_body $$ IH
    ihave H6 := h_compareWalker_visitMapItems_body $$ IH
    unfold typed.compareWalkerRec.specI
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
  unfold typed.compareWalkerRec.specI typed.compareWalker.compare.specI typed.compareWalker.compareListItem.specI typed.compareWalker.doList.specI typed.compareWalker.doMap.specI typed.compareWalker.visitListItems.specI typed.compareWalker.visitMapItem.specI typed.compareWalker.visitMapItems.specI at H
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    iintro %Φ HP HΦ
    ihave ⟨HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17
    iintro %Φ HP HΦ
    ihave ⟨-, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
    iintro %Φ HP HΦ
    ihave ⟨-, -, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
    iintro %Φ HP HΦ
    ihave ⟨-, -, -, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    iintro %Φ HP HΦ
    ihave ⟨-, -, -, -, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18
    iintro %Φ HP HΦ
    ihave ⟨-, -, -, -, -, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
    iintro %Φ HP HΦ
    ihave ⟨-, -, -, -, -, -, HH⟩ := H
    iapply HH $$ HP HΦ

end proof

end smd
end EtcdGrove
end Perennial
