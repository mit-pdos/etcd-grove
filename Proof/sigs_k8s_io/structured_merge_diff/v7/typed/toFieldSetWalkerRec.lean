/-
`typed.toFieldSetWalkerRec`: the cluster's Löb induction.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__toFieldSetBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__visitMapItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalkerRec

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

/-- Löb induction over the members' bodies (with `typed.toFieldSetWalkerRec.specI`'s members read back as their
specs). -/
theorem typed.toFieldSetWalkerRec.wp_proof
    (h_toFieldSetWalker_doList_body : typed.toFieldSetWalker.doList.specBody (GF := GF))
    (h_toFieldSetWalker_doMap_body : typed.toFieldSetWalker.doMap.specBody (GF := GF))
    (h_toFieldSetWalker_toFieldSet_body : typed.toFieldSetWalker.toFieldSet.specBody (GF := GF))
    (h_toFieldSetWalker_visitListItems_body : typed.toFieldSetWalker.visitListItems.specBody (GF := GF))
    (h_toFieldSetWalker_visitMapItems_body : typed.toFieldSetWalker.visitMapItems.specBody (GF := GF)) :
    typed.toFieldSetWalkerRec.spec (GF := GF) := by
  have H : ⊢ typed.toFieldSetWalkerRec.specI (GF := GF) := by
    iloeb as IH
    ihave H0 := h_toFieldSetWalker_doList_body $$ IH
    ihave H1 := h_toFieldSetWalker_doMap_body $$ IH
    ihave H2 := h_toFieldSetWalker_toFieldSet_body $$ IH
    ihave H3 := h_toFieldSetWalker_visitListItems_body $$ IH
    ihave H4 := h_toFieldSetWalker_visitMapItems_body $$ IH
    unfold typed.toFieldSetWalkerRec.specI
    isplit
    · iexact H0
    isplit
    · iexact H1
    isplit
    · iexact H2
    isplit
    · iexact H3
    iexact H4
  unfold typed.toFieldSetWalkerRec.specI typed.toFieldSetWalker.doList.specI typed.toFieldSetWalker.doMap.specI typed.toFieldSetWalker.toFieldSet.specI typed.toFieldSetWalker.visitListItems.specI typed.toFieldSetWalker.visitMapItems.specI at H
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · repeat iintro %_
    iintro HP HΦ
    ihave ⟨HH, -, -, -, -⟩ := H
    iapply HH $$ HP HΦ
  · repeat iintro %_
    iintro HP HΦ
    ihave ⟨-, HH, -, -, -⟩ := H
    iapply HH $$ HP HΦ
  · repeat iintro %_
    iintro HP HΦ
    ihave ⟨-, -, HH, -, -⟩ := H
    iapply HH $$ HP HΦ
  · repeat iintro %_
    iintro HP HΦ
    ihave ⟨-, -, -, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · repeat iintro %_
    iintro HP HΦ
    ihave ⟨-, -, -, -, HH⟩ := H
    iapply HH $$ HP HΦ

end proof

end smd
end EtcdGrove
end Perennial
