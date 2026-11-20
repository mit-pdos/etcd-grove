/-
`typed.validatingObjectWalkerRec`: the cluster's Löb induction.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__validateBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__visitMapItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalkerRec

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

/-- Löb induction over the members' bodies (with `typed.validatingObjectWalkerRec.specI`'s members read back as their
specs). -/
theorem typed.validatingObjectWalkerRec.wp_proof
    (h_validatingObjectWalker_doList_body : typed.validatingObjectWalker.doList.specBody (GF := GF))
    (h_validatingObjectWalker_doMap_body : typed.validatingObjectWalker.doMap.specBody (GF := GF))
    (h_validatingObjectWalker_validate_body : typed.validatingObjectWalker.validate.specBody (GF := GF))
    (h_validatingObjectWalker_visitListItems_body : typed.validatingObjectWalker.visitListItems.specBody (GF := GF))
    (h_validatingObjectWalker_visitMapItems_body : typed.validatingObjectWalker.visitMapItems.specBody (GF := GF)) :
    typed.validatingObjectWalkerRec.spec (GF := GF) := by
  have H : ⊢ typed.validatingObjectWalkerRec.specI (GF := GF) := by
    iloeb as IH
    ihave H0 := h_validatingObjectWalker_doList_body $$ IH
    ihave H1 := h_validatingObjectWalker_doMap_body $$ IH
    ihave H2 := h_validatingObjectWalker_validate_body $$ IH
    ihave H3 := h_validatingObjectWalker_visitListItems_body $$ IH
    ihave H4 := h_validatingObjectWalker_visitMapItems_body $$ IH
    unfold typed.validatingObjectWalkerRec.specI
    isplit
    · iexact H0
    isplit
    · iexact H1
    isplit
    · iexact H2
    isplit
    · iexact H3
    iexact H4
  unfold typed.validatingObjectWalkerRec.specI typed.validatingObjectWalker.doList.specI typed.validatingObjectWalker.doMap.specI typed.validatingObjectWalker.validate.specI typed.validatingObjectWalker.visitListItems.specI typed.validatingObjectWalker.visitMapItems.specI at H
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
