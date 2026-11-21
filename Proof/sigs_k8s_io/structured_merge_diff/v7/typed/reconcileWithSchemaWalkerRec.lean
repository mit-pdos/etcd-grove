/-
`typed.reconcileWithSchemaWalkerRec`: the cluster's Löb induction .
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__reconcileBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__visitMapItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalkerRec

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option synthInstance.maxSize 1024

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

/-- Löb induction over the members' bodies (with `typed.reconcileWithSchemaWalkerRec.specI`'s members read back as their
specs). -/
theorem typed.reconcileWithSchemaWalkerRec.wp_proof
    (h_reconcileWithSchemaWalker_doList_body : typed.reconcileWithSchemaWalker.doList.specBody (GF := GF))
    (h_reconcileWithSchemaWalker_doMap_body : typed.reconcileWithSchemaWalker.doMap.specBody (GF := GF))
    (h_reconcileWithSchemaWalker_reconcile_body : typed.reconcileWithSchemaWalker.reconcile.specBody (GF := GF))
    (h_reconcileWithSchemaWalker_visitListItems_body : typed.reconcileWithSchemaWalker.visitListItems.specBody (GF := GF))
    (h_reconcileWithSchemaWalker_visitMapItems_body : typed.reconcileWithSchemaWalker.visitMapItems.specBody (GF := GF)) :
    typed.reconcileWithSchemaWalkerRec.spec (GF := GF) := by
  have H : ⊢ typed.reconcileWithSchemaWalkerRec.specI (GF := GF) := by
    iloeb as IH
    ihave H0 := h_reconcileWithSchemaWalker_doList_body $$ IH
    ihave H1 := h_reconcileWithSchemaWalker_doMap_body $$ IH
    ihave H2 := h_reconcileWithSchemaWalker_reconcile_body $$ IH
    ihave H3 := h_reconcileWithSchemaWalker_visitListItems_body $$ IH
    ihave H4 := h_reconcileWithSchemaWalker_visitMapItems_body $$ IH
    unfold typed.reconcileWithSchemaWalkerRec.specI
    isplit
    · iexact H0
    isplit
    · iexact H1
    isplit
    · iexact H2
    isplit
    · iexact H3
    iexact H4
  unfold typed.reconcileWithSchemaWalkerRec.specI typed.reconcileWithSchemaWalker.doList.specI typed.reconcileWithSchemaWalker.doMap.specI typed.reconcileWithSchemaWalker.reconcile.specI typed.reconcileWithSchemaWalker.visitListItems.specI typed.reconcileWithSchemaWalker.visitMapItems.specI at H
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    iintro %Φ HP HΦ
    ihave ⟨HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    iintro %Φ HP HΦ
    ihave ⟨-, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8
    iintro %Φ HP HΦ
    ihave ⟨-, -, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
    iintro %Φ HP HΦ
    ihave ⟨-, -, -, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
    iintro %Φ HP HΦ
    ihave ⟨-, -, -, -, HH⟩ := H
    iapply HH $$ HP HΦ

end proof

end smd
end EtcdGrove
end Perennial
