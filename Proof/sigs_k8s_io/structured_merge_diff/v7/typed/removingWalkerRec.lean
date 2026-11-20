/-
`typed.removingWalkerRec`: the cluster's Löb induction.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removeItemsWithSchemaBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalkerRec

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

/-- Löb induction over the members' bodies (with `typed.removingWalkerRec.specI`'s members read back as their
specs). -/
theorem typed.removingWalkerRec.wp_proof
    (h_removeItemsWithSchema_body : typed.removeItemsWithSchema.specBody (GF := GF))
    (h_removingWalker_doList_body : typed.removingWalker.doList.specBody (GF := GF))
    (h_removingWalker_doMap_body : typed.removingWalker.doMap.specBody (GF := GF)) :
    typed.removingWalkerRec.spec (GF := GF) := by
  have H : ⊢ typed.removingWalkerRec.specI (GF := GF) := by
    iloeb as IH
    ihave H0 := h_removeItemsWithSchema_body $$ IH
    ihave H1 := h_removingWalker_doList_body $$ IH
    ihave H2 := h_removingWalker_doMap_body $$ IH
    unfold typed.removingWalkerRec.specI
    isplit
    · iexact H0
    isplit
    · iexact H1
    iexact H2
  unfold typed.removingWalkerRec.specI typed.removeItemsWithSchema.specI typed.removingWalker.doList.specI typed.removingWalker.doMap.specI at H
  refine ⟨?_, ?_, ?_⟩
  · repeat iintro %_
    iintro HP HΦ
    ihave ⟨HH, -, -⟩ := H
    iapply HH $$ HP HΦ
  · repeat iintro %_
    iintro HP HΦ
    ihave ⟨-, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · repeat iintro %_
    iintro HP HΦ
    ihave ⟨-, -, HH⟩ := H
    iapply HH $$ HP HΦ

end proof

end smd
end EtcdGrove
end Perennial
