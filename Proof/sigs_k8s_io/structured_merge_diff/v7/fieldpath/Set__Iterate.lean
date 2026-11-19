/-
`fieldpath.Set.Iterate`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Iterate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__iteratePrefix
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsIter
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep

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
variable [package_sem : fieldpath.Assumptions]

theorem fieldpath.Set.Iterate.wp_proof
    (h_Set_iteratePrefix : fieldpath.Set.iteratePrefix.spec (GF := GF)) :
    fieldpath.Set.Iterate.spec (GF := GF) := fun p S f I => by
  wp_start as ⟨#Hs, HI, #Hf⟩
  wp_auto
  wp_apply (wp_slice_literal (V := fieldpath.PathElement) (l := []))
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hcap⟩
  (try wp_auto)
  wp_apply (h_Set_iteratePrefix p S _ [] [] f S I []) $$ [Hsl Hcap HI] as ⟨-, -, %ds, %hds, HI⟩
  · iframe
    isplit; · iexact Hs
    isplit; · unfold isPEs; rw [fpL.isPEL_nil_eq]; itrivial
    isplit
    · ipureintro; intro q hq; simpa using hq
    · iexact Hf
  iapply HΦ
  iexists ds
  isplitr
  · ipureintro
    refine ⟨hds.1, hds.2.trans (FSet.ext' fun x => ?_)⟩
    rw [PathSet_mem_prepend_law_holds]; simp
  · simp only [List.nil_append]; iexact HI

end proof

end smd
end EtcdGrove
end Perennial
