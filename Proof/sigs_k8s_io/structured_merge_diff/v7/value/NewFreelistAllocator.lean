/-
`value.NewFreelistAllocator`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewFreelistAllocator
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsFreelist
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects

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
variable [package_sem : value.Assumptions]

theorem value.NewFreelistAllocator.wp_proof :
    value.NewFreelistAllocator.spec (GF := GF) := by
  wp_start
  repeat (first | wp_auto | wp_func_lits)
  wp_alloc fa as Hfa
  ipersist Hfa
  wp_auto
  iapply HΦ
  iapply isAlloc_fl_intro
  isplitr
  · iexact Hfa
  isplitl [«$v0»]
  · iunfold freelistOwn
    iexists _
    iframe
    isplitr
    · iexists []
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      · simp only [valueSepL, List.foldr_nil]; itrivial
    · iintro !> %Φ _ HΦ
      rw [← recv_eq_func_mk]
      wp_call
      wp_auto
      iapply HΦ
      iunfold wrapperOwn
      iexists _
      iexact «$r0»
  · iunfold freelistOwn
    iexists _
    iframe
    isplitr
    · iexists []
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      · simp only [valueSepL, List.foldr_nil]; itrivial
    · iintro !> %Φ _ HΦ
      rw [← recv_eq_func_mk]
      wp_call
      wp_auto
      iapply HΦ
      iunfold rangeOwn
      iexists _
      isplitl [«$r0»]
      · iexact «$r0»
      · iunfold wrapperOwn
        iexists _
        iexact «$v0»

end proof

end smd
end EtcdGrove
end Perennial
