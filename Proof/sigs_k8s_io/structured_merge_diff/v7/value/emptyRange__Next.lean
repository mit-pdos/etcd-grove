/-
`value.emptyRange.Next`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.emptyRange__Next
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
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

theorem value.emptyRange.Next.wp_proof :
    value.emptyRange.Next.spec (GF := GF) := fun q vs n => by
  wp_start as Hr
  iunfold ownRange at Hr
  icases Hr with (⟨%q', %h⟩ | ⟨%q', %sl, %w, %iw, %h, -⟩)
  · obtain ⟨hq, rfl, hn⟩ := h
    simp [intoVal_eq_iff] at hq
    subst hq
    wp_auto
    iapply HΦ
    isplitl
    · iunfold ownRange; ileft; iexists q; ipureintro; exact ⟨rfl, rfl, by omega⟩
    · ipureintro; simp; omega
  · exfalso; simp [emptyRange_ne_listUnstructuredRange] at h

end proof

end smd
end EtcdGrove
end Perennial
