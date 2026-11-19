/-
`value.valueUnstructured.IsList_ptr`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsList_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsList
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs

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

theorem value.valueUnstructured.IsList_ptr.wp_proof
    (h_valueUnstructured_IsList : value.valueUnstructured.IsList.spec (GF := GF)) :
    value.valueUnstructured.IsList_ptr.spec (GF := GF) := fun p dq x => by
  wp_start as Hv
  icases isValF_elim $$ Hv with ⟨%i, Hp, #Hi⟩
  wp_auto
  wp_apply h_valueUnstructured_IsList ⟨i⟩ x as %r %Hr
  · iexact Hi
  iapply HΦ
  isplitl [Hp]
  · iapply isValF_intro _ _ i; iframe; iexact Hi
  · ipureintro; exact Hr

end proof

end smd
end EtcdGrove
end Perennial
