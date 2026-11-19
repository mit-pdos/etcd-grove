/-
`value.freelistAllocator.allocValueUnstructured`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__allocValueUnstructured
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsFreelist

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

theorem value.freelistAllocator.allocValueUnstructured.wp_proof :
    value.freelistAllocator.allocValueUnstructured.spec (GF := GF) := fun p => by
  wp_start as Ha
  icases isAlloc_fl_elim $$ Ha with ⟨%fa, #Hp, H1, H2⟩
  wp_auto
  ihave Hp2 := Hp
  ispatial Hp2
  iStructNamed Hp2
  wp_load
  wp_auto
  wp_apply wp_freelist_allocate $$ [H1] as %q ⟨H1, Hq⟩
  · iexact H1
  iapply HΦ
  iframe
  iapply isAlloc_fl_intro
  iframe
  iexact Hp

end proof

end smd
end EtcdGrove
end Perennial
