/-
`value.freelistAllocator.Free`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
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

theorem value.freelistAllocator.Free.wp_proof :
    value.freelistAllocator.Free.spec (GF := GF) := fun p x => by
  wp_start as ⟨Ha, Hx⟩
  icases isAlloc_fl_elim $$ Ha with ⟨%fa, #Hp, H1, H2⟩
  ihave Hp2 := Hp
  ispatial Hp2
  iStructNamed Hp2
  cases x with
  | nil =>
    wp_auto
    iapply HΦ; iapply isAlloc_fl_intro; iframe; iexact Hp
  | ok i =>
    obtain ⟨ty, v⟩ := i
    iunfold freeable at Hx
    by_cases h1 : ty = go.GoType.PointerType value.valueUnstructured.ty
    · subst h1
      isimp at Hx
      icases Hx with ⟨%q, %rfl, Hw⟩
      iunfold wrapperOwn at Hw
      icases Hw with ⟨%i, Hw⟩
      wp_auto
      wp_apply wp_freelist_free $$ [H1 Hw] as H1
      · iframe; iunfold wrapperOwn; iexists _; iexact Hw
      iapply HΦ; iapply isAlloc_fl_intro; iframe; iexact Hp
    by_cases h2 : ty = go.GoType.PointerType value.listUnstructuredRange.ty
    · subst h2
      isimp [h1] at Hx
      icases Hx with ⟨%q, %rfl, Hw⟩
      iunfold rangeOwn at Hw
      icases Hw with ⟨%r, Hq, Hw⟩
      iunfold wrapperOwn at Hw
      icases Hw with ⟨%i, Hw⟩
      wp_auto
      wp_apply wp_freelist_free $$ [H2 Hq Hw] as H2
      · iframe; iunfold rangeOwn; iexists _; iframe; iunfold wrapperOwn; iexists _; iexact Hw
      iapply HΦ; iapply isAlloc_fl_intro; iframe; iexact Hp
    isimp [h1, h2] at Hx
    by_cases h3 : ty = go.GoType.PointerType value.valueReflect.ty ∨
        ty = go.GoType.PointerType value.mapReflect.ty ∨
        ty = go.GoType.PointerType value.structReflect.ty ∨
        ty = go.GoType.PointerType value.listReflect.ty ∨
        ty = go.GoType.PointerType value.listReflectRange.ty
    · isimp [h3] at Hx
      iexfalso; iexact Hx
    · isimp [h3] at Hx
      simp only [not_or] at h3
      obtain ⟨h3, h4, h5, h6, h7⟩ := h3
      repeat (first | wp_auto | simp only [h1, h2, h3, h4, h5, h6, h7, decide_false, ↓reduceIte])
      iapply HΦ; iapply isAlloc_fl_intro; iframe; iexact Hp

end proof

end smd
end EtcdGrove
end Perennial
