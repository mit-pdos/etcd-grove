/-
`typed.listValue`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).

Callees without a spec file here (other packages', the standard library's, or the
walker's own interface calls through a bundle): `fmt.Errorf`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listValue
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsListUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsList_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsNull_ptr
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
variable [package_sem : typed.Assumptions]

theorem typed.listValue.wp_proof
    (h_valueUnstructured_AsListUsing_ptr : value.valueUnstructured.AsListUsing_ptr.spec (GF := GF))
    (h_valueUnstructured_IsList_ptr : value.valueUnstructured.IsList_ptr.spec (GF := GF))
    (h_valueUnstructured_IsNull_ptr : value.valueUnstructured.IsNull_ptr.spec (GF := GF)) :
    typed.listValue.spec (GF := GF) := fun al v dq x => by
  wp_start as ⟨Hv, %Hx⟩
  ihave %Hc := isValF_concrete_law_holds v dq x $$ Hv
  obtain ⟨p, rfl⟩ := Hc
  wp_auto
  rcases Hx with rfl | Hx
  · wp_apply h_valueUnstructured_IsNull_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩
    · iexact Hv
    simp only [UVal.isNullB]
    wp_auto
    iapply HΦ
    iframe Hv
    isplitr
    · unfold isListO listOfO; ipureintro; rfl
    · ipureintro; simp
  · obtain ⟨vs, rfl⟩ : ∃ vs, x = .list vs := by
      cases x <;> simp [listOfO] at Hx ⊢
    wp_apply h_valueUnstructured_IsNull_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩
    · iexact Hv
    simp only [UVal.isNullB]
    wp_auto
    wp_apply h_valueUnstructured_IsList_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩
    · iexact Hv
    simp only [UVal.isListB]
    wp_auto
    wp_apply h_valueUnstructured_AsListUsing_ptr p dq vs al $$ [Hv] as %lv ⟨Hv, Hl⟩
    · iexact Hv
    iapply HΦ
    iframe Hv
    isplitl [Hl]
    · unfold isListO listOfO; iexact Hl
    · ipureintro; simp [listOfO]

end proof

end smd
end EtcdGrove
end Perennial
