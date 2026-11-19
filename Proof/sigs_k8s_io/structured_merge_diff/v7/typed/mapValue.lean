/-
`typed.mapValue`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).

Callees without a spec file here (other packages', the standard library's, or the
walker's own interface calls through a bundle): `fmt.Errorf`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mapValue
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsMapUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsMap_ptr
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

theorem typed.mapValue.wp_proof
    (h_valueUnstructured_AsMapUsing_ptr : value.valueUnstructured.AsMapUsing_ptr.spec (GF := GF))
    (h_valueUnstructured_IsMap_ptr : value.valueUnstructured.IsMap_ptr.spec (GF := GF))
    (h_valueUnstructured_IsNull_ptr : value.valueUnstructured.IsNull_ptr.spec (GF := GF)) :
    typed.mapValue.spec (GF := GF) := fun al v dq o => by
  wp_start as ⟨Hv, %Ho⟩
  obtain ⟨x, rfl⟩ : ∃ x, o = some x := by
    rcases Ho with h | h
    · exact ⟨_, h⟩
    · cases o <;> simp [mapOfO] at h ⊢
  iunfold isValO at Hv
  ihave %Hc := isValF_concrete_law_holds v dq x $$ Hv
  obtain ⟨p, rfl⟩ := Hc
  wp_auto
  rcases Ho with h | Hx
  · cases h
    wp_apply h_valueUnstructured_IsNull_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩
    · iexact Hv
    simp only [UVal.isNullB]
    wp_auto
    iapply HΦ
    isplitl [Hv]
    · iunfold isValO; iexact Hv
    isplitr
    · unfold isMapO mapOfO; ipureintro; rfl
    · ipureintro; simp
  · obtain ⟨kvs, rfl⟩ : ∃ kvs, x = .map kvs := by
      cases x <;> simp [mapOfO] at Hx ⊢
    wp_apply h_valueUnstructured_IsNull_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩
    · iexact Hv
    simp only [UVal.isNullB]
    wp_auto
    wp_apply h_valueUnstructured_IsMap_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩
    · iexact Hv
    simp only [UVal.isMapB]
    wp_auto
    wp_apply h_valueUnstructured_AsMapUsing_ptr p dq kvs al $$ [Hv] as %mv ⟨Hv, Hm⟩
    · iexact Hv
    iapply HΦ
    isplitl [Hv]
    · iunfold isValO; iexact Hv
    isplitl [Hm]
    · unfold isMapO mapOfO; iexact Hm
    · ipureintro; simp [mapOfO]

end proof

end smd
end EtcdGrove
end Perennial
