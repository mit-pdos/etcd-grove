/-
`typed.validateScalar`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validateScalar
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsBool_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsFloat_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsInt_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsNull_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsString_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__Unstructured_ptr
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

theorem typed.validateScalar.wp_proof
    (h_valueUnstructured_IsBool_ptr : value.valueUnstructured.IsBool_ptr.spec (GF := GF))
    (h_valueUnstructured_IsFloat_ptr : value.valueUnstructured.IsFloat_ptr.spec (GF := GF))
    (h_valueUnstructured_IsInt_ptr : value.valueUnstructured.IsInt_ptr.spec (GF := GF))
    (h_valueUnstructured_IsNull_ptr : value.valueUnstructured.IsNull_ptr.spec (GF := GF))
    (h_valueUnstructured_IsString_ptr : value.valueUnstructured.IsString_ptr.spec (GF := GF))
    (h_valueUnstructured_Unstructured_ptr : value.valueUnstructured.Unstructured_ptr.spec (GF := GF)) :
    typed.validateScalar.spec (GF := GF) := fun tp s v dq o pfx => by
  wp_start as ⟨#Htp, Hv, %Hok⟩
  cases o with
  | none =>
    iunfold isValO at Hv
    icases Hv with %Hv
    subst Hv
    wp_auto
    iapply HΦ
    isplitr
    · iunfold isValO; ipureintro; rfl
    · unfold noErrs ownErrs
      isplitr
      · iapply (ownSlice_nil (V := typed.ValidationError))
      · iapply ownSliceCap_nil
  | some x =>
    iunfold isValO at Hv
    ihave %Hc := isValF_concrete_law_holds v dq x $$ Hv
    obtain ⟨p, rfl⟩ := Hc
    wp_auto
    cases x <;> cases s <;> simp [scalarOk] at Hok
    all_goals repeat (first
      | (wp_apply h_valueUnstructured_IsNull_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩; try iexact Hv)
      | (wp_apply h_valueUnstructured_IsBool_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩; try iexact Hv)
      | (wp_apply h_valueUnstructured_IsString_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩; try iexact Hv)
      | (wp_apply h_valueUnstructured_IsInt_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩; try iexact Hv)
      | (wp_apply h_valueUnstructured_IsFloat_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩; try iexact Hv)
      | (simp only [UVal.isIntB, UVal.isStrB, UVal.isBoolB, UVal.isNullB, Scalar.goName]; wp_auto)
      | wp_auto)
    all_goals
      iapply HΦ
      isplitl [Hv]
      · iunfold isValO; iexact Hv
      · unfold noErrs ownErrs
        isplitr
        · iapply (ownSlice_nil (V := typed.ValidationError))
        · iapply ownSliceCap_nil

end proof

end smd
end EtcdGrove
end Perennial
