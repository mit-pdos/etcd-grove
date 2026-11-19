/-
`typed.deduceAtom`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.deduceAtom
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsBool_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsFloat_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsInt_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsList_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsMap_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsString_ptr
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs
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

theorem typed.deduceAtom.wp_proof
    (h_valueUnstructured_IsBool_ptr : value.valueUnstructured.IsBool_ptr.spec (GF := GF))
    (h_valueUnstructured_IsFloat_ptr : value.valueUnstructured.IsFloat_ptr.spec (GF := GF))
    (h_valueUnstructured_IsInt_ptr : value.valueUnstructured.IsInt_ptr.spec (GF := GF))
    (h_valueUnstructured_IsList_ptr : value.valueUnstructured.IsList_ptr.spec (GF := GF))
    (h_valueUnstructured_IsMap_ptr : value.valueUnstructured.IsMap_ptr.spec (GF := GF))
    (h_valueUnstructured_IsString_ptr : value.valueUnstructured.IsString_ptr.spec (GF := GF)) :
    typed.deduceAtom.spec (GF := GF) := fun a A v dq o => by
  wp_start as ⟨#Ha, Hv⟩
  -- the atom is of one kind: the other two pointers are nil
  ihave %hA : ⌜(∃ s, a = ⟨s, null, null⟩) ∨ (∃ l, a = ⟨null, l, null⟩) ∨ (∃ m, a = ⟨null, null, m⟩)⌝ $$ [] 
  · cases A with
    | scalar s =>
      icases (isAtomOpt_scalar_law_holds a s).1 $$ Ha with ⟨-, %Hn⟩
      ipureintro; left; exact ⟨a.Scalar', by cases a; simp_all⟩
    | list e rel ks =>
      icases (isAtomOpt_list_law_holds a e rel ks).1 $$ Ha with ⟨%Hn, -⟩
      ipureintro; right; left; exact ⟨a.List', by cases a; simp_all⟩
    | map fs e rel =>
      icases (isAtomOpt_map_law_holds a fs e rel).1 $$ Ha with ⟨%Hn, -⟩
      ipureintro; right; right; exact ⟨a.Map', by cases a; simp_all⟩
  iclear Ha
  obtain ⟨s, rfl⟩ | ⟨l, rfl⟩ | ⟨m, rfl⟩ := hA
  all_goals
    cases o with
    | none =>
      iunfold isValO at Hv
      icases Hv with %Hv
      subst Hv
      wp_auto
      iapply HΦ
      iunfold isValO; ipureintro; rfl
    | some x =>
      iunfold isValO at Hv
      ihave %Hc := isValF_concrete_law_holds v dq x $$ Hv
      obtain ⟨p, rfl⟩ := Hc
      wp_auto
      cases x
      all_goals repeat (first
        | (wp_apply h_valueUnstructured_IsBool_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩; try iexact Hv)
        | (wp_apply h_valueUnstructured_IsString_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩; try iexact Hv)
        | (wp_apply h_valueUnstructured_IsInt_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩; try iexact Hv)
        | (wp_apply h_valueUnstructured_IsFloat_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩; try iexact Hv)
        | (wp_apply h_valueUnstructured_IsList_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩; try iexact Hv)
        | (wp_apply h_valueUnstructured_IsMap_ptr p dq _ $$ [Hv] as %r ⟨Hv, %rfl⟩; try iexact Hv)
        | (simp only [UVal.isIntB, UVal.isStrB, UVal.isBoolB, UVal.isListB, UVal.isMapB, UVal.isFloatB]; wp_auto)
        | wp_auto)

end proof

end smd
end EtcdGrove
end Perennial
