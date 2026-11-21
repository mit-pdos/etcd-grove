/-
`typed.setItemToPathElement`: proved (Prove phase, 2026-11-21): case on the item's kind; a map, a
list or null gives an `errors.New` error (Perennial's `errors.wp_New`), a scalar `pe.Value = &child`.

Callees without a spec file here (other packages', the standard library's, or the
walker's own interface calls through a bundle): `errors.New`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.setItemToPathElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsList_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsMap_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsNull_ptr
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA3
public import Perennial.Proof.errors.Link

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

set_option linter.unusedSimpArgs false in
theorem typed.setItemToPathElement.wp_proof
    (h_valueUnstructured_IsList_ptr : value.valueUnstructured.IsList_ptr.spec (GF := GF))
    (h_valueUnstructured_IsMap_ptr : value.valueUnstructured.IsMap_ptr.spec (GF := GF))
    (h_valueUnstructured_IsNull_ptr : value.valueUnstructured.IsNull_ptr.spec (GF := GF)) :
    typed.setItemToPathElement.spec (GF := GF) :=
    fun child dq x => by
  wp_start as Hv
  ihave ⟨Hv, %hsh⟩ := LawA3.isValF_shape _ _ _ $$ Hv
  obtain ⟨p, rfl⟩ := hsh
  wp_auto
  wp_apply h_valueUnstructured_IsMap_ptr p dq _ $$ [Hv] as %r1 ⟨Hv, %hr1⟩
  · iframe
  subst hr1
  try wp_auto
  cases x
  case map kvs =>
    simp only [UVal.isMapB, decide_true]
    try wp_auto
    wp_apply _root_.Perennial.errors.wp_New as %err _
    try wp_auto
    iapply HΦ
    iframe
    ipureintro
    simp [UVal.isBoolB, UVal.isIntB, UVal.isStrB]
  case list vs =>
    simp only [UVal.isMapB, Bool.true_eq_false, decide_false]
    try wp_auto
    wp_apply h_valueUnstructured_IsList_ptr p dq _ $$ [Hv] as %r2 ⟨Hv, %hr2⟩
    · iframe
    subst hr2
    simp only [UVal.isListB, Bool.true_eq_false, decide_false, decide_true]
    try wp_auto
    wp_apply _root_.Perennial.errors.wp_New as %err _
    try wp_auto
    iapply HΦ
    iframe
    ipureintro
    simp [UVal.isBoolB, UVal.isIntB, UVal.isStrB]
  case null =>
    simp only [UVal.isMapB, Bool.true_eq_false, decide_false]
    try wp_auto
    wp_apply h_valueUnstructured_IsList_ptr p dq _ $$ [Hv] as %r2 ⟨Hv, %hr2⟩
    · iframe
    subst hr2
    simp only [UVal.isListB, Bool.true_eq_false, decide_false, decide_true]
    try wp_auto
    wp_apply h_valueUnstructured_IsNull_ptr p dq _ $$ [Hv] as %r3 ⟨Hv, %hr3⟩
    · iframe
    subst hr3
    simp only [UVal.isNullB, Bool.true_eq_false, decide_false, decide_true]
    try wp_auto
    wp_apply _root_.Perennial.errors.wp_New as %err _
    try wp_auto
    iapply HΦ
    iframe
    ipureintro
    simp [UVal.isBoolB, UVal.isIntB, UVal.isStrB]
  case bool b =>
    simp only [UVal.isMapB, Bool.true_eq_false, decide_false]
    try wp_auto
    wp_apply h_valueUnstructured_IsList_ptr p dq _ $$ [Hv] as %r2 ⟨Hv, %hr2⟩
    · iframe
    subst hr2
    simp only [UVal.isListB, Bool.true_eq_false, decide_false, decide_true]
    try wp_auto
    wp_apply h_valueUnstructured_IsNull_ptr p dq _ $$ [Hv] as %r3 ⟨Hv, %hr3⟩
    · iframe
    subst hr3
    simp only [UVal.isNullB, Bool.true_eq_false, decide_false, decide_true]
    try wp_auto
    iapply HΦ
    iframe
    ipureintro
    simp [UVal.isBoolB, UVal.isIntB, UVal.isStrB]
  case int i =>
    simp only [UVal.isMapB, Bool.true_eq_false, decide_false]
    try wp_auto
    wp_apply h_valueUnstructured_IsList_ptr p dq _ $$ [Hv] as %r2 ⟨Hv, %hr2⟩
    · iframe
    subst hr2
    simp only [UVal.isListB, Bool.true_eq_false, decide_false, decide_true]
    try wp_auto
    wp_apply h_valueUnstructured_IsNull_ptr p dq _ $$ [Hv] as %r3 ⟨Hv, %hr3⟩
    · iframe
    subst hr3
    simp only [UVal.isNullB, Bool.true_eq_false, decide_false, decide_true]
    try wp_auto
    iapply HΦ
    iframe
    ipureintro
    simp [UVal.isBoolB, UVal.isIntB, UVal.isStrB]
  case str s =>
    simp only [UVal.isMapB, Bool.true_eq_false, decide_false]
    try wp_auto
    wp_apply h_valueUnstructured_IsList_ptr p dq _ $$ [Hv] as %r2 ⟨Hv, %hr2⟩
    · iframe
    subst hr2
    simp only [UVal.isListB, Bool.true_eq_false, decide_false, decide_true]
    try wp_auto
    wp_apply h_valueUnstructured_IsNull_ptr p dq _ $$ [Hv] as %r3 ⟨Hv, %hr3⟩
    · iframe
    subst hr3
    simp only [UVal.isNullB, Bool.true_eq_false, decide_false, decide_true]
    try wp_auto
    iapply HΦ
    iframe
    ipureintro
    simp [UVal.isBoolB, UVal.isIntB, UVal.isStrB]

end proof

end smd
end EtcdGrove
end Perennial
