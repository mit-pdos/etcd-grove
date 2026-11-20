/-
`itemField`: the path of a field of a container by its key, a `fieldpath.Path` literal over `KeyElement` of a
one-field `value.FieldList` literal (`isFieldList_intro`, `isPath_intro`). Lean-first (2026-11-19).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.itemField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.FieldNameElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.KeyElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface
public import Proof.sigs_k8s_io.structured_merge_diff.v7.Laws
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Intro

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open smd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

/-- `KeyElement(value.Field{Name: "name", Value: value.NewValueInterface(key)})`, as a program
fragment's result: shared by `item` and `itemField`. -/
private theorem keyFieldList_intro (hScalar : isIface_scalar.law (GF := GF))
    (hFL : isFieldList_intro.law (GF := GF)) (hPersist : isValF_persist.law (GF := GF))
    (s : GoSlice) (v : sigs_k8s_io.structured_merge_diff.v7.value.Value) (k : GoString) :
    s ↦*{DFrac.discard} [({ Name' := go!"name", Value' := v } :
        sigs_k8s_io.structured_merge_diff.v7.value.Field)] -∗
      isValF (GF := GF) v (DFrac.own 1) (.str k) -∗
      |==> isFieldList s [(go!"name", .str k)] := by
  iintro #Hs Hv
  imod (hPersist _ _ _) $$ Hv with #Hv
  imodintro
  iapply (hFL s _ [(go!"name", .str k)] rfl) $$ Hs
  simp only [List.zip_cons_cons, List.zip_nil_right, sepL, List.foldr_cons, List.foldr_nil]
  isplitr
  · isplitr
    · ipureintro; trivial
    · iexact Hv
  · itrivial

theorem itemField.wp_proof_of (hPath : isPath_intro.law (GF := GF))
    (hScalar : isIface_scalar.law (GF := GF))
    (hFL : isFieldList_intro.law (GF := GF)) (hPersist : isValF_persist.law (GF := GF))
    (wp_FieldNameElement : smd.fieldpath.FieldNameElement.spec (GF := GF))
    (wp_NewValueInterface : smd.value.NewValueInterface.spec (GF := GF))
    (wp_KeyElement : smd.fieldpath.KeyElement.spec (GF := GF)) :
    itemField.spec (GF := GF) := fun k n => by
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply wp_FieldNameElement as %e1 He1
  wp_apply (wp_NewValueInterface _ (.str k)) as %v Hv
  · iapply hScalar.2.2.2
    itrivial
  wp_apply (wp_slice_literal (l := [({ Name' := go!"name", Value' := v } :
    sigs_k8s_io.structured_merge_diff.v7.value.Field)]))
  isplitr
  · ipureintro; rfl
  iintro %fp ⟨Hfs, -⟩
  wp_auto
  imod ownSlice_persist $$ Hfs with #Hfs
  imod (keyFieldList_intro hScalar hFL hPersist _ v k) $$ Hfs Hv with #Hfl
  wp_apply (wp_KeyElement _ [(go!"name", .str k)]) as %e2 He2
  · iexact Hfl
  wp_apply wp_FieldNameElement as %e3 He3
  wp_apply (wp_slice_literal (l := [e1, e2, e3]))
  isplitr
  · ipureintro; rfl
  iintro %sp ⟨Hs, -⟩
  wp_auto
  imod ownSlice_persist $$ Hs with #Hs
  imodintro
  iapply HΦ
  iapply (hPath _ [e1, e2, e3] (itemField k n) rfl) $$ Hs
  simp only [k8s_smd.itemField, k8s_smd.item, k8s_smd.str, List.cons_append, List.nil_append, List.zip_cons_cons, List.zip_nil_right, sepL,
    List.foldr_cons, List.foldr_nil]
  iframe

theorem itemField.wp_proof
    (wp_FieldNameElement : smd.fieldpath.FieldNameElement.spec (GF := GF))
    (wp_NewValueInterface : smd.value.NewValueInterface.spec (GF := GF))
    (wp_KeyElement : smd.fieldpath.KeyElement.spec (GF := GF)) :
    itemField.spec (GF := GF) :=
  itemField.wp_proof_of isPath_intro_law_holds isIface_scalar_law_holds isFieldList_intro_law_holds
    isValF_persist_law_holds wp_FieldNameElement wp_NewValueInterface wp_KeyElement

end proof

end k8s_smd
end EtcdGrove
end Perennial
