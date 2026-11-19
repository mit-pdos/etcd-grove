/-
`item` (`examples/k8s/smd/smd.go`). Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.item
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.FieldNameElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.KeyElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface

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

theorem item.wp_proof
    (wp_FieldNameElement : smd.fieldpath.FieldNameElement.spec (GF := GF))
    (wp_NewValueInterface : smd.value.NewValueInterface.spec (GF := GF))
    (wp_KeyElement : smd.fieldpath.KeyElement.spec (GF := GF)) :
    item.spec (GF := GF) := fun k => by
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply wp_FieldNameElement as %e1 He1
  wp_apply (wp_NewValueInterface _ (.str k)) as %v Hv
  · simp only [ownU]; ipureintro; trivial
  wp_apply (wp_slice_literal (l := [({ Name' := go!"name", Value' := v } : sigs_k8s_io.structured_merge_diff.v7.value.Field)]))
  isplitr
  · ipureintro; rfl
  iintro %fp ⟨Hfs, -⟩
  wp_auto
  imod ownSlice_persist $$ Hfs with #Hfs
  wp_apply (wp_KeyElement _ [(go!"name", .str k)]) $$ [Hv] as %e2 He2
  · unfold ownFieldList
    iexists _
    isplitr
    · iexact Hfs
    simp only [ownFieldsL]
    isplitr
    · ipureintro; simp
    isplitl [Hv]
    · iexact Hv
    itrivial
  wp_apply (wp_slice_literal (l := [e1, e2]))
  isplitr
  · ipureintro; rfl
  iintro %sp ⟨Hs, -⟩
  wp_auto
  imod ownSlice_persist $$ Hs with #Hs
  imodintro
  iapply HΦ
  unfold ownPath
  iexists [e1, e2]
  isplitr
  · iexact Hs
  simp only [k8s_smd.item, k8s_smd.str, ownPEL]
  isplitl [He1]
  · iexact He1
  isplitl [He2]
  · iexact He2
  itrivial

end proof

end k8s_smd
end EtcdGrove
end Perennial
