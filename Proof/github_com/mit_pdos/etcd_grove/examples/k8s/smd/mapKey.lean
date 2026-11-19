/-
`mapKey` (`examples/k8s/smd/smd.go`). Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.mapKey
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.FieldNameElement

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

theorem mapKey.wp_proof
    (wp_FieldNameElement : smd.fieldpath.FieldNameElement.spec (GF := GF)) :
    mapKey.spec (GF := GF) := fun n k => by
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply wp_FieldNameElement as %e1 He1
  wp_apply wp_FieldNameElement as %e2 He2
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
  simp only [k8s_smd.mapKey, ownPEL]
  isplitl [He1]
  · iexact He1
  isplitl [He2]
  · iexact He2
  itrivial

end proof

end k8s_smd
end EtcdGrove
end Perennial
