/-
`containerPaths` (`examples/k8s/smd/smd.go`). Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.containerPaths
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.item
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.itemField

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

theorem containerPaths.wp_proof
    (wp_item : item.spec (GF := GF))
    (wp_itemField : itemField.spec (GF := GF)) :
    containerPaths.spec (GF := GF) := fun k => by
  wp_start
  wp_auto
  wp_apply wp_item as %s1 H1
  wp_apply wp_itemField as %s2 H2
  wp_apply wp_itemField as %s3 H3
  wp_apply (wp_slice_literal (l := [s1, s2, s3]))
  isplitr
  · ipureintro; rfl
  iintro %sp ⟨Hs, -⟩
  wp_auto
  iapply HΦ
  iexists [s1, s2, s3]
  isplitl [Hs]
  · iexact Hs
  simp only [k8s_smd.containerPaths, ownPaths]
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · iexact H2
  isplitl [H3]
  · iexact H3
  itrivial

end proof

end k8s_smd
end EtcdGrove
end Perennial
