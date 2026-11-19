/-
`concat` (`examples/k8s/smd/smd.go`). Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.concat

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

theorem concat.wp_proof :
    concat.spec (GF := GF) := fun a b dqa dqb xs ys => by
  wp_start as ⟨Ha, Hb⟩
  wp_auto
  wp_apply (wp_slice_literal (l := ([] : List GoSlice)))
  isplitr
  · ipureintro; rfl
  iintro %sp ⟨Hs, Hcap⟩
  wp_auto
  wp_apply wp_slice_append $$ [$Hs $Hcap $Ha] as %s1 ⟨Hs1, Hcap1, Ha⟩
  wp_apply wp_slice_append $$ [$Hs1 $Hcap1 $Hb] as %s2 ⟨Hs2, -, Hb⟩
  iapply HΦ
  iframe Ha Hb
  rw [show xs ++ ys = [] ++ xs ++ ys by simp]
  iexact Hs2

end proof

end k8s_smd
end EtcdGrove
end Perennial
