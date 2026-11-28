/- Lean-first (no Rocq counterpart). `PinnedRead`'s proof (k8s-dist K9 step 5). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PinnedRead


@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem PinnedRead.wp_proof :
    PinnedRead.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start as -
  wp_auto
  by_cases h4 : x.Kind' = W64 4
  · rw [decide_eq_true h4]
    wp_auto
    wp_if_destruct
    · rw [show pinnedReadL x = true by simp [pinnedReadL, h4]; word]
      iapply HΦ; itrivial
    · rename_i hl
      rw [show pinnedReadL x = decide (x.Kind' = W64 5) by simp [pinnedReadL, h4]; word]
      iapply HΦ; itrivial
  · rw [decide_eq_false h4]
    wp_auto
    rw [show pinnedReadL x = decide (x.Kind' = W64 5) by simp [pinnedReadL]; intro h; exact absurd h h4]
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
