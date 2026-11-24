/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/NodeCount.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.NodeCount

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

theorem deployment.NodeCount.wp_proof :
    etcd_dist.deployment.NodeCount.spec (GF := GF) (hG := hG) := by
  intro w
  obtain ⟨kd, cl, op⟩ := w
  simp only [Workload.val]
  by_cases h0 : kd = W64 0
  · subst h0
    rw [show Workload.goNodeCount ⟨W64 0, cl, op⟩ = cl by simp [Workload.goNodeCount]]
    wp_start
    wp_auto
    wp_end
  by_cases h1 : kd = W64 1
  · subst h1
    rw [show Workload.goNodeCount ⟨W64 1, cl, op⟩ = cl by simp [Workload.goNodeCount]]
    wp_start
    wp_auto
    wp_end
  by_cases h2 : kd = W64 2
  · subst h2
    rw [show Workload.goNodeCount ⟨W64 2, cl, op⟩ = cl by simp [Workload.goNodeCount]]
    wp_start
    wp_auto
    wp_end
  by_cases h5 : kd = W64 5
  · subst h5
    rw [show Workload.goNodeCount ⟨W64 5, cl, op⟩ = W64 4 by simp [Workload.goNodeCount]]
    wp_start
    wp_auto
    wp_end
  rw [show Workload.goNodeCount ⟨kd, cl, op⟩ = W64 0 by
    unfold Workload.goNodeCount; dsimp only
    rw [if_neg (by rintro (h | h | h) <;> contradiction), if_neg h5]]
  wp_start
  wp_auto
  repeat (simp only [h0, h1, h2, h5, decide_false, Bool.not_false, Bool.false_eq_true, ↓reduceIte]; try wp_auto)
  wp_end

end proof

end etcd_dist
end EtcdGrove
end Perennial
