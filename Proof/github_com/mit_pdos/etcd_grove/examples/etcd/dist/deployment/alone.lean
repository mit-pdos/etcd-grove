/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/alone.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.alone

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem deployment.alone.wp_proof :
    etcd_dist.deployment.alone.spec (GF := GF) (hG := hG) := by
  intro k
  by_cases h5 : k = W64 5
  · subst h5
    rw [show kindAlone (W64 5) = true by decide]
    wp_start
    wp_auto
    wp_end
  by_cases h6 : k = W64 6
  · subst h6
    rw [show kindAlone (W64 6) = true by decide]
    wp_start
    wp_auto
    wp_end
  rw [show kindAlone k = false by simp [kindAlone, h5, h6]]
  wp_start
  wp_auto
  repeat (simp only [h5, h6, decide_false, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; wp_auto)
  wp_end

end proof

end etcd_dist
end EtcdGrove
end Perennial
