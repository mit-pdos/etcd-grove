/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/writesKeys.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.writesKeys

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

theorem deployment.writesKeys.wp_proof :
    etcd_dist.deployment.writesKeys.spec (GF := GF) (hG := hG) := by
  intro k
  by_cases h7 : k = W64 7
  · subst h7
    rw [show kindWritesKeys (W64 7) = false by decide]
    wp_start
    wp_auto
    wp_end
  by_cases h8 : k = W64 8
  · subst h8
    rw [show kindWritesKeys (W64 8) = false by decide]
    wp_start
    wp_auto
    wp_end
  by_cases h9 : k = W64 9
  · subst h9
    rw [show kindWritesKeys (W64 9) = false by decide]
    wp_start
    wp_auto
    wp_end
  rw [show kindWritesKeys k = true by simp [kindWritesKeys, h7, h8, h9]]
  wp_start
  wp_auto
  repeat (simp only [h7, h8, h9, decide_false, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; wp_auto)
  wp_end

end proof

end etcd_dist
end EtcdGrove
end Perennial
