/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/needsSoleWriter.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.needsSoleWriter

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

theorem needsSoleWriter.wp_proof :
    etcd_dist.needsSoleWriter.spec (GF := GF) (hG := hG) := by
  intro k
  by_cases h0 : k = W64 0
  · subst h0
    rw [show kindNeedsSoleWriter (W64 0) = true by decide]
    wp_start
    wp_auto
    wp_end
  by_cases h1 : k = W64 1
  · subst h1
    rw [show kindNeedsSoleWriter (W64 1) = true by decide]
    wp_start
    wp_auto
    wp_end
  by_cases h2 : k = W64 2
  · subst h2
    rw [show kindNeedsSoleWriter (W64 2) = true by decide]
    wp_start
    wp_auto
    wp_end
  by_cases h5 : k = W64 5
  · subst h5
    rw [show kindNeedsSoleWriter (W64 5) = true by decide]
    wp_start
    wp_auto
    wp_end
  by_cases h6 : k = W64 6
  · subst h6
    rw [show kindNeedsSoleWriter (W64 6) = true by decide]
    wp_start
    wp_auto
    wp_end
  rw [show kindNeedsSoleWriter k = false by simp only [kindNeedsSoleWriter, ne_eq, h0, h1, h2, h5, h6, not_false_eq_true, and_self, or_self, decide_true, decide_false]]
  wp_start
  wp_auto
  repeat (simp only [h0, h1, h2, h5, h6, decide_false, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; try wp_auto)
  wp_end

end proof

end etcd_dist
end EtcdGrove
end Perennial
