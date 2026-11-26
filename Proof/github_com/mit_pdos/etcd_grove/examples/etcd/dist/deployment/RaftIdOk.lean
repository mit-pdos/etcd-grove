/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/RaftIdOk.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.RaftIdOk

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

theorem RaftIdOk.wp_proof :
    etcd_dist.RaftIdOk.spec (GF := GF) (hG := hG) := by
  intro id
  have e : raftIdOk id =
      (!decide (id = W64 18446744073709551615) && !decide (id = W64 18446744073709551614)) := by
    unfold raftIdOk
    by_cases h1 : id = W64 18446744073709551615 <;> by_cases h2 : id = W64 18446744073709551614 <;>
      simp [h1, h2]
  rw [e]
  wp_start
  wp_auto
  by_cases h1 : id = W64 18446744073709551615
  · subst h1
    simp only [_root_.decide_true, Bool.not_true, Bool.false_and, ↓reduceIte]
    wp_auto
    wp_end
  · simp only [h1, _root_.decide_false, Bool.not_false, Bool.true_and, ↓reduceIte]
    wp_auto
    wp_end

end proof

end etcd_dist
end EtcdGrove
end Perennial
