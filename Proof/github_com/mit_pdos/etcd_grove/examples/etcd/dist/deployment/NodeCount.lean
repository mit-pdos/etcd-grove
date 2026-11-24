/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/NodeCount.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.NodeCount

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

theorem deployment.NodeCount.wp_proof :
    etcd_dist.deployment.NodeCount.spec (GF := GF) (hG := hG) := by
  intro w
  wp_start
  wp_auto
  repeat wp_if_destruct
  all_goals first
    | wp_end
    | (unfold Workload.goNodeCount Workload.val at *; simp_all (config := { decide := true }); wp_end)

end proof

end etcd_dist
end EtcdGrove
end Perennial
