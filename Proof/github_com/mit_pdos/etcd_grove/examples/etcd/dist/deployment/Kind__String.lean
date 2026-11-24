/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/Kind__String.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Kind__String
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.kindNames

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

theorem deployment.Kind.String.wp_proof (hNames : etcd_dist.deployment.kindNames.spec (GF := GF) (hG := hG)) :
    etcd_dist.deployment.Kind.String.spec (GF := GF) (hG := hG) := by
  intro k
  wp_start
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  unfold kindName
  by_cases hk : 0 ≤ sint.Z k
  · sorry
  · sorry

end proof

end etcd_dist
end EtcdGrove
end Perennial
