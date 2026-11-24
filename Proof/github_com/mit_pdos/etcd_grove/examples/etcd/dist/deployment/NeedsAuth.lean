/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/NeedsAuth.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.NeedsAuth
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

theorem deployment.NeedsAuth.wp_proof (hAlone : etcd_dist.deployment.alone.spec (GF := GF) (hG := hG)) :
    etcd_dist.deployment.NeedsAuth.spec (GF := GF) (hG := hG) := by
  intro k
  wp_start
  wp_auto
  wp_apply hAlone
  wp_end

end proof

end etcd_dist
end EtcdGrove
end Perennial
