/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/NodeDeployment.lean`. Lean-first; N7-kv.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeDeployment
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeMain
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.WellFormed
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Deployment__Endpoints
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Deployment__Node

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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]

theorem NodeDeployment.wp_proof (NP : w64 → GoString → List GoString → IProp GF)
    (hWF : WellFormed.spec (GF := GF) (hG := hG))
    (hEp : Deployment.Endpoints.spec (GF := GF) (hG := hG))
    (hNd : Deployment.Node.spec (GF := GF) (hG := hG))
    (hNM : NodeMain.spec (GF := GF) (hG := hG) NP) :
    NodeDeployment.spec (GF := GF) (hG := hG) NP := by
  intro v d n
  wp_start as ⟨%Hp, #Hd, Hsh⟩
  obtain ⟨Hkv, Hfips⟩ := Hp
  wp_auto
  wp_apply (hWF v d Hfips) as %err %Herr
  · iframe #
  wp_if_destruct
  · iapply HΦ; ipureintro; trivial
  sorry

end proof

end etcd_dist
end EtcdGrove
end Perennial
