/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/MainDeployment.lean`. Lean-first; N7-kv.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.MainDeployment
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.MainReady
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.WellFormed
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Deployment__Endpoints

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

theorem RunKV.wp_proof (OP : List GoString → w64 → IProp GF)
theorem MainDeployment.wp_proof (OP : List GoString → w64 → IProp GF)
    (hWF : WellFormed.spec (GF := GF) (hG := hG))
    (hEp : Deployment.Endpoints.spec (GF := GF) (hG := hG))
    (hMR : MainReady.spec (GF := GF) (hG := hG) OP) :
    MainDeployment.spec (GF := GF) (hG := hG) OP := by
  intro v d j ready
  wp_start as ⟨%Hp, #Hd, #Hready, Hsh⟩
  obtain ⟨Hkv, Hfips⟩ := Hp
  wp_auto
  wp_apply (hWF v d Hfips) as %err %Herr
  · iframe #
  wp_if_destruct
  · wp_func_call; wp_call; wp_auto
    iapply HΦ; done
  sorry

end proof

end etcd_dist
end EtcdGrove
end Perennial
