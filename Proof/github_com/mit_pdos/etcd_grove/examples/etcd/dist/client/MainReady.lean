/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/MainReady.lean`. Lean-first; N7-kv.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.MainReady
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunKV
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]

theorem MainReady.wp_proof (OP : List GoString → w64 → IProp GF)
    (hNC : NodeCount.spec (GF := GF) (hG := hG))
    (hRun : RunKV.spec (GF := GF) (hG := hG) OP) :
    MainReady.spec (GF := GF) (hG := hG) OP := by
  intro w eps nodes ns ready
  wp_start as ⟨%Hk, #Hnodes, #Hready, HOP⟩
  wp_auto
  wp_if_destruct
  · wp_func_call; wp_call; wp_auto
    iapply HΦ; ipureintro; trivial
  wp_apply hNC
  wp_if_destruct
  · -- `hasSetUp(KV)` is false: `ready()`
    wp_func_call; wp_call; wp_auto
    simp only [Workload.val, Hk]
    wp_auto
    iunfold readySpec at Hready
    wp_apply Hready
    -- the switch: kind 0, `RunKV`
    wp_apply (hRun nodes ns w.ops ready) $$ [HOP] as %r -
    · iunfold readySpec; iframe #; iframe
    iapply HΦ; ipureintro; trivial
  · wp_func_call; wp_call; wp_auto
    iapply HΦ; ipureintro; trivial

end proof

end etcd_dist
end EtcdGrove
end Perennial
