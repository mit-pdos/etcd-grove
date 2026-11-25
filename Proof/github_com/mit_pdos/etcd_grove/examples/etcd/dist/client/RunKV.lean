/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/RunKV.lean`. Lean-first; N7-kv.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunKV
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.OrchWith
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
    (hOrch : Orch.specWith (GF := GF) (hG := hG) OP) :
    RunKV.spec (GF := GF) (hG := hG) OP := by
  intro nodes ns ops ready
  wp_start as ⟨#Hnodes, #Hready, HOP⟩
  wp_auto
  iunfold readySpec at Hready
  wp_apply Hready as -
  wp_auto
  wp_apply (hOrch nodes ns ops _) $$ [HOP] as %r %hr
  · iframe #
    iframe
  wp_auto
  wp_if_destruct
  · exact absurd rfl hr
  wp_auto
  wp_if_destruct
  · wp_auto
    try wp_func_call
    try wp_call
    wp_auto
    iapply HΦ; done
  · wp_auto
    try wp_func_call
    try wp_call
    wp_auto
    iapply HΦ; done

end proof

end etcd_dist
end EtcdGrove
end Perennial
