/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/NodeMain.lean`. Lean-first; N7-kv.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeMain
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Rotate
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.NodeWith
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

theorem RunKV.wp_proof (OP : List GoString → w64 → IProp GF)
theorem NodeMain.wp_proof (NP : w64 → GoString → List GoString → IProp GF)
    (hNC : NodeCount.spec (GF := GF) (hG := hG))
    (hRot : Rotate.spec (GF := GF) (hG := hG))
    (hNode : Node.specWith (GF := GF) (hG := hG) NP) :
    NodeMain.spec (GF := GF) (hG := hG) NP := by
  intro w c addr eps epsL
  wp_start as ⟨%Hp, #Heps, HNP⟩
  obtain ⟨Hk, Hb⟩ := Hp
  have hnc : w.goNodeCount = w.clients := by simp [Workload.goNodeCount, Hk]
  ihave %Hel := ownSlice_len _ _ _ $$ Heps
  wp_auto
  wp_if_destruct
  · iapply HΦ; done
  wp_apply hNC as -
  rw [hnc]
  wp_auto
  wp_if_destruct
  · iapply HΦ; done
  wp_if_destruct
  · iapply HΦ; done
  simp only [Workload.val, Hk]
  wp_auto
  wp_apply (hRot (V := GoString) (T := go.string) eps DFrac.discard epsL c) as %out ⟨-, Hout⟩
  · iframe #
    ipureintro
    constructor <;> word
  wp_apply (hNode c addr out _) $$ [Hout HNP] as -
  · iframe
  wp_auto
  iapply HΦ; done

end proof

end etcd_dist
end EtcdGrove
end Perennial
