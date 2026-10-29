/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/watcher__ResultChan.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.watcher__ResultChan

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem watcher.ResultChan.wp_proof : watcher.ResultChan.spec (GF := GF) (hG := hG) := by
  intro _ w γ γw r ns bm inits
  wp_start as Hw
  unfold watchAt
  icases Hw with ⟨%w', %ch, %dch, %s, %cfg, %g, %Heq, #Hch, #Hdch, #Hs, #Hsrv, #Hsp, #Hdsp, #Hreg⟩
  have : w' = w := by
    have h := congrArg (fun x => match x with | GoInterface.ok i => i.v | _ => #()) Heq
    simp at h
    exact (go.intoVal_inj h).symm
  subst this
  wp_auto
  iapply HΦ
  iexact Hsp

end proof

end apimodel
end EtcdGrove
end Perennial
