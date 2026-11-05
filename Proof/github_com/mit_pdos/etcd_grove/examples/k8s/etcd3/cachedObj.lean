module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cachedObj

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem cachedObj.wp_proof :
    cachedObj.spec (GF := GF) (hG := hG) := by
  intro x
  cases hu : x.UseCached'
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_start as -
    wp_auto
    rw [hu]
    wp_auto
    iapply HΦ
    ipureintro
    rfl
  · simp only [↓reduceIte]
    wp_start as -
    wp_auto
    rw [hu]
    wp_auto
    iapply HΦ
    iexists _
    iframe
    ipureintro
    rfl

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
