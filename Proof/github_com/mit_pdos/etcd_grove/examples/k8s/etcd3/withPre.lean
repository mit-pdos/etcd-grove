module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.withPre
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.rvString

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem withPre.wp_proof
    (wp_rvString : rvString.spec (GF := GF) (hG := hG)) :
    withPre.spec (GF := GF) (hG := hG) := by
  intro x uid rv c hasC
  cases hasC
  · simp only [withPreL, Bool.false_eq_true, ↓reduceIte]
    wp_start as -
    wp_auto
    iapply HΦ; itrivial
  cases uid <;> cases rv <;> simp only [withPreL, Bool.false_eq_true, ↓reduceIte]
  all_goals wp_start as -
  all_goals (try wp_auto)
  all_goals (try (wp_apply wp_rvString; (try wp_auto)))
  all_goals (iapply HΦ; itrivial)

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
