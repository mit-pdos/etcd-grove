module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.pastRead

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem pastRead.wp_proof :
    pastRead.spec (GF := GF) (hG := hG) := by
  intro x req
  wp_start as -
  wp_auto
  by_cases h1 : x.MinRV' = []
  · rw [decide_eq_true h1]
    wp_auto
    rw [show pastReadL x req = false by simp [pastReadL, h1]]
    iapply HΦ; itrivial
  rw [decide_eq_false h1]
  wp_auto
  wp_if_destruct
  · rw [show pastReadL x (W64 0) = false by simp [pastReadL]]
    iapply HΦ; itrivial
  rename_i h2
  wp_if_destruct
  · rw [show pastReadL x req = true by simp_all [pastReadL]]
    iapply HΦ; itrivial
  have h3 := Hif
  by_cases h4 : x.Match' = W64 0
  · rw [decide_eq_true h4]
    cases hr : x.Recursive'
    · (try wp_auto)
      simp only [hr]
      (try wp_auto)
      rw [show pastReadL x req = false by simp_all [pastReadL]]
      iapply HΦ; itrivial
    · (try wp_auto)
      simp only [hr]
      (try wp_auto)
      rw [show pastReadL x req = decide (sint.Z (W64 0) < sint.Z x.Limit') by simp_all [pastReadL]]
      iapply HΦ; itrivial
  · rw [decide_eq_false h4]
    wp_auto
    rw [show pastReadL x req = false by simp_all [pastReadL]]
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
