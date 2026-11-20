module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.preMsg
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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem preMsg.wp_proof (wp_rvString : rvString.spec (GF := GF) (hG := hG)) :
    preMsg.spec (GF := GF) (hG := hG) := by
  intro x o
  by_cases hu : x.HasPreUID' = true ∧ x.PreUID' ≠ o.UID'
  · obtain ⟨hu, he⟩ := hu
    have hm : preMsgL x o = ((go!"Precondition failed: UID in precondition: " ++ x.PreUID') ++
        go!", UID in object meta: ") ++ o.UID' := by simp [preMsgL, hu, he]
    rw [hm]
    wp_start as -
    wp_auto
    rw [hu]
    wp_auto
    rw [decide_eq_false he]
    wp_auto
    iapply HΦ; itrivial
  · have hm : preMsgL x o = ((go!"Precondition failed: ResourceVersion in precondition: " ++
        x.PreRV') ++ go!", ResourceVersion in object meta: ") ++ rvStr o.ResourceVersion' := by
      unfold preMsgL
      rw [if_neg]
      intro h
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      exact hu h
    rw [hm]
    wp_start as -
    wp_auto
    cases h1 : x.HasPreUID'
    · wp_auto
      wp_apply wp_rvString
      iapply HΦ; itrivial
    · have he : x.PreUID' = o.UID' := Classical.byContradiction fun e => hu ⟨h1, e⟩
      wp_auto
      rw [decide_eq_true he]
      wp_auto
      wp_apply wp_rvString
      iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
