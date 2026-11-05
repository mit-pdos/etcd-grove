module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.sameObj

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

theorem sameObj.wp_proof :
    sameObj.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start as -
  wp_auto
  by_cases h1 : a.Name' = b.Name'
  · rw [decide_eq_true h1]
    wp_auto
    by_cases h2 : a.UID' = b.UID'
    · rw [decide_eq_true h2]
      wp_auto
      rw [show decide (a.Value' = b.Value') = sameObjL a b by simp [sameObjL, h1, h2]]
      iapply HΦ; itrivial
    · rw [decide_eq_false h2]
      wp_auto
      rw [show false = sameObjL a b by simp [sameObjL, h1, h2]]
      iapply HΦ; itrivial
  · rw [decide_eq_false h1]
    wp_auto
    rw [show false = sameObjL a b by simp [sameObjL, h1]]
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
