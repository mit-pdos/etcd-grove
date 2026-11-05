module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.rvString
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.rvBytes

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem rvString.wp_proof (wp_rvBytes : rvBytes.spec (GF := GF) (hG := hG)) :
    rvString.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    have h : rvStr (W64 0) = [] := rfl
    rw [h]
    iapply HΦ
    ipureintro; trivial
  · wp_apply wp_rvBytes
    (try wp_auto)
    have h : rvStr n = rvBytes n := by
      unfold rvStr; simp only [show ¬ n = 0 from Hif, ↓reduceIte]
    rw [h]
    iapply HΦ
    ipureintro; trivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
