module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.GetReadConsistency

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]

theorem GetReadConsistency.wp_proof : GetReadConsistency.spec (GF := GF) (hG := hG) := by
  intro opts
  wp_start as -
  simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ConsistencyConsistent,
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ConsistencyNotOlderThan]
  wp_auto
  by_cases h : opts.ResourceVersion' = []
  · rw [decide_eq_true h, if_pos h]
    wp_auto
    simp only [rconsStr]; iapply HΦ; itrivial
  · rw [decide_eq_false h, if_neg h]
    wp_auto
    simp only [rconsStr]; iapply HΦ; itrivial

end proof

end k8s_correctness
end EtcdGrove
end Perennial
