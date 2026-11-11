module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.isWrite

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

theorem isWrite.wp_proof : isWrite.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start as -
  wp_auto
  rcases Bool.eq_false_or_eq_true (decide (x.Kind' = W64 0)) with h1 | h1 <;> rw [h1] <;> (try wp_auto) <;>
    rcases Bool.eq_false_or_eq_true (decide (x.Kind' = W64 1)) with h2 | h2 <;> (try rw [h2]) <;>
    (try wp_auto)
  all_goals (simp only [isWriteL, h1, h2, Bool.true_or, Bool.false_or]; iapply HΦ; itrivial)

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
