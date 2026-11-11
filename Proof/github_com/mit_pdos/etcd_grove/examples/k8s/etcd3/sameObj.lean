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
  rcases Bool.eq_false_or_eq_true (decide (a.Namespace' = b.Namespace')) with h1 | h1 <;>
    rw [h1] <;> (try wp_auto) <;>
    rcases Bool.eq_false_or_eq_true (decide (a.Name' = b.Name')) with h2 | h2 <;> (try rw [h2]) <;>
    (try wp_auto) <;>
    rcases Bool.eq_false_or_eq_true (decide (a.UID' = b.UID')) with h3 | h3 <;> (try rw [h3]) <;>
    (try wp_auto) <;>
    rcases Bool.eq_false_or_eq_true (decide (a.Value' = b.Value')) with h4 | h4 <;> (try rw [h4]) <;>
    (try wp_auto) <;>
    rcases Bool.eq_false_or_eq_true (decide (a.Node' = b.Node')) with h5 | h5 <;> (try rw [h5]) <;>
    (try wp_auto)
  all_goals (simp only [sameObjL, h1, h2, h3, h4, h5, Bool.true_and, Bool.false_and,
      Bool.and_true, Bool.and_false]; iapply HΦ; itrivial)

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
