module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.outEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem Output_eq_iff (a b : Output) : a = b ↔
    a.Err' = b.Err' ∧ a.ErrKey' = b.ErrKey' ∧ a.ErrRV' = b.ErrRV' ∧ a.Name' = b.Name' ∧
    a.Value' = b.Value' ∧ a.RV' = b.RV' := by
  cases a; cases b; simp [and_assoc]

theorem outEqual.wp_proof : outEqual.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  wp_auto
  repeat' wp_if_destruct
  all_goals first
    | (rw [decide_eq_false (fun h => by subst h; simp_all)]; iapply HΦ; itrivial)
    | (rw [decide_eq_true (by rw [Output_eq_iff]; and_intros <;> assumption)]
       iapply HΦ; itrivial)

end proof

end k8setcd3
end EtcdGrove
end Perennial
