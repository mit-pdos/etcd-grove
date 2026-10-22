/-
Lean-first (no Rocq counterpart).

The proof of `inputEqual`: Go's `==` on the struct.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.inputEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem Input_eq_iff (a b : Input) : a = b ↔
    a.Kind' = b.Kind' ∧ a.Key' = b.Key' ∧ a.Val' = b.Val' ∧ a.Reject' = b.Reject' ∧
    a.NoOp' = b.NoOp' ∧ a.IgnoreNotFound' = b.IgnoreNotFound' := by
  cases a; cases b; simp [and_assoc]

theorem inputEqual.wp_proof : inputEqual.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  wp_auto
  repeat' wp_if_destruct
  all_goals first
    | (rw [decide_eq_false (fun h => by subst h; simp_all)]; iapply HΦ; itrivial)
    | (rw [decide_eq_true (by rw [Input_eq_iff]; and_intros <;> assumption)]
       iapply HΦ; itrivial)

end proof

end k8setcd3
end EtcdGrove
end Perennial
