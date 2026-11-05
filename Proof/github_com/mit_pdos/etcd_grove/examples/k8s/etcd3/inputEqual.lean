/-
Lean-first (no Rocq counterpart).

The proof of `inputEqual`: Go's `==` on the struct.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.inputEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Input_eq_iff (a b : Input) : a = b ↔
    a.Kind' = b.Kind' ∧ a.Key' = b.Key' ∧ a.Val' = b.Val' ∧ a.Reject' = b.Reject' ∧
    a.NoOp' = b.NoOp' ∧ a.IgnoreNotFound' = b.IgnoreNotFound' ∧ a.UID' = b.UID' ∧
    a.HasPreUID' = b.HasPreUID' ∧ a.PreUID' = b.PreUID' ∧ a.HasPreRV' = b.HasPreRV' ∧
    a.PreRV' = b.PreRV' ∧ a.UseCached' = b.UseCached' ∧ a.Cached'.Name' = b.Cached'.Name' ∧
    a.Cached'.UID' = b.Cached'.UID' ∧ a.Cached'.Value' = b.Cached'.Value' ∧
    a.Cached'.ResourceVersion' = b.Cached'.ResourceVersion' ∧ a.MinRV' = b.MinRV' ∧
    a.Client' = b.Client' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ⟨_, _, _, _⟩, _, _⟩ := a
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ⟨_, _, _, _⟩, _, _⟩ := b
  simp [and_assoc]

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

end k8s_etcd3
end EtcdGrove
end Perennial
