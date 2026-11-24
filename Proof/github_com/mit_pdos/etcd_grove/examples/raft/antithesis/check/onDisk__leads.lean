/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.leads()` (B 291-359, `OnDisk.leads`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__leads
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__w
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__role
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem onDisk.leads.wp_proof (wp_w : onDisk.w.spec (GF := GF) (hG := hG))
    (wp_role : Event.role.spec (GF := GF) (hG := hG)) :
    onDisk.leads.spec (GF := GF) (hG := hG) := by
  intro g x v
  wp_start as ⟨#Hx, %Hv⟩
  unfold OnDisk.leads at Hv
  obtain ⟨y, hy, rfl⟩ := fieldEq_ok Hv
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'w.method_unfold]
  try wp_auto
  wp_apply wp_w g x $$ [Hx] as %e #He
  · iexact Hx
  try wp_auto
  wp_apply wp_role e x.w y $$ [He]
  · iframe He; ipureintro; exact hy
  try wp_auto
  have : decide (y = go!"leader") = (y == leader) := by
    by_cases h : y = go!"leader" <;> simp [h, leader]
  rw [this]
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
