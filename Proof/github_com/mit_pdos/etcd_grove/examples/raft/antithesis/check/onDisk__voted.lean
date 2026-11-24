/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.voted()` (B 291-359, `OnDisk.voted`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__voted
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__w
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__V1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__vote
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

theorem onDisk.voted.wp_proof (wp_w : onDisk.w.spec (GF := GF) (hG := hG))
    (wp_V1 : onDisk.V1.spec (GF := GF) (hG := hG)) (wp_vote : Event.vote.spec (GF := GF) (hG := hG)) :
    onDisk.voted.spec (GF := GF) (hG := hG) := by
  intro g x v
  wp_start as ⟨#Hx, %Hv⟩
  unfold OnDisk.voted at Hv
  obtain ⟨vo, hvo, Hv⟩ := bind_ok Hv
  obtain ⟨v1, hv1, Hv⟩ := bind_ok Hv
  simp only [pure_ok, Except.ok.injEq] at Hv
  subst Hv
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'w.method_unfold]
  try wp_auto
  wp_apply wp_w g x $$ [Hx] as %e #He
  · iexact Hx
  try wp_auto
  wp_apply wp_vote e x.w vo $$ [He]
  · iframe He; ipureintro; exact hvo
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'V1.method_unfold]
  try wp_auto
  wp_apply wp_V1 g x v1 $$ [Hx]
  · iframe Hx; ipureintro; exact hv1
  try wp_auto
  have : (!decide (vo = v1)) = (vo != v1) := by by_cases h : vo = v1 <;> simp [h]
  rw [this]
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
