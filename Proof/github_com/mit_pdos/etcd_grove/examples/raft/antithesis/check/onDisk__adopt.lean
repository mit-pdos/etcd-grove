/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.adopt()` (B 291-359, `OnDisk.adopt`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__adopt
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__T0
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__T1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__elect
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

theorem onDisk.adopt.wp_proof (wp_T0 : onDisk.T0.spec (GF := GF) (hG := hG))
    (wp_T1 : onDisk.T1.spec (GF := GF) (hG := hG)) (wp_elect : onDisk.elect.spec (GF := GF) (hG := hG)) :
    onDisk.adopt.spec (GF := GF) (hG := hG) := by
  intro g x v
  wp_start as ⟨#Hx, %Hv⟩
  unfold OnDisk.adopt at Hv
  obtain ⟨c, hc, ht, hf⟩ := andM_ok Hv
  obtain ⟨t1, ht1, hc⟩ := bind_ok hc
  simp only [pure_ok, Except.ok.injEq] at hc
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_T1_unfold.method_unfold]
  try wp_auto
  wp_apply wp_T1 g x t1 $$ [Hx] as %u1 %Hu1
  · iframe Hx; ipureintro; exact ht1
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_T0_unfold.method_unfold]
  try wp_auto
  wp_apply wp_T0 g x $$ [Hx] as %u0 %Hu0
  · iexact Hx
  try wp_auto
  rw [decide_w64_eq, Hu1, Hu0]
  by_cases he : t1 = x.T0
  · rw [decide_eq_true he]
    have : c = false := by rw [← hc]; simp [he]
    rw [hf this]
    try wp_auto
    iapply HΦ; ipureintro; trivial
  rw [decide_eq_false he]
  have : c = true := by rw [← hc]; simp [he]
  have Hr := ht this
  unfold notM at Hr
  obtain ⟨el, hel, Hr⟩ := bind_ok Hr
  simp only [pure_ok, Except.ok.injEq] at Hr
  subst Hr
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_elect_unfold.method_unfold]
  try wp_auto
  wp_apply wp_elect g x el $$ [Hx]
  · iframe Hx; ipureintro; exact hel
  try wp_auto
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
