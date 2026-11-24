/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.isApp()` (B 291-359, `OnDisk.isApp`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__isApp
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__bat
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__hasM
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__m
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__T1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__typ
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__term
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem onDisk.isApp.wp_proof (wp_bat : onDisk.bat.spec (GF := GF) (hG := hG))
    (wp_hasM : onDisk.hasM.spec (GF := GF) (hG := hG)) (wp_m : onDisk.m.spec (GF := GF) (hG := hG))
    (wp_T1 : onDisk.T1.spec (GF := GF) (hG := hG)) (wp_typ : Msg.typ.spec (GF := GF) (hG := hG))
    (wp_term : Msg.term.spec (GF := GF) (hG := hG)) :
    onDisk.isApp.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  unfold OnDisk.isApp at Hv
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'bat.method_unfold]
  try wp_auto
  wp_apply wp_bat gx x $$ [Hx]
  · iexact Hx
  cases hb : x.bat
  · rw [hb] at Hv; simp only [pure_ok, andM_ok_false, Except.ok.injEq] at Hv; subst Hv
    try wp_auto
    iapply HΦ; ipureintro; trivial
  rw [hb] at Hv; simp only [pure_ok, andM_ok_true] at Hv
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'hasM.method_unfold]
  try wp_auto
  wp_apply wp_hasM gx x $$ [Hx]
  · iexact Hx
  cases hh : x.hasM
  · rw [hh] at Hv; simp only [pure_ok, andM_ok_false, Except.ok.injEq] at Hv; subst Hv
    try wp_auto
    iapply HΦ; ipureintro; trivial
  rw [hh] at Hv; simp only [pure_ok, andM_ok_true] at Hv
  obtain ⟨c, hc, ht, hf⟩ := andM_ok Hv
  obtain ⟨m, hm, hc⟩ := bind_ok hc
  obtain ⟨ty, hty, hc⟩ := bind_ok hc
  simp only [pure_ok, Except.ok.injEq] at hc
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'm.method_unfold]
  try wp_auto
  wp_apply wp_m gx x m $$ [Hx] as %u #Hu
  · iframe Hx; ipureintro; exact hm
  try wp_auto
  wp_apply wp_typ u m ty $$ [Hu]
  · iframe Hu; ipureintro; exact hty
  try wp_auto
  by_cases happ : ty = go!"app"
  case neg =>
    rw [decide_eq_false happ]
    have : c = false := by rw [← hc]; simp [happ]
    rw [hf this]
    try wp_auto
    iapply HΦ; ipureintro; trivial
  rw [decide_eq_true happ]
  have : c = true := by rw [← hc]; simp [happ]
  have Hr := ht this
  obtain ⟨m', hm', Hr⟩ := bind_ok Hr
  rw [hm] at hm'; cases hm'
  obtain ⟨mt, hmt, Hr⟩ := bind_ok Hr
  obtain ⟨t1, ht1, Hr⟩ := bind_ok Hr
  simp only [pure_ok, Except.ok.injEq] at Hr
  subst Hr
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'm.method_unfold]
  try wp_auto
  wp_apply wp_m gx x m $$ [Hx] as %u' #Hu'
  · iframe Hx; ipureintro; exact hm
  try wp_auto
  wp_apply wp_term u' m mt $$ [Hu'] as %w1 %Hw1
  · iframe Hu'; ipureintro; exact hmt
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'T1.method_unfold]
  try wp_auto
  wp_apply wp_T1 gx x t1 $$ [Hx] as %w2 %Hw2
  · iframe Hx; ipureintro; exact ht1
  try wp_auto
  rw [decide_w64_eq, Hw1, Hw2, decide_eq_beq']
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
