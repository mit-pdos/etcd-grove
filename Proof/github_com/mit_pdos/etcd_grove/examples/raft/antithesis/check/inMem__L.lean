/-
Lean-first (no Rocq counterpart). #33 S3b W3a (2026-11-23): the proof of `x.L()` (B 214-253, `InMem.L`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__L
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__ll2
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__T
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__Has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__Get
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0Laws

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

theorem inMem.L.wp_proof
    (wp_ll2 : inMem.ll2.spec (GF := GF) (hG := hG))
    (wp_T : inMem.T.spec (GF := GF) (hG := hG))
    (wp_Has : TermLogs.Has.spec (GF := GF) (hG := hG))
    (wp_Get : TermLogs.Get.spec (GF := GF) (hG := hG)) :
    inMem.L.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  wp_auto
  unfold InMem.L at Hv
  obtain ⟨l2, hl2, Hv⟩ := bind_ok Hv
  obtain ⟨t, ht, Hv⟩ := bind_ok Hv
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]
  try wp_auto
  wp_apply wp_T gx x t $$ [Hx] as %ut %Hut
  · iframe Hx; ipureintro; exact ht
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_ll2_unfold.method_unfold]
  try wp_auto
  wp_apply wp_ll2 gx x l2 $$ [Hx] as %u2 #Hu2
  · iframe Hx; ipureintro; exact hl2
  try wp_auto
  wp_apply wp_Has u2 l2 ut $$ [Hu2]
  · iexact Hu2
  rw [Hut]
  cases hh : l2.has t
  · simp only [hh, Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Hv
    subst Hv
    ihave #Hn := Init0_logNil (GF := GF)
    try wp_auto
    iapply HΦ; iexact Hn
  simp only [hh, ite_true] at Hv
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]
  try wp_auto
  wp_apply wp_T gx x t $$ [Hx] as %ut2 %Hut2
  · iframe Hx; ipureintro; exact ht
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_ll2_unfold.method_unfold]
  try wp_auto
  wp_apply wp_ll2 gx x l2 $$ [Hx] as %u3 #Hu3
  · iframe Hx; ipureintro; exact hl2
  try wp_auto
  try wp_auto
  wp_apply wp_Get u3 l2 ut2 v $$ [Hu3] as %ug #Hug
  · iframe Hu3; ipureintro; rw [Hut2]; exact Hv
  try wp_auto
  iapply HΦ; iexact Hug

end proof

end AntCheck
end EtcdGrove
end Perennial
