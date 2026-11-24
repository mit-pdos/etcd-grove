/-
Lean-first (no Rocq counterpart). #33 S3b W3a (2026-11-23): the proof of `x.cmt()` (B 214-253, `InMem.cmt`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__cmt
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__leads
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__L
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__c
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__known
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__T
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermAt
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

theorem inMem.cmt.wp_proof
    (wp_leads : inMem.leads.spec (GF := GF) (hG := hG))
    (wp_c : inMem.c.spec (GF := GF) (hG := hG))
    (wp_known : inMem.known.spec (GF := GF) (hG := hG))
    (wp_L : inMem.L.spec (GF := GF) (hG := hG))
    (wp_T : inMem.T.spec (GF := GF) (hG := hG))
    (wp_TermAt : TermAt.spec (GF := GF) (hG := hG)) :
    inMem.cmt.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  wp_auto
  unfold InMem.cmt at Hv
  obtain ⟨a, ha, hat, haf⟩ := andM_ok Hv
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_unfold'leads.method_unfold]
  try wp_auto
  wp_apply wp_leads gx x a $$ [Hx]
  · iframe Hx; ipureintro; exact ha
  try wp_auto
  cases a
  · rw [haf rfl]
    try wp_auto
    iapply HΦ; ipureintro; trivial
  have Hv := hat rfl
  obtain ⟨b, hb, hbt, hbf⟩ := andM_ok Hv
  obtain ⟨c, hc, hb⟩ := bind_ok hb
  obtain ⟨k, hk, hb⟩ := bind_ok hb
  simp only [pure_ok, Except.ok.injEq] at hb
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_unfold'c.method_unfold]
  try wp_auto
  wp_apply wp_c gx x c $$ [Hx] as %uc %Huc
  · iframe Hx; ipureintro; exact hc
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_unfold'known.method_unfold]
  try wp_auto
  wp_apply wp_known gx x k $$ [Hx] as %uk %Huk
  · iframe Hx; ipureintro; exact hk
  try wp_auto
  rw [Huc, Huk]
  cases b
  · have hck : ¬ k < c := by simpa using hb
    rw [decide_eq_false hck, hbf rfl]
    try wp_auto
    iapply HΦ; ipureintro; trivial
  have hck : k < c := by simpa using hb
  rw [decide_eq_true hck]
  have Hv := hbt rfl
  clear hbt hbf haf hat
  obtain ⟨l, hl, Hv⟩ := bind_ok Hv
  rw [hc, ok_bind] at Hv
  obtain ⟨t, ht, Hv⟩ := bind_ok Hv
  simp only [pure_ok, Except.ok.injEq] at Hv
  subst Hv
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_unfold'L.method_unfold]
  try wp_auto
  wp_apply wp_L gx x l $$ [Hx] as %ul #Hul
  · iframe Hx; ipureintro; exact hl
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_unfold'c.method_unfold]
  try wp_auto
  wp_apply wp_c gx x c $$ [Hx] as %uc2 %Huc2
  · iframe Hx; ipureintro; exact hc
  try wp_auto
  wp_apply wp_TermAt ul l uc2 $$ [Hul] as %r %Hr
  · iexact Hul
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_unfold'T.method_unfold]
  try wp_auto
  wp_apply wp_T gx x t $$ [Hx] as %ut %Hut
  · iframe Hx; ipureintro; exact ht
  try wp_auto
  rw [decide_w64_eq, Hr, Hut, Huc2]
  try wp_auto
  have : decide (termAt l c = t) = (termAt l c == t) := by
    by_cases h : termAt l c = t <;> simp [h]
  rw [this]
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
