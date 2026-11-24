/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `SendableIn` (B 117-126).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SendableIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.leadersHas
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__Has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EntriesEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.RecordedIn
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

theorem SendableIn.wp_proof (wp_leadersHas : leadersHas.spec (GF := GF) (hG := hG))
    (wp_Has : TermLogs.Has.spec (GF := GF) (hG := hG))
    (wp_Get : TermLogs.Get.spec (GF := GF) (hG := hG))
    (wp_TermAt : TermAt.spec (GF := GF) (hG := hG))
    (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG))
    (wp_EntriesEqual : EntriesEqual.spec (GF := GF) (hG := hG))
    (wp_RecordedIn : RecordedIn.spec (GF := GF) (hG := hG)) :
    SendableIn.spec (GF := GF) (hG := hG) := by
  intro ldl ld lll ll chl ch tll tl g f b
  wp_start as ⟨#Hld, #Hll, #Hch, #Htl, #Hf, %Hb⟩
  obtain ⟨Hb, Hp, Hk⟩ := Hb
  iunfold appendFactRO at Hf
  icases Hf with ⟨%Hfr, #Hes⟩
  obtain ⟨hsrc, hdst, hterm, hpli, hplt, hcmt⟩ := Hfr
  ihave %Hesl := logRO_len _ _ $$ Hes
  unfold sendableIn at Hb
  wp_auto
  wp_apply wp_leadersHas ldl ld _ { server := f.src, term := f.term } $$ [Hld]
  · iframe Hld; ipureintro; exact ⟨hsrc, hterm⟩
  cases hl : ld.contains { server := f.src, term := f.term }
  · simp only [hl, Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hb; subst Hb
    try wp_auto
    iapply HΦ; ipureintro; trivial
  simp only [hl, Bool.not_true, Bool.false_eq_true, ite_false] at Hb
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.TypeAssumptions.ptr_unfold'Has.method_unfold]
  try wp_auto
  wp_apply wp_Has lll ll g.Term' $$ [Hll]
  · iexact Hll
  rw [hterm]
  cases hh : ll.has f.term
  · simp only [hh, Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hb; subst Hb
    try wp_auto
    iapply HΦ; ipureintro; trivial
  simp only [hh, Bool.not_true, Bool.false_eq_true, ite_false] at Hb
  obtain ⟨l, hlg, Hb⟩ := bind_ok Hb
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.TypeAssumptions.ptr_unfold'Get.method_unfold]
  try wp_auto
  wp_apply wp_Get lll ll g.Term' l $$ [Hll] as %lsl #Hl
  · iframe Hll; ipureintro; rw [hterm]; exact hlg
  ihave %Hlsl := logRO_len _ _ $$ Hl
  try wp_auto
  have hpk : sint.Z (g.PrevLogIndex' + g.Entries'.len) = f.prevLogIndex + f.entries.length := by
    rw [sint_add (by rw [hpli, Hesl]; unfold bigOk at Hp; omega) (by rw [hpli, Hesl]; unfold bigOk at Hp; omega), hpli, Hesl]
  rw [hpk, Hlsl]
  by_cases h1 : f.prevLogIndex + f.entries.length ≤ l.length
  case neg =>
    rw [decide_eq_false h1]
    simp only [h1, decide_false, Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hb; subst Hb
    try wp_auto
    iapply HΦ; ipureintro; trivial
  rw [decide_eq_true h1]
  simp only [h1, decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at Hb
  try wp_auto
  wp_apply wp_TermAt lsl l g.PrevLogIndex' $$ [Hl] as %r %Hr
  · iexact Hl
  try wp_auto
  rw [decide_w64_eq, hplt, Hr, hpli]
  by_cases h2 : f.prevLogTerm = termAt l f.prevLogIndex
  case neg =>
    rw [decide_eq_false h2]
    simp only [h2, bne_iff_ne, ne_eq, not_false_eq_true, ite_true, pure_ok, Except.ok.injEq] at Hb
    subst Hb
    try wp_auto
    iapply HΦ; ipureintro; trivial
  rw [decide_eq_true h2]
  simp only [h2, bne_self_eq_false, Bool.false_eq_true, ite_false] at Hb
  obtain ⟨sub, hsub, Hb⟩ := bind_ok Hb
  obtain ⟨eq, heq, Hb⟩ := bind_ok Hb
  try wp_auto
  have hp1 : sint.Z (g.PrevLogIndex' + W64 1) = f.prevLogIndex + 1 := by
    rw [sint_add (by rw [hpli, sint_one]; unfold bigOk at Hp; omega) (by rw [hpli, sint_one]; unfold bigOk at Hp; omega), hpli, sint_one]
  wp_apply wp_SubSeq lsl l (g.PrevLogIndex' + W64 1) (g.PrevLogIndex' + g.Entries'.len) sub $$ [Hl] as %subl #Hsub
  · iframe Hl; ipureintro; rw [hp1, hpk]; exact hsub
  try wp_auto
  wp_apply wp_EntriesEqual g.Entries' f.entries subl sub eq $$ [Hes Hsub]
  · iframe Hes Hsub; ipureintro; exact heq
  cases eq
  · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hb
    subst Hb
    try wp_auto
    iapply HΦ; ipureintro; trivial
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Hb
  try wp_auto
  obtain ⟨x, hx, ht, hf⟩ := orM_ok Hb
  simp only [pure_ok, Except.ok.injEq] at hx
  subst hx
  rw [decide_w64_eq, hcmt, sint_zero]
  by_cases hc0 : f.commit = 0
  · rw [decide_eq_true hc0]
    rw [ht (by simp [hc0])]
    try wp_auto
    iapply HΦ; ipureintro; trivial
  rw [decide_eq_false hc0]
  try wp_auto
  wp_apply wp_RecordedIn chl ch tll tl lsl l g.Commit' g.Term' b $$ [Hch Htl Hl]
  · iframe Hch Htl Hl; ipureintro; rw [hcmt, hterm]; exact hf (by simp [hc0])
  try wp_auto
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
