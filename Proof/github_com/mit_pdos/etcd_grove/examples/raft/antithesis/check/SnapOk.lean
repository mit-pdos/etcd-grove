/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `SnapOk` (B 80-83).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SnapOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__typ
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__term
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__index
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__logTerm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__Has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermAt
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

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

theorem SnapOk.wp_proof (wp_typ : Msg.typ.spec (GF := GF) (hG := hG))
    (wp_term : Msg.term.spec (GF := GF) (hG := hG))
    (wp_index : Msg.index.spec (GF := GF) (hG := hG))
    (wp_logTerm : Msg.logTerm.spec (GF := GF) (hG := hG))
    (wp_Has : TermLogs.Has.spec (GF := GF) (hG := hG))
    (wp_Get : TermLogs.Get.spec (GF := GF) (hG := hG))
    (wp_TermAt : TermAt.spec (GF := GF) (hG := hG)) :
    SnapOk.spec (GF := GF) (hG := hG) := by
  intro sl ll g m b
  wp_start as ⟨#Hll, #Hm, %Hb⟩
  unfold snapOk at Hb
  cases h1 : m.typ with
  | error _ => simp [h1] at Hb; cases Hb
  | ok ty =>
  simp only [h1] at Hb
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'typ.method_unfold]
  try wp_auto
  wp_apply wp_typ g m ty $$ [Hm]
  · iframe Hm; ipureintro; exact h1
  try wp_auto
  by_cases hty : ty = go!"snap"
  case neg =>
    have hb : b = true := by simp [hty, bind, Except.bind, Pure.pure, Except.pure] at Hb; exact Hb
    subst hb
    wp_if_destruct
    · exact absurd rfl hty
    · try wp_auto
      iapply HΦ; ipureintro; trivial
  subst hty
  simp only [decide_true, Bool.not_true] 
  try wp_auto
  simp at Hb
  cases h2 : m.term_ with
  | error _ => simp [h2] at Hb; cases Hb
  | ok t =>
  simp only [h2] at Hb
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
  try wp_auto
  wp_apply wp_term g m t $$ [Hm] as %ut %Hut
  · iframe Hm; ipureintro; exact h2
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.TypeAssumptions.ptr_unfold'Has.method_unfold]
  try wp_auto
  wp_apply wp_Has sl ll ut $$ [Hll]
  · iexact Hll
  rw [Hut]
  cases hh : ll.has t
  · simp [hh, bind, Except.bind, Pure.pure, Except.pure] at Hb
    subst Hb
    try wp_auto
    iapply HΦ; ipureintro; trivial
  simp only [hh, bind, Except.bind, Pure.pure, Except.pure] at Hb
  cases h3 : m.index_ with
  | error _ => simp [h3] at Hb
  | ok k =>
  cases h4 : ll.get t with
  | error _ => simp [h3, h4] at Hb
  | ok l =>
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'index.method_unfold]
  try wp_auto
  wp_apply wp_index g m k $$ [Hm] as %uk %Huk
  · iframe Hm; ipureintro; exact h3
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
  try wp_auto
  wp_apply wp_term g m t $$ [Hm] as %ut' %Hut'
  · iframe Hm; ipureintro; exact h2
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.TypeAssumptions.ptr_unfold'Get.method_unfold]
  try wp_auto
  wp_apply wp_Get sl ll ut' l $$ [Hll] as %lsl #Hl
  · iframe Hll; ipureintro; rw [Hut']; exact h4
  try wp_auto
  ihave %Hlen := logRO_len _ _ $$ Hl
  simp only [h3, h4, ite_true, Bool.true_eq_false, ite_false] at Hb
  wp_if_destruct
  rotate_left
  · have hk : (l.length : Int) < k := by omega
    simp [hk] at Hb; subst Hb
    try wp_auto
    iapply HΦ; ipureintro; trivial
  have hk : ¬ ((l.length : Int) < k) := by omega
  simp only [hk, ite_false] at Hb
  cases h5 : m.logTerm_ with
  | error _ => simp [h5, Functor.map, Except.map] at Hb
  | ok lt =>
  simp only [h5] at Hb
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
  try wp_auto
  wp_apply wp_term g m t $$ [Hm] as %ut2 %Hut2
  · iframe Hm; ipureintro; exact h2
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.TypeAssumptions.ptr_unfold'Get.method_unfold]
  try wp_auto
  wp_apply wp_Get sl ll ut2 l $$ [Hll] as %lsl2 #Hl2
  · iframe Hll; ipureintro; rw [Hut2]; exact h4
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'index.method_unfold]
  try wp_auto
  wp_apply wp_index g m k $$ [Hm] as %uk2 %Huk2
  · iframe Hm; ipureintro; exact h3
  try wp_auto
  wp_apply wp_TermAt lsl2 l uk2 $$ [Hl2] as %r %Hr
  · iexact Hl2
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'logTerm.method_unfold]
  try wp_auto
  wp_apply wp_logTerm g m lt $$ [Hm] as %ul %Hul
  · iframe Hm; ipureintro; exact h5
  try wp_auto
  simp [Functor.map, Except.map] at Hb
  rw [Huk2] at Hr
  have key : (r = ul) ↔ termAt l k = lt :=
    ⟨fun h => by rw [← Hr, ← Hul, h], fun h => by
      have : sint.Z r = sint.Z ul := by rw [Hr, Hul, h]
      word⟩
  have hd : decide (r = ul) = b := by rw [← Hb]; by_cases hx : termAt l k = lt <;> simp [key, hx]
  rw [hd]
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
