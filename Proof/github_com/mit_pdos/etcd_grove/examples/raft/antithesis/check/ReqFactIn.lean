/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `ReqFactIn` (B 85-91).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ReqFactIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__typ
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__term
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__index
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__from
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__to
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__Has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ToAppendFact
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0Laws

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

theorem reqFactIn_snap {ll : TermFn (List Entry)} {m : Msg} {f : AppendFact} {t : Int}
    (h1 : m.typ = .ok go!"snap") (h2 : m.term_ = .ok t) (Hf : reqFactIn ll m = .ok f) :
    ∃ src dst k es, m.from_ = .ok src ∧ m.to_ = .ok dst ∧ m.index_ = .ok k ∧
      f = { src, dst, term := t, prevLogIndex := 0, prevLogTerm := 0, entries := es, commit := k } ∧
      (if ll.has t then ∃ l, ll.get t = .ok l ∧ subSeq l 1 k = .ok es else es = []) := by
  unfold reqFactIn at Hf
  simp only [h1, h2, bind, Except.bind, beq_self_eq_true, ite_true] at Hf
  cases h3 : m.from_ <;> cases h4 : m.to_ <;> cases h5 : m.index_ <;> cases hh : ll.has t <;>
    cases h6 : ll.get t <;> simp only [h3, h4, h5, hh, h6, Bool.false_eq_true, ite_true, ite_false,
      Pure.pure, Except.pure, reduceCtorEq] at Hf
  all_goals first
    | (split at Hf <;> simp_all)
    | (cases Hf; exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, by simp⟩)

theorem ReqFactIn.wp_proof (wp_typ : Msg.typ.spec (GF := GF) (hG := hG))
    (wp_term : Msg.term.spec (GF := GF) (hG := hG))
    (wp_index : Msg.index.spec (GF := GF) (hG := hG))
    (wp_from : Msg.«from».spec (GF := GF) (hG := hG))
    (wp_to : Msg.to.spec (GF := GF) (hG := hG))
    (wp_Has : TermLogs.Has.spec (GF := GF) (hG := hG))
    (wp_Get : TermLogs.Get.spec (GF := GF) (hG := hG))
    (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG))
    (wp_ToAppendFact : ToAppendFact.spec (GF := GF) (hG := hG)) :
    ReqFactIn.spec (GF := GF) (hG := hG) := by
  intro sl ll g m f
  wp_start as ⟨#Hll, #Hm, %Hf⟩
  have Hf0 := Hf
  unfold reqFactIn at Hf
  cases h1 : m.typ with
  | error _ => simp [h1, bind, Except.bind] at Hf
  | ok ty =>
  simp only [h1, bind, Except.bind] at Hf
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_typ_unfold.method_unfold]
  try wp_auto
  wp_apply wp_typ g m ty $$ [Hm]
  · iframe Hm; ipureintro; exact h1
  try wp_auto
  by_cases hty : ty = go!"snap"
  case neg =>
    simp only [hty, beq_iff_eq, ite_false] at Hf
    wp_if_destruct
    · exact absurd rfl hty
    try wp_auto
    wp_apply wp_ToAppendFact g m f $$ [Hm] as %u #Hu
    · iframe Hm; ipureintro; exact Hf
    try wp_auto
    iapply HΦ; iexact Hu
  subst hty
  simp only [beq_self_eq_true, ite_true] at Hf
  try wp_auto
  cases h2 : m.term_ with
  | error _ => simp [h2] at Hf
  | ok t =>
  simp only [h2] at Hf
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_term_unfold.method_unfold]
  try wp_auto
  wp_apply wp_term g m t $$ [Hm] as %ut %Hut
  · iframe Hm; ipureintro; exact h2
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.TypeAssumptions.ptr_Has_unfold.method_unfold]
  try wp_auto
  wp_apply wp_Has sl ll ut $$ [Hll]
  · iexact Hll
  rw [Hut]
  obtain ⟨src, dst, k, es, h3, h4, h5, rfl, hes⟩ := reqFactIn_snap h1 h2 Hf0
  clear Hf Hf0
  cases hh : ll.has t
  · simp only [hh, Bool.false_eq_true, ite_false] at hes
    subst hes
    ihave #Hes := Init0_logNil (GF := GF)
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_from_unfold.method_unfold]
    try wp_auto
    wp_apply wp_from g m src $$ [Hm]
    · iframe Hm; ipureintro; exact h3
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_to_unfold.method_unfold]
    try wp_auto
    wp_apply wp_to g m dst $$ [Hm]
    · iframe Hm; ipureintro; exact h4
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_term_unfold.method_unfold]
    try wp_auto
    wp_apply wp_term g m t $$ [Hm] as %ut3 %Hut3
    · iframe Hm; ipureintro; exact h2
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_index_unfold.method_unfold]
    try wp_auto
    wp_apply wp_index g m k $$ [Hm] as %uk3 %Huk3
    · iframe Hm; ipureintro; exact h5
    try wp_auto
    iapply HΦ
    iunfold appendFactRO
    iframe Hes
    ipureintro
    exact ⟨rfl, rfl, Hut3, rfl, rfl, Huk3⟩
  · obtain ⟨l, h6, h7⟩ : ∃ l, ll.get t = .ok l ∧ subSeq l 1 k = .ok es := by simpa [hh] using hes
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_term_unfold.method_unfold]
    try wp_auto
    wp_apply wp_term g m t $$ [Hm] as %ut2 %Hut2
    · iframe Hm; ipureintro; exact h2
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.TypeAssumptions.ptr_Get_unfold.method_unfold]
    try wp_auto
    wp_apply wp_Get sl ll ut2 l $$ [Hll] as %lsl #Hl
    · iframe Hll; ipureintro; rw [Hut2]; exact h6
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_index_unfold.method_unfold]
    try wp_auto
    wp_apply wp_index g m k $$ [Hm] as %uk2 %Huk2
    · iframe Hm; ipureintro; exact h5
    try wp_auto
    wp_apply wp_SubSeq lsl l (W64 1) uk2 es $$ [Hl] as %esl #Hes
    · iframe Hl; ipureintro; rw [Huk2]; exact h7
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_from_unfold.method_unfold]
    try wp_auto
    wp_apply wp_from g m src $$ [Hm]
    · iframe Hm; ipureintro; exact h3
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_to_unfold.method_unfold]
    try wp_auto
    wp_apply wp_to g m dst $$ [Hm]
    · iframe Hm; ipureintro; exact h4
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_term_unfold.method_unfold]
    try wp_auto
    wp_apply wp_term g m t $$ [Hm] as %ut3 %Hut3
    · iframe Hm; ipureintro; exact h2
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_index_unfold.method_unfold]
    try wp_auto
    wp_apply wp_index g m k $$ [Hm] as %uk3 %Huk3
    · iframe Hm; ipureintro; exact h5
    try wp_auto
    iapply HΦ
    iunfold appendFactRO
    iframe Hes
    ipureintro
    exact ⟨rfl, rfl, Hut3, rfl, rfl, Huk3⟩

end proof

end AntCheck
end EtcdGrove
end Perennial
