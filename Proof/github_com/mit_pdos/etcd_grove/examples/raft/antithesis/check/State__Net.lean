/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the proof of `State.Net` (B 478-494).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Net
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setPre
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__term
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__vote
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__commit
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__entries
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__first
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Vote
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EntriesEqual
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

theorem State.Net.wp_proof
    (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_setPre : setPre.spec (GF := GF) (hG := hG))
    (wp_term : Event.term.spec (GF := GF) (hG := hG))
    (wp_vote : Event.vote.spec (GF := GF) (hG := hG))
    (wp_commit : Event.commit.spec (GF := GF) (hG := hG))
    (wp_entries : Event.entries.spec (GF := GF) (hG := hG))
    (wp_first : Event.first.spec (GF := GF) (hG := hG))
    (wp_Vote : State.Vote.spec (GF := GF) (hG := hG))
    (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG))
    (wp_EntriesEqual : EntriesEqual.spec (GF := GF) (hG := hG)) :
    State.Net.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp

  obtain ⟨bb, EE, HW, HNO, -, hbb, -⟩ := HBd
  unfold numBound Event.weight at hbb
  unfold State.net at Ho
  icases undoRO_at g.Undo' s.undo n ⟨Hn, by rw [HWf.len_undo]; exact Hlt⟩ $$ HUndo with ⟨%u, #Hua, #Hu⟩
  icases intsRO_at g.CurrentTerm' s.currentTerm n ⟨Hn, by rw [HWf.len_currentTerm]; exact Hlt⟩ $$ HCurrentTerm with ⟨%ct, #Hcta, %Hct⟩
  icases intsRO_at g.CommitIndex' s.commitIndex n ⟨Hn, by rw [HWf.len_commitIndex]; exact Hlt⟩ $$ HCommitIndex with ⟨%ci, #Hcia, %Hci⟩
  icases logsRO_at g.Log' s.log n ⟨Hn, by rw [HWf.len_log]; exact Hlt⟩ $$ HLog with ⟨%lg, #Hlga, #Hlg⟩
  ihave %Hlgl := logRO_len _ _ $$ Hlg
  wp_auto
  wp_apply wp_load_at _ _ u Hn $$ [Hua]
  · iexact Hua
  cases hu : s.undo[sint.nat n]! with
  | none =>
    rw [hu] at Ho
    simp only [pure_ok, Except.ok.injEq] at Ho
    subst Ho
    iunfold preRO at Hu
    icases Hu with %Hnull
    subst Hnull
    wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  | some pu =>
  rw [hu] at Ho
  dsimp only at Ho
  iunfold preRO at Hu
  icases Hu with ⟨%gp, #Hgp, %Hpf, #Hsuf, #Hms, #Hvs, #Hacks⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgp
  ihave #Hgp' := Hgp
  iStructNamed Hgp'
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_apply wp_load_at _ _ u Hn $$ [Hua]
  · iexact Hua
  try wp_auto
  -- `ev.term() == s.CurrentTerm[n] && ev.vote() == s.Vote(n) && ev.commit() == s.CommitIndex[n]`
  obtain ⟨c, hc, Ho⟩ := bind_ok Ho
  obtain ⟨x1, hx1, ht1, hf1⟩ := andM_ok hc
  obtain ⟨y1, hy1, rfl⟩ := fieldEq_ok hx1
  wp_apply wp_term e ev y1 $$ [He] as %u1 %Hu1
  · iframe He; ipureintro; exact hy1
  try wp_auto
  wp_apply wp_load_at _ _ ct Hn $$ [Hcta]
  · iexact Hcta
  try wp_auto
  rw [decide_w64_eq, Hu1, Hct]
  by_cases c1 : y1 = s.currentTerm[sint.nat n]!
  case neg =>
    rw [decide_eq_false c1]
    rw [hf1 (beq_of_ne' c1)] at Ho
    simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  rw [decide_eq_true c1]
  have hc2 := ht1 (beq_of_eq' c1)
  obtain ⟨x2, hx2, ht2, hf2⟩ := andM_ok hc2
  obtain ⟨y2, hy2, rfl⟩ := fieldEq_ok hx2
  try wp_auto
  wp_apply wp_vote e ev y2 $$ [He]
  · iframe He; ipureintro; exact hy2
  try wp_auto
  wp_apply wp_Vote p s n $$ [Hs]
  · iframe Hs; ipureintro; exact ⟨Hn, Hlt⟩
  try wp_auto
  by_cases c2 : y2 = s.vote (sint.nat n)
  case neg =>
    rw [decide_eq_false c2]
    rw [hf2 (beq_of_ne' c2)] at Ho
    simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  rw [decide_eq_true c2]
  have hc3 := ht2 (beq_of_eq' c2)
  obtain ⟨y3, hy3, hc3⟩ := fieldEq_ok hc3
  subst hc3
  try wp_auto
  wp_apply wp_commit e ev y3 $$ [He] as %u3 %Hu3
  · iframe He; ipureintro; exact hy3
  try wp_auto
  wp_apply wp_load_at _ _ ci Hn $$ [Hcia]
  · iexact Hcia
  try wp_auto
  rw [decide_w64_eq, Hu3, Hci]
  by_cases c3 : y3 = s.commitIndex[sint.nat n]!
  case neg =>
    rw [decide_eq_false c3]
    rw [beq_of_ne' c3] at Ho
    simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  rw [decide_eq_true c3]
  rw [beq_of_eq' c3] at Ho
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
  obtain ⟨es, hes, Ho⟩ := bind_ok Ho
  have hesz : es.length ≤ ev.size := by unfold Event.size; rw [need_ok hes]; simp; omega
  try wp_auto
  wp_apply wp_entries e ev es $$ [He] as %esl #Hes
  · iframe He; ipureintro; exact hes
  ihave %Hesl := logRO_len _ _ $$ Hes
  try wp_auto
  by_cases h0 : es.length = 0
  · have : esl.len = W64 0 := by have := Hesl; rw [h0] at this; word
    rw [this]
    simp only [h0, beq_self_eq_true, ite_true] at Ho
    try wp_auto
    rw [decide_w64_eq, Hpf.2.2.2.2.2.2.1, sint_zero]
    by_cases hl : pu.low = 0
    · rw [decide_eq_true hl]
      rw [show (pu.low != 0) = false by simp [hl]] at Ho
      simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Ho
      -- the successor: `{ u with low := 0 }`
      try wp_auto
      wp_apply wp_clone p s $$ [Hs] as %q Hq
      · iexact Hs
      ipersist nu
      ihave #Hnu : preRO nu_ptr (some { pu with low := 0 }) $$ []
      · iunfold preRO
        iexists _
        iframe nu Hsuf Hms Hvs Hacks
        ipureintro
        exact ⟨Hpf.1, Hpf.2.1, Hpf.2.2.1, Hpf.2.2.2.1, Hpf.2.2.2.2.1, Hpf.2.2.2.2.2.1, rfl, Hpf.2.2.2.2.2.2.2⟩
      try wp_auto
      wp_apply wp_setPre g.Undo' s.undo n nu_ptr _ $$ [HUndo Hnu] as %out #Hout
      · iframe HUndo Hnu; ipureintro; exact ⟨Hn, by rw [HWf.len_undo]; exact Hlt⟩
      try wp_auto
      wp_apply wp_set_undo q s out (s.undo.set (sint.nat n) (some { pu with low := 0 }))
        (by rw [List.length_set, HWf.len_undo]) $$ [Hq Hout] as Hq
      · iframe Hq Hout
      try wp_auto
      subst Ho
      iapply HΦ
      iunfold succOwn
      isplitr
      · ipureintro; rfl
      iexact Hq
    · rw [decide_eq_false hl]
      rw [show (pu.low != 0) = true by simpa using hl] at Ho
      simp only [ite_true, pure_ok, Except.ok.injEq] at Ho
      subst Ho
      try wp_auto
      iapply HΦ; iunfold succOwn; ipureintro; rfl
  have hne : esl.len ≠ W64 0 := by intro h; rw [h] at Hesl; simp at Hesl; omega
  rw [decide_eq_false hne]
  rw [show (es.length == 0) = false by simpa using h0] at Ho
  simp only [Bool.false_eq_true, ite_false] at Ho
  obtain ⟨c, hc, Ho⟩ := bind_ok Ho
  obtain ⟨x1, hx1, ht1, hf1⟩ := andM_ok hc
  obtain ⟨fi, hfi, rfl⟩ := fieldEq_ok hx1
  have hfin : numOk fi := by have := HNO.2.2.1; rw [need_ok hfi] at this; exact this
  unfold numOk numBound at hfin
  have hsz : (ev.size : Int) < 2 ^ 61 := by omega
  try wp_auto
  wp_apply wp_load_at _ _ lg Hn $$ [Hlga]
  · iexact Hlga
  try wp_auto
  wp_apply wp_first e ev fi $$ [He] as %uf %Huf
  · iframe He; ipureintro; exact hfi
  try wp_auto
  rw [decide_w64_eq, Hpf.2.2.2.2.2.2.1, Huf]
  by_cases h1 : pu.low = fi
  case neg =>
    rw [decide_eq_false h1]
    rw [hf1 (beq_of_ne' (fun h => h1 h.symm))] at Ho
    simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  rw [decide_eq_true h1]
  have hc2 := ht1 (beq_of_eq' h1.symm)
  obtain ⟨x2, hx2, ht2, hf2⟩ := andM_ok hc2
  obtain ⟨fi2, hfi2, hx2⟩ := bind_ok hx2
  rw [hfi] at hfi2; cases hfi2
  simp only [pure_ok, Except.ok.injEq] at hx2
  subst hx2
  try wp_auto
  wp_apply wp_first e ev fi $$ [He] as %uf2 %Huf2
  · iframe He; ipureintro; exact hfi
  try wp_auto
  wp_apply wp_entries e ev es $$ [He] as %esl2 #Hes2
  · iframe He; ipureintro; exact hes
  ihave %Hesl2 := logRO_len _ _ $$ Hes2
  try wp_auto
  have hsum : sint.Z (uf2 + esl2.len - W64 1) = fi + es.length - 1 := by
    have h1 : sint.Z (uf2 + esl2.len) = fi + es.length := by
      rw [sint_add (by rw [Huf2, Hesl2]; omega) (by rw [Huf2, Hesl2]; omega), Huf2, Hesl2]
    rw [sint_sub (by rw [h1, sint_one]; omega) (by rw [h1, sint_one]; omega), h1, sint_one]
  rw [decide_w64_eq, Hlgl, hsum]
  by_cases h2 : ((s.log[sint.nat n]!).length : Int) = fi + es.length - 1
  case neg =>
    rw [decide_eq_false h2]
    rw [hf2 (beq_of_ne' h2)] at Ho
    simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  rw [decide_eq_true h2]
  have hc3 := ht2 (beq_of_eq' h2)
  obtain ⟨fi3, hfi3, hc3⟩ := bind_ok hc3
  rw [hfi] at hfi3; cases hfi3
  obtain ⟨sub, hsub, hc3⟩ := bind_ok hc3
  try wp_auto
  wp_apply wp_load_at _ _ lg Hn $$ [Hlga]
  · iexact Hlga
  try wp_auto
  wp_apply wp_first e ev fi $$ [He] as %uf3 %Huf3
  · iframe He; ipureintro; exact hfi
  try wp_auto
  wp_apply wp_SubSeq lg _ uf3 lg.len sub $$ [Hlg] as %subl #Hsub
  · iframe Hlg; ipureintro; rw [Huf3, Hlgl]; exact hsub
  try wp_auto
  wp_apply wp_entries e ev es $$ [He] as %esl3 #Hes3
  · iframe He; ipureintro; exact hes
  try wp_auto
  wp_apply wp_EntriesEqual subl sub esl3 es c $$ [Hsub Hes3]
  · iframe Hsub Hes3; ipureintro; exact hc3
  cases c
  · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Ho
  -- the successor: `{ u with low := 0 }`
  try wp_auto
  wp_apply wp_clone p s $$ [Hs] as %q Hq
  · iexact Hs
  ipersist nu
  ihave #Hnu : preRO nu_ptr (some { pu with low := 0 }) $$ []
  · iunfold preRO
    iexists _
    iframe nu Hsuf Hms Hvs Hacks
    ipureintro
    exact ⟨Hpf.1, Hpf.2.1, Hpf.2.2.1, Hpf.2.2.2.1, Hpf.2.2.2.2.1, Hpf.2.2.2.2.2.1, rfl, Hpf.2.2.2.2.2.2.2⟩
  try wp_auto
  wp_apply wp_setPre g.Undo' s.undo n nu_ptr _ $$ [HUndo Hnu] as %out #Hout
  · iframe HUndo Hnu; ipureintro; exact ⟨Hn, by rw [HWf.len_undo]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_undo q s out (s.undo.set (sint.nat n) (some { pu with low := 0 }))
    (by rw [List.length_set, HWf.len_undo]) $$ [Hq Hout] as Hq
  · iframe Hq Hout
  try wp_auto
  subst Ho
  iapply HΦ
  iunfold succOwn
  isplitr
  · ipureintro; rfl
  iexact Hq

end proof

end AntCheck
end EtcdGrove
end Perennial
