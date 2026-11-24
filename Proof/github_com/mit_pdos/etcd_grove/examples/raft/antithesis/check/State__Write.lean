/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the proof of `State.Write` (B 462-470).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Write
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__OnDisk
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__term
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__vote
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__commit
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__first
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__entries
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EntriesEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setQueue
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.W6Laws

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

set_option hygiene false in
/-- `Write`'s report differs from the queued one: `ok = false`. -/
local macro "wdiffer" : tactic => `(tactic| (
  (have hs := hf rfl); subst hs;
  simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho; subst Ho;
  (try wp_auto); iapply HΦ; iunfold succOwn; ipureintro; rfl))

theorem State.Write.wp_proof (onDisk_keeps : W6Laws.OnDiskKeeps)
    (wp_OnDisk : State.OnDisk.spec (GF := GF) (hG := hG))
    (wp_term : Event.term.spec (GF := GF) (hG := hG))
    (wp_vote : Event.vote.spec (GF := GF) (hG := hG))
    (wp_commit : Event.commit.spec (GF := GF) (hG := hG))
    (wp_first : Event.first.spec (GF := GF) (hG := hG))
    (wp_entries : Event.entries.spec (GF := GF) (hG := hG))
    (wp_EntriesEqual : EntriesEqual.spec (GF := GF) (hG := hG))
    (wp_setQueue : setQueue.spec (GF := GF) (hG := hG)) :
    State.Write.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  obtain ⟨bb, EE, HW, HNO, -, hbb, -⟩ := HBd
  unfold numBound Event.weight at hbb
  unfold State.write at Ho
  icases queueRO_at g.Queue' s.queue n ⟨Hn, by rw [HWf.len_queue]; exact Hlt⟩ $$ HQueue with ⟨%qv, #Hqa, #Hq⟩
  ihave %Hql := qitemsRO_len _ _ $$ Hq
  wp_auto
  wp_apply wp_load_at _ _ qv Hn $$ [Hqa]
  · iexact Hqa
  try wp_auto
  cases hq : s.queue[sint.nat n]! with
  | nil =>
    rw [hq] at Ho Hql
    simp only [pure_ok, Except.ok.injEq] at Ho
    subst Ho
    have : qv.len = W64 0 := by simp at Hql; word
    rw [this]
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  | cons q rest =>
  rw [hq] at Ho Hql
  have hne : qv.len ≠ W64 0 := by intro h; rw [h] at Hql; simp at Hql; omega
  rw [decide_eq_false hne]
  dsimp only at Ho
  obtain ⟨same, hsame, Ho⟩ := bind_ok Ho
  try wp_auto
  wp_apply wp_load_at _ _ qv Hn $$ [Hqa]
  · iexact Hqa
  try wp_auto
  ihave #Hq' := Hq
  iunfold qitemsRO at Hq'
  icases Hq' with ⟨%items, #Hitems, #Hb⟩
  icases sliceRO_at (fun g x => qitemRO (GF := GF) g x) qv items (q :: rest) (W64 0) ⟨by decide, by simp⟩ $$ [Hitems Hb] with ⟨%gq, #Hgqa, #Hgq⟩
  · iframe Hitems Hb
  have h0 : (q :: rest)[sint.nat (W64 0)]! = q := by rw [show sint.nat (W64 0) = 0 from rfl]; rfl
  rw [h0]
  wp_apply wp_load_at _ _ gq (by decide) $$ [Hgqa]
  · iexact Hgqa
  try wp_auto
  ihave #Hgq' := Hgq
  iunfold qitemRO at Hgq'
  icases Hgq' with ⟨#Hwe, #Hwm⟩
  obtain ⟨x, hx, ht, hf⟩ := andM_ok hsame
  obtain ⟨a1, ha1, hx⟩ := bind_ok hx
  obtain ⟨a2, ha2, hx⟩ := bind_ok hx
  simp only [pure_ok, Except.ok.injEq] at hx
  wp_apply wp_term e ev a1 $$ [He] as %u1 %Hu1
  · iframe He; ipureintro; exact ha1
  try wp_auto
  wp_apply wp_term gq.Ev' q.ev a2 $$ [Hwe] as %u2 %Hu2
  · iframe Hwe; ipureintro; exact ha2
  try wp_auto
  rw [decide_w64_eq, Hu1, Hu2, decide_eq_beq', hx]
  cases x
  · wdiffer
  have hs := ht rfl
  try wp_auto
  obtain ⟨x, hx, ht, hf⟩ := andM_ok hs
  obtain ⟨a1, ha1, hx⟩ := bind_ok hx
  obtain ⟨a2, ha2, hx⟩ := bind_ok hx
  simp only [pure_ok, Except.ok.injEq] at hx
  wp_apply wp_vote e ev a1 $$ [He] 
  · iframe He; ipureintro; exact ha1
  try wp_auto
  wp_apply wp_vote gq.Ev' q.ev a2 $$ [Hwe] 
  · iframe Hwe; ipureintro; exact ha2
  try wp_auto
  rw [decide_eq_beq', hx]
  cases x
  · wdiffer
  have hs := ht rfl
  try wp_auto
  obtain ⟨x, hx, ht, hf⟩ := andM_ok hs
  obtain ⟨a1, ha1, hx⟩ := bind_ok hx
  obtain ⟨a2, ha2, hx⟩ := bind_ok hx
  simp only [pure_ok, Except.ok.injEq] at hx
  wp_apply wp_commit e ev a1 $$ [He] as %u1 %Hu1
  · iframe He; ipureintro; exact ha1
  try wp_auto
  wp_apply wp_commit gq.Ev' q.ev a2 $$ [Hwe] as %u2 %Hu2
  · iframe Hwe; ipureintro; exact ha2
  try wp_auto
  rw [decide_w64_eq, Hu1, Hu2, decide_eq_beq', hx]
  cases x
  · wdiffer
  have hs := ht rfl
  try wp_auto
  obtain ⟨x, hx, ht, hf⟩ := andM_ok hs
  obtain ⟨a1, ha1, hx⟩ := bind_ok hx
  obtain ⟨a2, ha2, hx⟩ := bind_ok hx
  simp only [pure_ok, Except.ok.injEq] at hx
  wp_apply wp_first e ev a1 $$ [He] as %u1 %Hu1
  · iframe He; ipureintro; exact ha1
  try wp_auto
  wp_apply wp_first gq.Ev' q.ev a2 $$ [Hwe] as %u2 %Hu2
  · iframe Hwe; ipureintro; exact ha2
  try wp_auto
  rw [decide_w64_eq, Hu1, Hu2, decide_eq_beq', hx]
  cases x
  · wdiffer
  have hs := ht rfl
  try wp_auto
  obtain ⟨a1, ha1, hs⟩ := bind_ok hs
  obtain ⟨a2, ha2, hs⟩ := bind_ok hs
  wp_apply wp_entries e ev a1 $$ [He] as %el1 #Hel1
  · iframe He; ipureintro; exact ha1
  try wp_auto
  wp_apply wp_entries gq.Ev' q.ev a2 $$ [Hwe] as %el2 #Hel2
  · iframe Hwe; ipureintro; exact ha2
  try wp_auto
  wp_apply wp_EntriesEqual el1 a1 el2 a2 same $$ [Hel1 Hel2]
  · iframe Hel1 Hel2; ipureintro; exact hs
  cases same
  · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho; subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
  obtain ⟨o', hod, Ho⟩ := bind_ok Ho
  try wp_auto
  have hbd : OnDisk.Bounded (OnDisk.mk s (sint.nat n) q false s.role s.leaders s.ledLog s.chain s.termLen s.viol) :=
    ⟨bb, EE, by unfold numBound; push_cast at hbb ⊢; omega, W6Laws.onDisk_within_self _ HW hq⟩
  wp_apply wp_OnDisk p s n gq q false g.Role' s.role g.Leaders' s.leaders g.LedLog' s.ledLog g.Chain' s.chain
    g.TermLen' s.termLen g.Viol' s.viol o' $$ [Hs Hgq HRole HLeaders HLedLog HChain HTermLen HViol] as %q' %ok Hsucc
  · iframe Hs Hgq HRole HLeaders HLedLog HChain HTermLen HViol
    ipureintro; exact ⟨Hn, Hlt, HWf.len_role, hbd, hod⟩
  try wp_auto
  cases o' with
  | none =>
    simp only [pure_ok, Except.ok.injEq] at Ho
    subst Ho
    iunfold succOwn at Hsucc
    icases Hsucc with %Hok
    subst Hok
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  | some ns =>
  simp only [pure_ok, Except.ok.injEq] at Ho
  subst Ho
  iunfold succOwn at Hsucc
  icases Hsucc with ⟨%Hok, Hns⟩
  subst Hok
  obtain ⟨hcfg, -, -, -⟩ := onDisk_keeps _ _ _ _ _ _ _ _ _ _ _ hod
  try wp_auto
  wp_apply wp_load_at _ _ qv Hn $$ [Hqa]
  · iexact Hqa
  try wp_auto
  have hql1 : (1 : Int) ≤ sint.Z qv.len := by rw [Hql]; simp; omega
  ihave %Hcap := ownSlice_wf $$ Hitems
  have hcapT := eq_true (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z qv.len ∧ sint.Z qv.len ≤ sint.Z qv.cap by
    rw [sint_one]; omega)
  rw [ite_eq_left_of_eq_true _ _ hcapT]
  ihave #Hsub := qitemsRO_subslice qv (q :: rest) (W64 1) qv.len ⟨by decide, by rw [sint_one]; omega, Int.le_refl _⟩ $$ Hq
  have hsub : subslice (sint.nat (W64 1)) (sint.nat qv.len) (q :: rest) = rest := by
    rw [show sint.nat (W64 1) = 1 from rfl, show sint.nat qv.len = (q :: rest).length by
      have := sint_nat_cast (k := qv.len) (by omega); omega]
    exact W6Laws.subslice_tail q rest
  rw [hsub]
  try wp_auto
  wp_apply wp_setQueue g.Queue' s.queue n _ rest $$ [HQueue Hsub] as %out #Hout
  · iframe HQueue Hsub; ipureintro; exact ⟨Hn, by rw [HWf.len_queue]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_queue q' ns out (s.queue.set (sint.nat n) rest)
    (by rw [List.length_set, HWf.len_queue, hcfg]) $$ [Hns Hout] as Hns
  · iframe Hns Hout
  try wp_auto
  iapply HΦ
  iunfold succOwn
  isplitr
  · ipureintro; rfl
  iexact Hns

end proof

end AntCheck
end EtcdGrove
end Perennial
