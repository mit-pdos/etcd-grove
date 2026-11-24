/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the proof of `State.Flush` (B 474-478).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Flush
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__OnDisk
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__more
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

theorem State.Flush.wp_proof (onDisk_keeps : W6Laws.OnDiskKeeps)
    (wp_OnDisk : State.OnDisk.spec (GF := GF) (hG := hG))
    (wp_more : Event.more.spec (GF := GF) (hG := hG))
    (wp_setQueue : setQueue.spec (GF := GF) (hG := hG)) :
    State.Flush.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  obtain ⟨bb, EE, HW, HNO, -, hbb, -⟩ := HBd
  unfold numBound Event.weight at hbb
  unfold State.flush at Ho
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
  obtain ⟨mv, hmv, Ho⟩ := bind_ok Ho
  obtain ⟨o', hod, Ho⟩ := bind_ok Ho
  try wp_auto
  wp_apply wp_load_at _ _ qv Hn $$ [Hqa]
  · iexact Hqa
  try wp_auto
  ihave #Hq' := Hq
  iunfold qitemsRO at Hq'
  icases Hq' with ⟨%items, #Hitems, #Hb⟩
  icases sliceRO_at (fun g x => qitemRO (GF := GF) g x) qv items (q :: rest) (W64 0) ⟨by decide, by simp⟩ $$ [Hitems Hb] with ⟨%gq, #Hgqa, #Hgq⟩
  · iframe Hitems Hb
  wp_apply wp_load_at _ _ gq (by decide) $$ [Hgqa]
  · iexact Hgqa
  try wp_auto
  wp_apply wp_more e ev mv $$ [He] as %um %Hum
  · iframe He; ipureintro; exact hmv
  try wp_auto
  rw [decide_w64_eq, Hum, show sint.Z (W64 1) = 1 from rfl, decide_eq_beq']
  have hbd : OnDisk.Bounded (OnDisk.mk s (sint.nat n) q (mv == 1) s.role s.leaders s.ledLog s.chain s.termLen s.viol) :=
    ⟨bb, EE, by unfold numBound; push_cast at hbb ⊢; omega, W6Laws.onDisk_within_self _ HW hq⟩
  have h0 : (q :: rest)[sint.nat (W64 0)]! = q := by rw [show sint.nat (W64 0) = 0 from rfl]; rfl
  rw [h0]
  wp_apply wp_OnDisk p s n gq q (mv == 1) g.Role' s.role g.Leaders' s.leaders g.LedLog' s.ledLog g.Chain' s.chain
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
