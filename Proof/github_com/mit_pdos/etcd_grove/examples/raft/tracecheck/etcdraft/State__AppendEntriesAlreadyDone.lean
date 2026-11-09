/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__AppendEntriesAlreadyDone`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__AppendEntriesAlreadyDone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__commitTo
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__HasNoConflict
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__reply

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

set_option hygiene false in
local macro "ad_send" stt:term : tactic => `(tactic| (
    irename «$a0» => Hmq
    ipersist Hmq
    ihave #Hnil := logRO_nil (GF := GF)
    ihave #Hresp : msgRO (GF := GF) «$a0_ptr» { type := .appendEntriesResponse, subtype := m.subtype, term := (st.s (uint.nat i)).currentTerm, success := true, matchIndex := (if (Bool.or (m.subtype == "heartbeat") (decide (sint.Z index > (st.s (uint.nat i)).commitIndex))) then m.prevLogIndex + m.entries.length else (st.s (uint.nat i)).commitIndex), source := uint.nat i, dest := uint.nat j } $$ []
    · iunfold msgRO
      iexists _
      iframe Hmq Hnil
      ipureintro
      refine ⟨rfl, Hv.2.1, Hf.1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
      simp only [hpn, Hf.2.2.2.2.1]
      simp [hsb, hA]; try (intro h; omega)
    wp_apply wp_reply t $stt _ _ _ q m $$ [Ht Hresp Hmsg] as Ht
    · iframe Ht Hresp Hmsg; ipureintro; exact ⟨Hpok.1, Hpok.count_lt _, Hmok.1⟩
    try wp_auto
    imodintro
    iapply HΦ
    rw [hst]
    iexists _; iexact Ht))

-- After the commit: the match index, the response sent, the request discarded (hygiene off).
set_option hygiene false in
local macro "ad_fin" stt:term : tactic => `(tactic| (
    try wp_auto
    rw [decide_strRel Hv.2.1 strRel_heartbeat]
    by_cases hsb : m.subtype = "heartbeat"
    · rw [decide_eq_true hsb]
      wp_auto
      ad_send $stt
    · rw [decide_eq_false hsb]
      wp_auto
      rw [hcmp]
      wp_auto
      ad_send $stt))

-- Enabled with `index > commitIndex`: the clone, committed to the request's end (hygiene off).
set_option hygiene false in
local macro "ad_tailB" : tactic => `(tactic| (
    try wp_auto
    wp_apply wp_clone p st $$ [Hst] as %t Ht
    · iexact Hst
    try wp_auto
    rw [decide_eq_false (show ¬ sint.Z index ≤ sint.Z gs.CommitIndex' by rw [Hf.2.2.2.2.1]; exact hA)]
    wp_auto
    wp_apply wp_min_int
    try wp_auto
    wp_apply wp_commitTo t st [] i (if sint.Z gm.CommitIndex' < sint.Z (gm.PrevLogIndex' + gm.Entries'.len) then gm.CommitIndex' else gm.PrevLogIndex' + gm.Entries'.len) $$ [Ht] as Ht
    · iframe Ht; ipureintro; exact Hi
    have hst : st.appendEntriesAlreadyDone (uint.nat i) (uint.nat j) (sint.Z index) m = some ((st.commitTo (uint.nat i) (sint.Z (if sint.Z gm.CommitIndex' < sint.Z (gm.PrevLogIndex' + gm.Entries'.len) then gm.CommitIndex' else gm.PrevLogIndex' + gm.Entries'.len))).reply { type := .appendEntriesResponse, subtype := m.subtype, term := (st.s (uint.nat i)).currentTerm, success := true, matchIndex := (if (Bool.or (m.subtype == "heartbeat") (decide (sint.Z index > (st.s (uint.nat i)).commitIndex))) then m.prevLogIndex + m.entries.length else (st.s (uint.nat i)).commitIndex), source := uint.nat i, dest := uint.nat j } m) := by
      rw [sint_min, hcm, hpn]
      unfold State.appendEntriesAlreadyDone; simp [hA, hen]
    ad_fin (st.commitTo (uint.nat i) (sint.Z (if sint.Z gm.CommitIndex' < sint.Z (gm.PrevLogIndex' + gm.Entries'.len) then gm.CommitIndex' else gm.PrevLogIndex' + gm.Entries'.len)))))

theorem State.AppendEntriesAlreadyDone.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_commitTo : State.commitTo.spec (GF := GF) (hG := hG))
    (wp_HasNoConflict : State.HasNoConflict.spec (GF := GF) (hG := hG))
    (wp_reply : State.reply.spec (GF := GF) (hG := hG)) :
    State.AppendEntriesAlreadyDone.spec (GF := GF) (hG := hG) := by
  intro p st i j index q m
  wp_start as ⟨#Hst, #Hmsg, %Hi, %Hpok, %Hmok, %hx1, %hx2, %hp1, %hp2, %hll, %hel⟩
  read_server
  read_msg
  iunfold logRO at Hve
  icases Hve with ⟨%fs, #Hfs, #Hfl⟩
  ihave %Hfsl := ownSlice_len $$ Hfs
  ihave %Hfll := BigSepL2.bigSepL2_length $$ Hfl
  iapply wp_fupd
  wp_auto
  lookup_server
  have hlen : sint.Z gs.Log'.len = ((st.s (uint.nat i)).log.length : Int) := by rw [← Hell, Hesl.1]; word
  have hflen : sint.Z gm.Entries'.len = (m.entries.length : Int) := by rw [← Hfll, Hfsl.1]; word
  have hpn : sint.Z (gm.PrevLogIndex' + gm.Entries'.len) = m.prevLogIndex + m.entries.length := by
    have := Hv.2.2.2.2.2.2.1; rw [← hflen, ← this]; word
  have hcm : sint.Z gm.CommitIndex' = m.commitIndex := Hv.2.2.2.2.2.2.2.2.1
  ipersist s
  ipersist m
  ipersist i
  ipersist j
  ipersist index
  ipersist v
  by_cases hA : sint.Z index ≤ (st.s (uint.nat i)).commitIndex
  · rw [decide_eq_true (show sint.Z index ≤ sint.Z gs.CommitIndex' by rw [Hf.2.2.2.2.1]; exact hA)]
    have hcmp : decide (sint.Z gs.CommitIndex' < sint.Z index) = false := by
      rw [Hf.2.2.2.2.1]; simp; omega
    wp_auto
    wp_apply wp_clone p st $$ [Hst] as %t Ht
    · iexact Hst
    try wp_auto
    rw [decide_eq_true (show sint.Z index ≤ sint.Z gs.CommitIndex' by rw [Hf.2.2.2.2.1]; exact hA)]
    wp_auto
    rw [decide_strRel Hv.2.1 strRel_heartbeat]
    by_cases hsb0 : m.subtype = "heartbeat"
    · rw [decide_eq_true hsb0]
      wp_auto
      wp_apply wp_commitTo t st [] i gm.CommitIndex' $$ [Ht] as Ht
      · iframe Ht; ipureintro; exact Hi
      have hst : st.appendEntriesAlreadyDone (uint.nat i) (uint.nat j) (sint.Z index) m = some ((st.commitTo (uint.nat i) (sint.Z gm.CommitIndex')).reply { type := .appendEntriesResponse, subtype := m.subtype, term := (st.s (uint.nat i)).currentTerm, success := true, matchIndex := (if (Bool.or (m.subtype == "heartbeat") (decide (sint.Z index > (st.s (uint.nat i)).commitIndex))) then m.prevLogIndex + m.entries.length else (st.s (uint.nat i)).commitIndex), source := uint.nat i, dest := uint.nat j } m) := by
        unfold State.appendEntriesAlreadyDone; simp [hA, hsb0, hcm]; try (intro h; omega)
      ad_fin (st.commitTo (uint.nat i) (sint.Z gm.CommitIndex'))
    · rw [decide_eq_false hsb0]
      wp_auto
      have hst : st.appendEntriesAlreadyDone (uint.nat i) (uint.nat j) (sint.Z index) m = some (st.reply { type := .appendEntriesResponse, subtype := m.subtype, term := (st.s (uint.nat i)).currentTerm, success := true, matchIndex := (if (Bool.or (m.subtype == "heartbeat") (decide (sint.Z index > (st.s (uint.nat i)).commitIndex))) then m.prevLogIndex + m.entries.length else (st.s (uint.nat i)).commitIndex), source := uint.nat i, dest := uint.nat j } m) := by
        unfold State.appendEntriesAlreadyDone; simp [hA, hsb0]; try (intro h; omega)
      ad_fin st
  rw [decide_eq_false (show ¬ sint.Z index ≤ sint.Z gs.CommitIndex' by rw [Hf.2.2.2.2.1]; exact hA)]
  have hcmp : decide (sint.Z gs.CommitIndex' < sint.Z index) = true := by
    rw [Hf.2.2.2.2.1]; simp; omega
  wp_auto
  rw [hcmp]
  wp_auto
  have hz := uint_eq_iff gm.Entries'.len (W64 0) _ 0 (by rw [show uint.nat gm.Entries'.len = m.entries.length by have := hflen; word]) rfl
  by_cases hB1 : m.entries.length = 0
  · rw [decide_eq_true (hz.2 hB1)]
    have hen : m.entries.isEmpty = true := by simpa using hB1
    ad_tailB
  rw [decide_eq_false (fun e => hB1 (hz.1 e))]
  wp_auto
  rw [decide_eq_false (fun e => hB1 (hz.1 e))]
  wp_auto
  have hne : m.entries ≠ [] := fun h => hB1 (by simp [h])
  have hle : sint.Z (gm.PrevLogIndex' + gm.Entries'.len) ≤ sint.Z gs.Log'.len ↔
      m.prevLogIndex + m.entries.length ≤ ((st.s (uint.nat i)).log.length : Int) := by rw [hpn, hlen]
  by_cases hB2 : m.prevLogIndex + m.entries.length ≤ ((st.s (uint.nat i)).log.length : Int)
  rotate_left
  · rw [decide_eq_false (fun e => hB2 (hle.1 e))]
    wp_auto
    imodintro
    iapply HΦ
    have : st.appendEntriesAlreadyDone (uint.nat i) (uint.nat j) (sint.Z index) m = none := by
      unfold State.appendEntriesAlreadyDone; simp [hA, hne, hB2]
    rw [this]; ipureintro; rfl
  rw [decide_eq_true (hle.2 hB2)]
  wp_auto
  wp_apply wp_HasNoConflict p st i index gm.Entries' m.entries $$ [Hst]
  · iframe Hst
    isplitl []
    · iunfold logRO; iexists fs; iframe Hfs Hfl
    ipureintro; exact ⟨Hi, hx1, hx2, hll, hel⟩
  cases hnc : st.hasNoConflict (uint.nat i) (sint.Z index) m.entries
  · wp_auto
    imodintro
    iapply HΦ
    have : st.appendEntriesAlreadyDone (uint.nat i) (uint.nat j) (sint.Z index) m = none := by
      unfold State.appendEntriesAlreadyDone; simp [hA, hne, hB2, hnc]
    rw [this]; ipureintro; rfl
  have hen : (m.prevLogIndex + m.entries.length ≤ ((st.s (uint.nat i)).log.length : Int)) ∧ st.hasNoConflict (uint.nat i) (sint.Z index) m.entries = true := ⟨hB2, hnc⟩
  have hen' : m.entries.isEmpty = false := by simpa using hB1
  ad_tailB

end proof

end Etcdraft
end EtcdGrove
end Perennial
