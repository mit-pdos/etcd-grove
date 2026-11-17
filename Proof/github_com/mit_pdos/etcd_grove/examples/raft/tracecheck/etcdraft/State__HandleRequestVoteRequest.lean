/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__HandleRequestVoteRequest`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__HandleRequestVoteRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__mut
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.LastTerm
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

-- The response sent, the request discarded, the clone frozen (hygiene off).
set_option hygiene false in
local macro "rv_fin" st':term : tactic => `(tactic| (
    try wp_auto
    irename «$a0» => Hmq
    ipersist Hmq
    ihave #Hnil := logRO_nil (GF := GF)
    ihave #Hresp : msgRO (GF := GF) «$a0_ptr» { type := .requestVoteResponse, term := (st.s (uint.nat i)).currentTerm, voteGranted := ((m.term == (st.s (uint.nat i)).currentTerm) && (decide (m.lastLogTerm > lastTerm (st.s (uint.nat i)).log) || ((m.lastLogTerm == lastTerm (st.s (uint.nat i)).log) && decide (m.lastLogIndex ≥ (st.s (uint.nat i)).log.length))) && (((st.s (uint.nat i)).votedFor == uint.nat j) || (((st.s (uint.nat i)).votedFor == nil) && ((st.s (uint.nat i)).lead == nil)))), source := uint.nat i, dest := uint.nat j } $$ []
    · iunfold msgRO
      iexists _
      iframe Hmq Hnil
      ipureintro
      exact ⟨rfl, strRel_empty, Hf.1, rfl, rfl, hg.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    wp_apply wp_reply t $st' _ _ _ q m $$ [Ht Hresp Hmsg] as Ht
    · iframe Ht Hresp Hmsg; ipureintro; exact ⟨Hpok.1, Hpok.count_lt _, Hmok.1⟩
    try wp_auto
    imod stateOwn_persist $$ Ht with #Ht
    imodintro
    iapply HΦ
    have : st.handleRequestVoteRequest (uint.nat i) (uint.nat j) m = some (($st' : State).reply { type := .requestVoteResponse, term := (st.s (uint.nat i)).currentTerm, voteGranted := ((m.term == (st.s (uint.nat i)).currentTerm) && (decide (m.lastLogTerm > lastTerm (st.s (uint.nat i)).log) || ((m.lastLogTerm == lastTerm (st.s (uint.nat i)).log) && decide (m.lastLogIndex ≥ (st.s (uint.nat i)).log.length))) && (((st.s (uint.nat i)).votedFor == uint.nat j) || (((st.s (uint.nat i)).votedFor == nil) && ((st.s (uint.nat i)).lead == nil)))), source := uint.nat i, dest := uint.nat j } m) := by
      unfold State.handleRequestVoteRequest
      simp only [hg]
      simp [h0]
    rw [this]
    iexact Ht))

theorem State.HandleRequestVoteRequest.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_mut : State.mut.spec (GF := GF) (hG := hG))
    (wp_LastTerm : LastTerm.spec (GF := GF) (hG := hG))
    (wp_reply : State.reply.spec (GF := GF) (hG := hG)) :
    State.HandleRequestVoteRequest.spec (GF := GF) (hG := hG) := by
  intro p st i j q m
  wp_start as ⟨#Hst, #Hmsg, %Hi, %Hpok, %Hmok⟩
  read_server
  read_msg
  iapply wp_fupd
  wp_auto
  lookup_server
  wp_apply wp_LastTerm _ _ $$ [Hlog] as %lt %Hlt
  · iexact Hlog
  try wp_auto
  ipersist s
  ipersist m
  ipersist j
  ipersist i
  ipersist v
  have hlen : sint.Z gs.Log'.len = ((st.s (uint.nat i)).log.length : Int) := by rw [← Hell, Hesl.1]; word
  wp_join (Q := fun v => iprop(⌜v = #(decide (m.lastLogTerm > lastTerm (st.s (uint.nat i)).log) || ((m.lastLogTerm == lastTerm (st.s (uint.nat i)).log) && decide (m.lastLogIndex ≥ (st.s (uint.nat i)).log.length)))⌝)) at (if: _ then _ else _)
  · by_cases hgt : m.lastLogTerm > lastTerm (st.s (uint.nat i)).log
    · rw [decide_eq_true (show sint.Z lt < sint.Z gm.LastLogTerm' by rw [Hlt, Hv.2.2.2.1]; exact hgt)]
      wp_auto
      ipureintro; congr 1; simp [beq_iff_eq, beq_eq_false_iff_ne, hgt]
    rw [decide_eq_false (show ¬ sint.Z lt < sint.Z gm.LastLogTerm' by rw [Hlt, Hv.2.2.2.1]; exact hgt)]
    wp_auto
    wp_apply wp_LastTerm _ _ $$ [Hlog] as %lt2 %Hlt2
    · iexact Hlog
    try wp_auto
    have he := sint_eq_iff gm.LastLogTerm' lt2 _ _ Hv.2.2.2.1 Hlt2
    by_cases heq : m.lastLogTerm = lastTerm (st.s (uint.nat i)).log
    · rw [decide_eq_true (he.2 heq)]
      wp_auto
      ipureintro
      have : decide (sint.Z gs.Log'.len ≤ sint.Z gm.LastLogIndex') = decide (m.lastLogIndex ≥ (st.s (uint.nat i)).log.length) := by
        rw [hlen, Hv.2.2.2.2.1]; try rfl
      rw [this]; try simp [beq_iff_eq, heq]
    · rw [decide_eq_false (fun e => heq (he.1 e))]
      wp_auto
      ipureintro; congr 1; simp [beq_iff_eq, beq_eq_false_iff_ne, hgt, heq]
  rename_i v
  iintro %Hv0
  subst Hv0
  wp_auto
  ipersist logOk
  have e1 := sint_eq_iff gm.Term' gs.CurrentTerm' _ _ Hv.2.2.1 Hf.1
  have e3 := uint_eq_iff gs.VotedFor' j _ (uint.nat j) Hf.2.2.1 rfl
  have e4 := uint_eq_iff gs.VotedFor' (W64 0) _ nil Hf.2.2.1 rfl
  have e5 := uint_eq_iff gs.Lead' (W64 0) _ nil Hf.2.2.2.1 rfl
  wp_join (Q := fun v => iprop(⌜v = #((m.term == (st.s (uint.nat i)).currentTerm) && (decide (m.lastLogTerm > lastTerm (st.s (uint.nat i)).log) || ((m.lastLogTerm == lastTerm (st.s (uint.nat i)).log) && decide (m.lastLogIndex ≥ (st.s (uint.nat i)).log.length))) && (((st.s (uint.nat i)).votedFor == uint.nat j) || (((st.s (uint.nat i)).votedFor == nil) && ((st.s (uint.nat i)).lead == nil))))⌝)) at (if: _ then _ else _)
  · by_cases h1 : m.term = (st.s (uint.nat i)).currentTerm
    rotate_left
    · rw [decide_eq_false (fun x => h1 (e1.1 x))]
      wp_auto
      ipureintro; congr 1; simp [beq_iff_eq, beq_eq_false_iff_ne, h1]
    rw [decide_eq_true (e1.2 h1)]
    wp_auto
    cases hlo : (decide (m.lastLogTerm > lastTerm (st.s (uint.nat i)).log) || ((m.lastLogTerm == lastTerm (st.s (uint.nat i)).log) && decide (m.lastLogIndex ≥ (st.s (uint.nat i)).log.length)))
    · wp_auto
      ipureintro; congr 1; simp [beq_iff_eq, beq_eq_false_iff_ne]
    wp_auto
    by_cases h3 : (st.s (uint.nat i)).votedFor = uint.nat j
    · rw [decide_eq_true (e3.2 h3)]
      wp_auto
      ipureintro; congr 1; simp [beq_iff_eq, beq_eq_false_iff_ne, h1, h3]
    rw [decide_eq_false (fun x => h3 (e3.1 x))]
    wp_auto
    try simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Nil]
    by_cases h4 : (st.s (uint.nat i)).votedFor = nil
    · rw [decide_eq_true (e4.2 h4)]
      wp_auto
      have h3' : ¬ nil = uint.nat j := h4 ▸ h3
      by_cases h5 : (st.s (uint.nat i)).lead = nil
      · rw [decide_eq_true (e5.2 h5)]
        ipureintro; congr 1; simp [beq_iff_eq, beq_eq_false_iff_ne, h1, h3', h4, h5]
      · rw [decide_eq_false (fun x => h5 (e5.1 x))]
        ipureintro; congr 1; simp [beq_iff_eq, beq_eq_false_iff_ne, h1, h3', h4, h5]
    rw [decide_eq_false (fun x => h4 (e4.1 x))]
    wp_auto
    ipureintro; congr 1; simp [beq_iff_eq, beq_eq_false_iff_ne, h1, h3, h4]
  rename_i v
  iintro %Hv0
  subst Hv0
  wp_auto
  have hle : sint.Z gm.Term' ≤ sint.Z gs.CurrentTerm' ↔ m.term ≤ (st.s (uint.nat i)).currentTerm := by
    rw [Hf.1, Hv.2.2.1]
  by_cases h0 : m.term ≤ (st.s (uint.nat i)).currentTerm
  rotate_left
  · rw [decide_eq_false (fun e => h0 (hle.1 e))]
    wp_auto
    imodintro
    iapply HΦ
    have : st.handleRequestVoteRequest (uint.nat i) (uint.nat j) m = none := by
      unfold State.handleRequestVoteRequest; simp [h0]
    rw [this]
    ipureintro; rfl
  rw [decide_eq_true (hle.2 h0)]
  wp_auto
  wp_apply wp_clone p st $$ [Hst] as %t Ht
  · iexact Hst
  try wp_auto
  cases hg : ((m.term == (st.s (uint.nat i)).currentTerm) && (decide (m.lastLogTerm > lastTerm (st.s (uint.nat i)).log) || ((m.lastLogTerm == lastTerm (st.s (uint.nat i)).log) && decide (m.lastLogIndex ≥ (st.s (uint.nat i)).log.length))) && (((st.s (uint.nat i)).votedFor == uint.nat j) || (((st.s (uint.nat i)).votedFor == nil) && ((st.s (uint.nat i)).lead == nil))))
  · rv_fin st
  · try wp_auto
    mut_open t, st, [], i, Ht
    try wp_auto
    close_copy { gc with VotedFor' := j }, (fun v => { v with votedFor := uint.nat j }),
      ⟨Hcf.1, Hcf.2.1, rfl, Hcf.2.2.2.1, Hcf.2.2.2.2.1, Hcf.2.2.2.2.2⟩
    irename Hs => Ht
    rv_fin (st.upd (uint.nat i) (fun v => { v with votedFor := uint.nat j }))

end proof

end Etcdraft
end EtcdGrove
end Perennial
