/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__RejectAppendEntriesRequest`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__RejectAppendEntriesRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
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

-- Not enabled: `nil` (hygiene off).
set_option hygiene false in
local macro "rj_none" lo:term : tactic => `(tactic| (
    try wp_auto
    imodintro
    iapply HΦ
    have : st.rejectAppendEntriesRequest (uint.nat i) (uint.nat j) m $lo = none := by
      unfold State.rejectAppendEntriesRequest; simp_all
    rw [this]
    ipureintro; rfl))

-- Enabled, `success` computed: the response sent, the request discarded (hygiene off).
set_option hygiene false in
local macro "rj_fin" lo:term : tactic => `(tactic| (
    try wp_auto
    irename «$a0» => Hmq
    ipersist Hmq
    ihave #Hnil := logRO_nil (GF := GF)
    ihave #Hresp : msgRO (GF := GF) «$a0_ptr» { type := .appendEntriesResponse, subtype := "app", term := (st.s (uint.nat i)).currentTerm, success := (st.preVote || st.checkQuorum) && decide (m.term < (st.s (uint.nat i)).currentTerm), matchIndex := 0, source := uint.nat i, dest := uint.nat j } $$ []
    · iunfold msgRO
      iexists _
      iframe Hmq Hnil
      ipureintro
      exact ⟨rfl, strRel_app, Hf.1, rfl, rfl, rfl, rfl, rfl, rfl, by simp_all, rfl, rfl, rfl⟩
    wp_apply wp_reply t st [] _ _ q m $$ [Ht Hresp Hmsg] as Ht
    · iframe Ht Hresp Hmsg; ipureintro; exact ⟨Hpok.1, Hpok.count_lt _, Hmok.1⟩
    try wp_auto
    imod stateOwn_persist $$ Ht with #Ht
    imodintro
    iapply HΦ
    have : st.rejectAppendEntriesRequest (uint.nat i) (uint.nat j) m $lo =
        some (st.reply { type := .appendEntriesResponse, subtype := "app", term := (st.s (uint.nat i)).currentTerm, success := (st.preVote || st.checkQuorum) && decide (m.term < (st.s (uint.nat i)).currentTerm), matchIndex := 0, source := uint.nat i, dest := uint.nat j } m) := by
      unfold State.rejectAppendEntriesRequest; simp_all
    rw [this]
    iexact Ht))

-- Enabled: the clone, `success` by the configuration's cases (hygiene off).
set_option hygiene false in
local macro "rj_some" lo:term : tactic => `(tactic| (
    try wp_auto
    wp_apply wp_clone p st $$ [Hst] as %t Ht
    · iexact Hst
    try wp_auto
    rw [Hrc.2.1, Hrc.2.2]
    cases hpv : st.preVote <;> cases hcq : st.checkQuorum <;>
      (try wp_auto) <;> (try rw [decide_eq_true (htl.2 hlt)]) <;> (try rw [decide_eq_false (fun e => hlt (htl.1 e))]) <;> rj_fin $lo))

theorem State.RejectAppendEntriesRequest.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_reply : State.reply.spec (GF := GF) (hG := hG)) :
    State.RejectAppendEntriesRequest.spec (GF := GF) (hG := hG) := by
  intro p st i j q m logOk
  wp_start as ⟨#Hst, #Hmsg, %Hi, %Hpok, %Hmok⟩
  read_server
  read_msg
  iapply wp_fupd
  wp_auto
  lookup_server
  have htl : sint.Z gm.Term' < sint.Z gs.CurrentTerm' ↔ m.term < (st.s (uint.nat i)).currentTerm := by
    rw [Hf.1, Hv.2.2.1]
  by_cases hlt : m.term < (st.s (uint.nat i)).currentTerm
  · rw [decide_eq_true (htl.2 hlt)]
    rj_some (logOk)
  rw [decide_eq_false (fun e => hlt (htl.1 e))]
  wp_auto
  have ht := sint_eq_iff gm.Term' gs.CurrentTerm' _ _ Hv.2.2.1 Hf.1
  by_cases h1 : m.term = (st.s (uint.nat i)).currentTerm
  rotate_left
  · rw [decide_eq_false (fun e => h1 (ht.1 e))]; rj_none (logOk)
  rw [decide_eq_true (ht.2 h1)]
  wp_auto
  try simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Follower]
  rw [decide_strRel Hf.2.1 strRel_follower]
  by_cases h2 : (st.s (uint.nat i)).state = follower
  rotate_left
  · rw [decide_eq_false h2]; rj_none (logOk)
  rw [decide_eq_true h2]
  wp_auto
  cases hl : logOk
  · rj_some (false)
  · rj_none (true)

end proof

end Etcdraft
end EtcdGrove
end Perennial
