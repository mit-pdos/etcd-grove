/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__RequestVote`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__RequestVote
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__send
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__GetConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__GetLearners
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Union
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Minus
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.LastTerm

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

theorem State.RequestVote.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_send : State.send.spec (GF := GF) (hG := hG))
    (wp_GetConfig : State.GetConfig.spec (GF := GF) (hG := hG))
    (wp_GetLearners : State.GetLearners.spec (GF := GF) (hG := hG))
    (wp_Union : Set.Union.spec (GF := GF) (hG := hG))
    (wp_Minus : Set.Minus.spec (GF := GF) (hG := hG))
    (wp_Has : Set.Has.spec (GF := GF) (hG := hG))
    (wp_LastTerm : LastTerm.spec (GF := GF) (hG := hG)) :
    State.RequestVote.spec (GF := GF) (hG := hG) := by
  intro p st i j
  wp_start as ⟨#Hst, %Hi, %Hpok⟩
  read_server
  iapply wp_fupd
  wp_auto
  lookup_server
  try simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Candidate]
  rw [decide_strRel Hf.2.1 strRel_candidate]
  by_cases h1 : (st.s (uint.nat i)).state = candidate
  rotate_left
  · rw [decide_eq_false h1]
    wp_auto
    imodintro
    iapply HΦ
    have : st.requestVote (uint.nat i) (uint.nat j) = none := by
      unfold State.requestVote; simp [h1]
    rw [this]
    ipureintro; rfl
  rw [decide_eq_true h1]
  wp_auto
  wp_apply wp_GetLearners p st i $$ [Hst] as %sl1 #Hsl1
  · iframe Hst; ipureintro; exact Hi
  try wp_auto
  wp_apply wp_GetConfig p st i $$ [Hst] as %sl2 #Hsl2
  · iframe Hst; ipureintro; exact Hi
  try wp_auto
  wp_apply wp_Union _ _ _ _ $$ [Hsl1 Hsl2] as %sl3 #Hsl3
  · iframe Hsl1 Hsl2
  try wp_auto
  wp_apply wp_Minus _ _ _ _ $$ [Hsl3 Hvr] as %sl4 #Hsl4
  · iframe Hsl3 Hvr
  try wp_auto
  wp_apply wp_Has _ _ j $$ [Hsl4]
  · iexact Hsl4
  iintro -
  try wp_auto
  have hc : (((st.getConfig (uint.nat i)).union (st.getLearners (uint.nat i))).minus (st.s (uint.nat i)).votesResponded).contains (uint.nat j) = decide (uint.nat j ∈ ((st.getConfig (uint.nat i)).union (st.getLearners (uint.nat i))).minus (st.s (uint.nat i)).votesResponded) := by
    simp [List.contains_iff_mem]
  by_cases h2 : uint.nat j ∈ ((st.getConfig (uint.nat i)).union (st.getLearners (uint.nat i))).minus (st.s (uint.nat i)).votesResponded
  rotate_left
  · rw [decide_eq_false h2]
    wp_auto
    imodintro
    iapply HΦ
    have : st.requestVote (uint.nat i) (uint.nat j) = none := by
      unfold State.requestVote; simp [h1, hc, h2]
    rw [this]
    ipureintro; rfl
  rw [decide_eq_true h2]
  wp_auto
  wp_apply wp_clone p st $$ [Hst] as %t Ht
  · iexact Hst
  try wp_auto
  have hlen : sint.Z gs.Log'.len = ((st.s (uint.nat i)).log.length : Int) := by rw [← Hell, Hesl.1]; word
  have hij : i = j ↔ uint.nat i = uint.nat j := ⟨fun h => h ▸ rfl, fun h => word.unsigned_inj (by exact_mod_cast h)⟩
  ihave #Hnil := logRO_nil (GF := GF)
  by_cases h3 : i = j
  · rw [decide_eq_true h3]
    wp_auto
    irename «$a0» => Hmq
    ipersist Hmq
    ihave #Hm : msgRO (GF := GF) «$a0_ptr» { type := .requestVoteResponse, term := (st.s (uint.nat i)).currentTerm, voteGranted := true, source := uint.nat i, dest := uint.nat i } $$ []
    · iunfold msgRO
      iexists _
      iframe Hmq Hnil
      ipureintro
      exact ⟨rfl, strRel_empty, Hf.1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    wp_apply wp_send t st [] _ _ $$ [Ht Hm] as Ht
    · iframe Ht Hm; ipureintro; exact ⟨Hpok.1, Hpok.count_lt _⟩
    try wp_auto
    imod stateOwn_persist $$ Ht with #Ht
    imodintro
    iapply HΦ
    have : st.requestVote (uint.nat i) (uint.nat j) = some (st.send { type := .requestVoteResponse, term := (st.s (uint.nat i)).currentTerm, voteGranted := true, source := uint.nat i, dest := uint.nat i }) := by
      unfold State.requestVote; rw [if_pos (by simp [h1, hc, h2])]; simp [hij.1 h3]
    rw [this]
    iexact Ht
  rw [decide_eq_false h3]
  wp_auto
  wp_apply wp_LastTerm _ _ $$ [Hlog] as %lt %Hlt
  · iexact Hlog
  try wp_auto
  irename «$a0» => Hmq
  ipersist Hmq
  ihave #Hm : msgRO (GF := GF) «$a0_ptr» { type := .requestVoteRequest, term := (st.s (uint.nat i)).currentTerm, lastLogTerm := lastTerm (st.s (uint.nat i)).log, lastLogIndex := (st.s (uint.nat i)).log.length, source := uint.nat i, dest := uint.nat j } $$ []
  · iunfold msgRO
    iexists _
    iframe Hmq Hnil
    ipureintro
    exact ⟨rfl, strRel_empty, Hf.1, Hlt, hlen, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  wp_apply wp_send t st [] _ _ $$ [Ht Hm] as Ht
  · iframe Ht Hm; ipureintro; exact ⟨Hpok.1, Hpok.count_lt _⟩
  try wp_auto
  imod stateOwn_persist $$ Ht with #Ht
  imodintro
  iapply HΦ
  have : st.requestVote (uint.nat i) (uint.nat j) = some (st.send { type := .requestVoteRequest, term := (st.s (uint.nat i)).currentTerm, lastLogTerm := lastTerm (st.s (uint.nat i)).log, lastLogIndex := (st.s (uint.nat i)).log.length, source := uint.nat i, dest := uint.nat j }) := by
    unfold State.requestVote; rw [if_pos (by simp [h1, hc, h2]), if_pos (by simpa using fun e => h3 (hij.2 e))]
  rw [this]
  iexact Ht

end proof

end Etcdraft
end EtcdGrove
end Perennial
