/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__HandleRequestVoteResponse`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__HandleRequestVoteResponse
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__mut
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Add
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__discard

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

theorem State.HandleRequestVoteResponse.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_mut : State.mut.spec (GF := GF) (hG := hG))
    (wp_Add : Set.Add.spec (GF := GF) (hG := hG))
    (wp_discard : State.discard.spec (GF := GF) (hG := hG)) :
    State.HandleRequestVoteResponse.spec (GF := GF) (hG := hG) := by
  intro p st i j q m
  wp_start as ⟨#Hst, #Hmsg, %Hi, %Hmnd⟩
  read_server
  read_msg
  iapply wp_fupd
  wp_auto
  lookup_server
  have ht := sint_eq_iff gm.Term' gs.CurrentTerm' _ _ Hv.2.2.1 Hf.1
  by_cases h1 : m.term = (st.s (uint.nat i)).currentTerm
  rotate_left
  · rw [decide_eq_false (fun e => h1 (ht.1 e))]
    wp_auto
    imodintro
    iapply HΦ
    have : st.handleRequestVoteResponse (uint.nat i) (uint.nat j) m = none := by
      unfold State.handleRequestVoteResponse; simp [h1]
    rw [this]
    ipureintro; rfl
  rw [decide_eq_true (ht.2 h1)]
  wp_auto
  wp_apply wp_clone p st $$ [Hst] as %t Ht
  · iexact Hst
  try wp_auto
  try simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.PreCandidate]
  rw [decide_strRel Hf.2.1 strRel_preCandidate]
  by_cases h2 : (st.s (uint.nat i)).state = preCandidate
  · rw [decide_eq_true h2]
    wp_auto
    wp_apply wp_discard t st [] q m $$ [Ht Hmsg] as Ht
    · iframe Ht Hmsg; ipureintro; exact Hmnd
    try wp_auto
    imod stateOwn_persist $$ Ht with #Ht
    imodintro
    iapply HΦ
    have : st.handleRequestVoteResponse (uint.nat i) (uint.nat j) m = some (st.discard m) := by
      unfold State.handleRequestVoteResponse; simp [h1, h2]
    rw [this]
    iexact Ht
  rw [decide_eq_false h2]
  wp_auto
  mut_open t, st, [], i, Ht
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Add_unfold.method_unfold]
  wp_auto
  wp_apply wp_Add _ _ j $$ [Hvr] as %u #Hu
  · iexact Hvr
  try wp_auto
  rw [Hv.2.2.2.2.2.1]
  cases hg : m.voteGranted
  · try wp_auto
    close_copy' { gc with VotesResponded' := u },
      (fun w => { w with votesResponded := (st.s (uint.nat i)).votesResponded.add (uint.nat j) }),
      Hcf with Hcl Hu Hcg Hcc Hcd
    wp_apply wp_discard t _ _ q m $$ [Hs Hmsg] as Ht
    · iframe Hs Hmsg; ipureintro; exact Hmnd
    try wp_auto
    imod stateOwn_persist $$ Ht with #Ht
    imodintro
    iapply HΦ
    rw [show st.handleRequestVoteResponse (uint.nat i) (uint.nat j) m = some ((st.upd (uint.nat i) (fun w => { w with votesResponded := (st.s (uint.nat i)).votesResponded.add (uint.nat j) })).discard m) by unfold State.handleRequestVoteResponse; simp [h1, h2, hg]]
    iexact Ht
  · try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Add_unfold.method_unfold]
    wp_auto
    wp_apply wp_Add _ _ j $$ [Hvg] as %u2 #Hu2
    · iexact Hvg
    try wp_auto
    close_copy' { gc with VotesResponded' := u, VotesGranted' := u2 },
      (fun w => { w with votesResponded := (st.s (uint.nat i)).votesResponded.add (uint.nat j), votesGranted := (st.s (uint.nat i)).votesGranted.add (uint.nat j) }),
      Hcf with Hcl Hu Hu2 Hcc Hcd
    wp_apply wp_discard t _ _ q m $$ [Hs Hmsg] as Ht
    · iframe Hs Hmsg; ipureintro; exact Hmnd
    try wp_auto
    imod stateOwn_persist $$ Ht with #Ht
    imodintro
    iapply HΦ
    rw [show st.handleRequestVoteResponse (uint.nat i) (uint.nat j) m = some ((st.upd (uint.nat i) (fun w => { w with votesResponded := (st.s (uint.nat i)).votesResponded.add (uint.nat j), votesGranted := (st.s (uint.nat i)).votesGranted.add (uint.nat j) })).discard m) by unfold State.handleRequestVoteResponse; simp [h1, h2, hg]]
    iexact Ht

end proof

end Etcdraft
end EtcdGrove
end Perennial
