/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__UpdateTerm`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__UpdateTerm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__becomeFollowerOfTerm

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
local macro "ut_none" : tactic => `(tactic| (
    try wp_auto
    imodintro
    iapply HΦ
    have : st.updateTerm (uint.nat i) (uint.nat j) m = none := by
      unfold State.updateTerm; simp_all
    rw [this]
    ipureintro; rfl))

-- Enabled: the clone, a follower of `m`'s term (hygiene off).
set_option hygiene false in
local macro "ut_some" : tactic => `(tactic| (
    try wp_auto
    wp_apply wp_clone p st $$ [Hst] as %t Ht
    · iexact Hst
    try wp_auto
    wp_apply wp_bf t st [] i gm.Term' $$ [Ht] as Ht
    · iframe Ht; ipureintro; exact Hi
    try wp_auto
    imod stateOwn_persist $$ Ht with #Ht
    imodintro
    iapply HΦ
    rw [h5, ← Hv.2.2.1]
    iexact Ht))

theorem State.UpdateTerm.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_bf : State.becomeFollowerOfTerm.spec (GF := GF) (hG := hG)) :
    State.UpdateTerm.spec (GF := GF) (hG := hG) := by
  intro p st i j q m
  wp_start as ⟨#Hst, #Hmsg, %Hi⟩
  read_server
  read_msg
  iapply wp_fupd
  wp_auto
  lookup_server
  simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.PreVoteRequest,
    github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.PreVoteResponse]
  have ht : sint.Z gs.CurrentTerm' < sint.Z gm.Term' ↔ (st.s (uint.nat i)).currentTerm < m.term := by
    rw [Hf.1, Hv.2.2.1]
  by_cases h1 : (st.s (uint.nat i)).currentTerm < m.term
  rotate_left
  · rw [decide_eq_false (fun e => h1 (ht.1 e))]; ut_none
  rw [decide_eq_true (ht.2 h1)]
  wp_auto
  rw [show (W8 4 : w8) = msgTypeW .preVoteRequest from rfl, msgTypeW_decide Hv.1]
  by_cases h2 : m.type = .preVoteRequest
  · rw [decide_eq_true h2]; ut_none
  rw [decide_eq_false h2]
  wp_auto
  rw [show (W8 5 : w8) = msgTypeW .preVoteResponse from rfl, msgTypeW_decide Hv.1]
  have h3 : ¬ (m.type = .preVoteResponse ∧ m.voteGranted = true) → st.updateTerm (uint.nat i) (uint.nat j) m =
      some (st.becomeFollowerOfTerm (uint.nat i) m.term) := by
    intro h3; unfold State.updateTerm; simp_all
  by_cases h4 : m.type = .preVoteResponse
  · rw [decide_eq_true h4]
    wp_auto
    rw [Hv.2.2.2.2.2.1]
    cases hg : m.voteGranted
    · have h5 := h3 (by simp [hg])
      ut_some
    · ut_none
  · rw [decide_eq_false h4]
    have h5 := h3 (by simp [h4])
    ut_some

end proof

end Etcdraft
end EtcdGrove
end Perennial
