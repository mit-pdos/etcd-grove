/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__ReturnToFollowerState`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__ReturnToFollowerState
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__mut

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
local macro "rf_none" : tactic => `(tactic| (
    try wp_auto
    imodintro
    iapply HΦ
    have : st.returnToFollowerState (uint.nat i) m = none := by
      unfold State.returnToFollowerState; simp_all
    rw [this]
    ipureintro; rfl))

-- Enabled: the clone, server `i` a follower (hygiene off).
set_option hygiene false in
local macro "rf_some" : tactic => `(tactic| (
    have hrf : st.returnToFollowerState (uint.nat i) m =
        some (st.upd (uint.nat i) (fun v => { v with state := follower })) := by
      unfold State.returnToFollowerState
      rcases hrole with h | h <;> simp [h1, h, candidate, preCandidate]
    try wp_auto
    wp_apply wp_clone p st $$ [Hst] as %t Ht
    · iexact Hst
    try wp_auto
    mut_open t, st, [], i, Ht
    simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Follower]
    try wp_auto
    close_copy { gc with State' := go!"StateFollower" }, (fun v => { v with state := follower }),
      ⟨Hcf.1, strRel_follower, Hcf.2.2.1, Hcf.2.2.2.1, Hcf.2.2.2.2.1, Hcf.2.2.2.2.2⟩
    try wp_auto
    imodintro
    iapply HΦ
    rw [hrf]
    iexists _; iexact Hs))

theorem State.ReturnToFollowerState.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_mut : State.mut.spec (GF := GF) (hG := hG)) :
    State.ReturnToFollowerState.spec (GF := GF) (hG := hG) := by
  intro p st i q m
  wp_start as ⟨#Hst, #Hmsg, %Hi⟩
  read_server
  read_msg
  iapply wp_fupd
  wp_auto
  lookup_server
  have ht := sint_eq_iff gm.Term' gs.CurrentTerm' _ _ Hv.2.2.1 Hf.1
  by_cases h1 : m.term = (st.s (uint.nat i)).currentTerm
  rotate_left
  · rw [decide_eq_false (fun e => h1 (ht.1 e))]; rf_none
  rw [decide_eq_true (ht.2 h1)]
  wp_auto
  rw [decide_strRel Hf.2.1 strRel_candidate]
  by_cases h2 : (st.s (uint.nat i)).state = candidate
  · rw [decide_eq_true h2]
    have hrole : (st.s (uint.nat i)).state = candidate ∨ (st.s (uint.nat i)).state = preCandidate := .inl h2
    rf_some
  rw [decide_eq_false h2]
  wp_auto
  rw [decide_strRel Hf.2.1 strRel_preCandidate]
  by_cases h3 : (st.s (uint.nat i)).state = preCandidate
  · rw [decide_eq_true h3]
    have hrole : (st.s (uint.nat i)).state = candidate ∨ (st.s (uint.nat i)).state = preCandidate := .inr h3
    rf_some
  rw [decide_eq_false h3]
  rf_none

end proof

end Etcdraft
end EtcdGrove
end Perennial
