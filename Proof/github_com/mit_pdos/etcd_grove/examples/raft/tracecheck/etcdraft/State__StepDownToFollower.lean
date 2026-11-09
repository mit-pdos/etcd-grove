/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__StepDownToFollower`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__StepDownToFollower
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

-- Enabled: the clone, stepped down (hygiene off).
set_option hygiene false in
local macro "sd_tail" : tactic => `(tactic| (
    have hsd : st.stepDownToFollower (uint.nat i) =
        some (st.becomeFollowerOfTerm (uint.nat i) (st.s (uint.nat i)).currentTerm) := by
      unfold State.stepDownToFollower; rcases hrole with h | h | h <;> simp [h, leader, candidate, preCandidate]
    try wp_auto
    wp_apply wp_clone p st $$ [Hst] as %t Ht
    · iexact Hst
    try wp_auto
    wp_apply wp_bf t st [] i gs.CurrentTerm' $$ [Ht] as Ht
    · iframe Ht; ipureintro; exact Hi
    try wp_auto
    imod stateOwn_persist $$ Ht with #Ht
    imodintro
    iapply HΦ
    rw [hsd, Hf.1]
    iexact Ht))

theorem State.StepDownToFollower.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_bf : State.becomeFollowerOfTerm.spec (GF := GF) (hG := hG)) :
    State.StepDownToFollower.spec (GF := GF) (hG := hG) := by
  intro p st i
  wp_start as ⟨#Hst, %Hi⟩
  read_server
  iapply wp_fupd
  wp_auto
  lookup_server
  rw [decide_strRel Hf.2.1 strRel_leader]
  by_cases h1 : (st.s (uint.nat i)).state = leader
  · rw [decide_eq_true h1]
    have hrole : (st.s (uint.nat i)).state = leader ∨ (st.s (uint.nat i)).state = candidate ∨
        (st.s (uint.nat i)).state = preCandidate := .inl h1
    sd_tail
  rw [decide_eq_false h1]
  wp_auto
  rw [decide_strRel Hf.2.1 strRel_candidate]
  by_cases h2 : (st.s (uint.nat i)).state = candidate
  · rw [decide_eq_true h2]
    have hrole : (st.s (uint.nat i)).state = leader ∨ (st.s (uint.nat i)).state = candidate ∨
        (st.s (uint.nat i)).state = preCandidate := .inr (.inl h2)
    sd_tail
  rw [decide_eq_false h2]
  wp_auto
  rw [decide_strRel Hf.2.1 strRel_preCandidate]
  by_cases h3 : (st.s (uint.nat i)).state = preCandidate
  · rw [decide_eq_true h3]
    have hrole : (st.s (uint.nat i)).state = leader ∨ (st.s (uint.nat i)).state = candidate ∨
        (st.s (uint.nat i)).state = preCandidate := .inr (.inr h3)
    sd_tail
  rw [decide_eq_false h3]
  wp_auto
  imodintro
  iapply HΦ
  have : st.stepDownToFollower (uint.nat i) = none := by
    unfold State.stepDownToFollower; simp [h1, h2, h3]
  rw [this]
  ipureintro; rfl

end proof

end Etcdraft
end EtcdGrove
end Perennial
