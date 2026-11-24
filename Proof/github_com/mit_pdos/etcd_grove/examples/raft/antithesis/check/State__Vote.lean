/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `State.Vote` (B 100).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Vote
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__VoteOf
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem State.Vote.wp_proof (wp_VoteOf : State.VoteOf.spec (GF := GF) (hG := hG)) :
    State.Vote.spec (GF := GF) (hG := hG) := by
  intro p s n
  wp_start as ⟨#Hs, %Hn⟩
  obtain ⟨Hn0, Hlt⟩ := Hn
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  icases intsRO_at g.VoteTerm' s.voteTerm n ⟨Hn0, by rw [HWf.len_voteTerm]; exact Hlt⟩ $$ HVoteTerm with ⟨%vt, #Hvt, %Hvt⟩
  ihave #Hvf := strsRO_at g.VoteFor' s.voteFor n ⟨Hn0, by rw [HWf.len_voteFor]; exact Hlt⟩ $$ HVoteFor
  icases intsRO_at g.CurrentTerm' s.currentTerm n ⟨Hn0, by rw [HWf.len_currentTerm]; exact Hlt⟩ $$ HCurrentTerm with ⟨%ct, #Hct, %Hct⟩
  wp_auto
  wp_apply wp_load_at _ _ vt Hn0 $$ [Hvt]
  · iexact Hvt
  try wp_auto
  wp_apply wp_load_at _ _ _ Hn0 $$ [Hvf] as -
  · iexact Hvf
  try wp_auto
  wp_apply wp_load_at _ _ ct Hn0 $$ [Hct]
  · iexact Hct
  try wp_auto
  wp_apply wp_VoteOf p s vt _ ct $$ [Hs]
  · iexact Hs
  try wp_auto
  unfold State.vote
  rw [← Hvt, ← Hct]
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
