(** * Pure model-level lemmas and vocabulary

    Split out of [election.v] on 2026-09-14; see
    [notes/raft-election-refinement.md]. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.defs.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** The (fixed) set of voters. *)
Context (cfg : gset w64).

Implicit Type γ : raft_election_names.
Implicit Type s : nstate.t.

(** The outcome of feeding a [MsgVoteResp] to a candidate. *)
Definition vote_resp_result id s (from : w64) (reject : bool) (won lost : bool)
  : nstate.t :=
  let s1 := s <| nstate.votes := record_vote s.(nstate.votes) from (negb reject) |> in
  if won then become_leader id s1
  else if lost then become_follower s1 s1.(nstate.term) (W64 0)
  else s1.

(** An election message: the only ones in scope. *)
Definition election_msg (m : raftpb.Message.t) : Prop :=
  m.(raftpb.Message.Type') = MsgHup ∨
  m.(raftpb.Message.Type') = MsgVote ∨
  m.(raftpb.Message.Type') = MsgVoteResp.

(** ** Model-level lemmas justifying each branch of [Step]

    These are pure facts about the protocol, independent of the program
    logic; the WP proofs below feed them to [own_raft_ghost_step]. *)

(** Dropping a message is always legal. *)
Lemma step_drop id s : step cfg id s [] s [].
Proof. constructor. Qed.

(** Stepping down and then answering a vote request, in one protocol step. *)
Lemma step_stepdown_then_vote id s (m : msg.t) :
  m.(msg.ty) = mtype.Vote →
  m.(msg.to) = id →
  uint.Z s.(nstate.term) < uint.Z m.(msg.term) →
  step cfg id s ([m] ++ [m])
       ((become_follower s m.(msg.term) (W64 0))
          <| nstate.vote := m.(msg.from) |>)
       ([] ++ [msg.mk mtype.VoteResp id m.(msg.from) m.(msg.term) false]).
Proof.
  intros Hty Hto Hlt.
  eapply step_trans with
    (s₁ := become_follower s m.(msg.term)
             (if from_leader m.(msg.ty) then m.(msg.from) else W64 0)).
  { by apply step_higher_term. }
  rewrite Hty /=.
  apply step_grant_vote; try done.
  (* [become_follower] to a strictly greater term clears the vote and the
     leader, so [can_vote] holds. *)
  rewrite /can_vote /become_follower /=.
  right. destruct (decide (m.(msg.term) = s.(nstate.term))) as [Heq|Hne].
  { rewrite Heq in Hlt. lia. }
  done.
Qed.

(** Stepping down and then declining. *)
Lemma step_stepdown_then_reject id s (m : msg.t) :
  m.(msg.ty) = mtype.Vote →
  m.(msg.to) = id →
  uint.Z s.(nstate.term) < uint.Z m.(msg.term) →
  step cfg id s ([m] ++ [m]) (become_follower s m.(msg.term) (W64 0))
       ([] ++ [msg.mk mtype.VoteResp id m.(msg.from) m.(msg.term) true]).
Proof.
  intros Hty Hto Hlt.
  eapply step_trans with
    (s₁ := become_follower s m.(msg.term)
             (if from_leader m.(msg.ty) then m.(msg.from) else W64 0)).
  { by apply step_higher_term. }
  rewrite Hty /=.
  by apply step_reject_vote.
Qed.

(** Recording a vote response and then winning. *)
Lemma step_record_then_win id s (m : msg.t) peers :
  m.(msg.ty) = mtype.VoteResp →
  m.(msg.to) = id →
  m.(msg.term) = s.(nstate.term) →
  s.(nstate.role) = role.Candidate →
  peers ≡ₚ elements (cfg ∖ {[id]}) →
  let s1 := s <| nstate.votes :=
                  record_vote s.(nstate.votes) m.(msg.from) (negb m.(msg.reject)) |> in
  is_quorum cfg (granted s1.(nstate.votes)) →
  step cfg id s ([m] ++ []) (become_leader id s1)
       ([] ++ ((λ to, msg.mk mtype.App id to s1.(nstate.term) false) <$> peers)).
Proof.
  intros ????? s1 Hq.
  eapply step_trans; [by apply step_record_vote|].
  by apply step_win.
Qed.

(** Recording a vote response and then losing. *)
Lemma step_record_then_lose id s (m : msg.t) :
  m.(msg.ty) = mtype.VoteResp →
  m.(msg.to) = id →
  m.(msg.term) = s.(nstate.term) →
  s.(nstate.role) = role.Candidate →
  let s1 := s <| nstate.votes :=
                  record_vote s.(nstate.votes) m.(msg.from) (negb m.(msg.reject)) |> in
  is_quorum cfg (rejected s1.(nstate.votes)) →
  step cfg id s ([m] ++ []) (become_follower s1 s1.(nstate.term) (W64 0)) ([] ++ []).
Proof.
  intros ???? s1 Hq.
  eapply step_trans; [by apply step_record_vote|].
  by apply step_lose.
Qed.

End proof.
