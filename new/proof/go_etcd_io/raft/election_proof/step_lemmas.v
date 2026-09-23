(** * Pure model-level lemmas and vocabulary *)

Require Export New.proof.go_etcd_io.raft.election_proof.defs.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** The (fixed) set of voters. *)
Context (cfg : gset w64).

Implicit Type γ : raft_election_names.
Implicit Type s : nstate.t.

(** The outcome of feeding a [MsgVoteResp] to a candidate.  [ms] is what a
    winner's [bcastAppend] put on the network; it is irrelevant unless [won].

    [ms] is an arbitrary list of [App]s rather than one per peer, matching
    [step_win] — see the comment there for why the exact broadcast is not
    pinned down. *)
Definition vote_resp_result id s (from : w64) (reject : bool) (won lost : bool)
  (ms : list msg.t) : nstate.t :=
  let s1 := s <| nstate.votes := record_vote s.(nstate.votes) from (negb reject) |> in
  if won then send_msgs (become_leader id s1) ms
  else if lost then become_follower s1 s1.(nstate.term) (W64 0)
  else s1.


(** An election message: the only ones in scope. *)
Definition election_msg (m : raftpb.Message.t) : Prop :=
  m.(raftpb.Message.Type') = MsgHup ∨
  m.(raftpb.Message.Type') = MsgVote ∨
  m.(raftpb.Message.Type') = MsgVoteResp.

(** ** Model-level lemmas justifying each branch of [Step]

    Protocol facts, about [pstate.t]: the [Step] proof applies them to
    [to_pstate s].  (Before 2026-09-22 one record served both layers.) *)
Implicit Type ps : pstate.t.

(** The protocol reading of [vote_resp_result]. *)
Definition pvote_resp_result id (ps : pstate.t) (from : w64) (reject : bool)
  (won lost : bool) (ms : list msg.t) : pstate.t :=
  let s1 := ps <| pstate.votes := record_vote ps.(pstate.votes) from (negb reject) |> in
  if won then psend_msgs (pbecome_leader id s1) ms
  else if lost then pbecome_follower s1 s1.(pstate.term) (W64 0)
  else s1.

Lemma to_pstate_vote_resp_result id s from reject won lost ms :
  to_pstate (vote_resp_result id s from reject won lost ms)
  = pvote_resp_result id (to_pstate s) from reject won lost ms.
Proof.
  rewrite /vote_resp_result /pvote_resp_result.
  destruct won; [|destruct lost]; simpl.
  - rewrite to_pstate_send_msgs to_pstate_become_leader //.
  - rewrite to_pstate_become_follower //.
  - done.
Qed.

(** [vote_resp_result] keeps [nstate_wf]: every outcome is a [becomeX] or
    leaves [r.step] and the role alone, and none of them lends anything. *)
Lemma nstate_wf_vote_resp_result id s from reject won lost ms :
  nstate_wf s → nstate_wf (vote_resp_result id s from reject won lost ms).
Proof.
  intros [Hsf Hl]. rewrite /vote_resp_result.
  destruct won; [|destruct lost]; split; simpl; done.
Qed.

(** ** Branch lemmas

    These are pure facts about the protocol, independent of the program
    logic; the WP proofs below feed them to [own_raft_ghost_step]. *)

(** Dropping a message is always legal. *)
Lemma step_drop id (s : pstate.t) : step cfg id s [] s.
Proof. constructor. Qed.

(** Stepping down and then answering a vote request, in one protocol step. *)
Lemma step_stepdown_then_vote id (s : pstate.t) (m : msg.t) :
  m.(msg.ty) = mtype.Vote →
  m.(msg.to) = id →
  m.(msg.from) ≠ W64 0 →
  uint.Z s.(pstate.term) < uint.Z m.(msg.term) →
  step cfg id s ([m] ++ [m])
       (psend_msgs ((pbecome_follower s m.(msg.term) (W64 0))
                     <| pstate.vote := m.(msg.from) |>)
          [msg.mk mtype.VoteResp id m.(msg.from) m.(msg.term) false]).
Proof.
  intros Hty Hto Hfrom Hlt.
  eapply step_trans with
    (s₁ := pbecome_follower s m.(msg.term)
             (if from_leader m.(msg.ty) then m.(msg.from) else W64 0)).
  { by apply step_higher_term. }
  rewrite Hty /=.
  apply step_grant_vote; try done.
  (* [pbecome_follower] to a strictly greater term clears the vote and the
     leader, so [pcan_vote] holds. *)
  rewrite /pcan_vote /pbecome_follower /=.
  right. destruct (decide (m.(msg.term) = s.(pstate.term))) as [Heq|Hne].
  { rewrite Heq in Hlt. lia. }
  done.
Qed.

(** Stepping down and then declining. *)
Lemma step_stepdown_then_reject id (s : pstate.t) (m : msg.t) :
  m.(msg.ty) = mtype.Vote →
  m.(msg.to) = id →
  uint.Z s.(pstate.term) < uint.Z m.(msg.term) →
  step cfg id s ([m] ++ [m])
       (psend_msgs (pbecome_follower s m.(msg.term) (W64 0))
          [msg.mk mtype.VoteResp id m.(msg.from) m.(msg.term) true]).
Proof.
  intros Hty Hto Hlt.
  eapply step_trans with
    (s₁ := pbecome_follower s m.(msg.term)
             (if from_leader m.(msg.ty) then m.(msg.from) else W64 0)).
  { by apply step_higher_term. }
  rewrite Hty /=.
  by apply step_reject_vote.
Qed.

(** Recording a vote response and then winning. *)
Lemma step_record_then_win id (s : pstate.t) (m : msg.t) ms :
  m.(msg.ty) = mtype.VoteResp →
  m.(msg.to) = id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) = role.Candidate →
  let s1 := s <| pstate.votes :=
                  record_vote s.(pstate.votes) m.(msg.from) (negb m.(msg.reject)) |> in
  app_sends id s1.(pstate.term) ms →
  is_quorum cfg (granted s1.(pstate.votes)) →
  step cfg id s ([m] ++ []) (psend_msgs (pbecome_leader id s1) ms).
Proof.
  intros ???? s1 Hms Hq.
  eapply step_trans; [by apply step_record_vote|].
  by apply step_win.
Qed.

(** Recording a vote response and then losing. *)
Lemma step_record_then_lose id (s : pstate.t) (m : msg.t) :
  m.(msg.ty) = mtype.VoteResp →
  m.(msg.to) = id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) = role.Candidate →
  let s1 := s <| pstate.votes :=
                  record_vote s.(pstate.votes) m.(msg.from) (negb m.(msg.reject)) |> in
  ¬ is_quorum cfg (cfg ∖ rejected s1.(pstate.votes)) →
  step cfg id s ([m] ++ []) (pbecome_follower s1 s1.(pstate.term) (W64 0)).
Proof.
  intros ???? s1 Hq.
  eapply step_trans; [by apply step_record_vote|].
  by apply step_lose.
Qed.

End proof.
