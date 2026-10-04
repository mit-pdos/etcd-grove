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
    [become_leader] includes [appendEntry]'s self-acknowledgement.

    [ms] is whatever [repl_sends] allows rather than one [App] per peer,
    matching [step_win] — see the comment there for why the exact broadcast
    is not pinned down. *)
Definition vote_resp_result id s (from : w64) (reject : bool) (won lost : bool)
  (ms : list msg.t) : nstate.t :=
  let s1 := s <| nstate.votes := record_vote s.(nstate.votes) from (negb reject) |> in
  if won then send_msgs (become_leader id s1) ms
  else if lost then become_follower s1 s1.(nstate.term) (W64 0)
  else s1.

(** The outcome of feeding a [MsgPreVoteResp] to a pre-candidate
    ([stepCandidate] in [StatePreCandidate]): the tally records it, then
    a win starts the real election ([campaign(campaignElection)], whose
    requests go to [peers]), a loss is [becomeFollower(r.Term, None)], and
    otherwise nothing.  The pre-vote tally is invisible to the protocol
    ([to_pstate]). *)
Definition prevote_resp_result id s (from : w64) (reject : bool) (won lost : bool)
  (peers : list w64) : nstate.t :=
  let s1 := s <| nstate.votes := record_vote s.(nstate.votes) from (negb reject) |> in
  if won then campaign_state id s1 false peers
  else if lost then become_follower s1 s1.(nstate.term) (W64 0)
  else s1.


(** ** Model-level lemmas justifying each branch of [Step]

    Protocol facts, about [pstate.t]: the [Step] proof applies them to
    [to_pstate s].  (Before 2026-09-22 one record served both layers.) *)
Implicit Type ps : pstate.t.

(** The protocol reading of [vote_resp_result], with the new leader's
    [Match] values [mt]. *)
Definition pvote_resp_result id (ps : pstate.t) (from : w64) (reject : bool)
  (won lost : bool) (mt : gmap w64 w64) (ms : list msg.t) : pstate.t :=
  let s1 := ps <| pstate.votes := record_vote ps.(pstate.votes) from (negb reject) |> in
  if won then psend_msgs (pwin_state id s1 mt) ([pself_ack id (pwin_state id s1 mt)] ++ ms)
  else if lost then pbecome_follower s1 s1.(pstate.term) (W64 0)
  else s1.

(** A candidate's outcome, with whatever [Progress] values the code left:
    [Match] is visible only if it won. *)
Lemma to_pstate_vote_resp_result id s from reject won lost ms pvs :
  s.(nstate.role) = prole.Candidate →
  to_pstate (vote_resp_result id s from reject won lost ms <| nstate.prvals := pvs |>)
  = pvote_resp_result id (to_pstate s) from reject won lost (prvals_match pvs) ms.
Proof.
  intros Hrc. rewrite /vote_resp_result /pvote_resp_result.
  assert (Hr : s.(nstate.role) ≠ prole.Leader) by (rewrite Hrc; discriminate).
  assert (Hnp : s.(nstate.role) ≠ prole.PreCandidate) by (rewrite Hrc; discriminate).
  set (s1 := s <| nstate.votes := record_vote s.(nstate.votes) from (negb reject) |>).
  set (ps1 := to_pstate s <| pstate.votes :=
                record_vote (to_pstate s).(pstate.votes) from (negb reject) |>).
  assert (Hps1 : to_pstate s1 = ps1).
  { rewrite /s1 /ps1 to_pstate_votes; last exact Hnp.
    rewrite to_pstate_votes_nonpre //. }
  destruct won; [|destruct lost].
  - change (to_pstate (send_msgs (become_leader id s1 <| nstate.prvals := pvs |>) ms)
            = psend_msgs (pwin_state id ps1 (prvals_match pvs))
                ([pself_ack id (pwin_state id ps1 (prvals_match pvs))] ++ ms)).
    rewrite to_pstate_send_msgs to_pstate_become_leader Hps1.
    rewrite /psend_msgs /= -app_assoc //.
  - change (to_pstate (become_follower s1 s1.(nstate.term) (W64 0) <| nstate.prvals := pvs |>)
            = pbecome_follower ps1 ps1.(pstate.term) (W64 0)).
    rewrite to_pstate_prvals_nl; last done.
    rewrite to_pstate_become_follower Hps1 //.
  - change (to_pstate (s1 <| nstate.prvals := pvs |>) = ps1).
    rewrite to_pstate_prvals_nl; last done. done.
Qed.

(** [vote_resp_result] keeps [nstate_wf]: every outcome is a [becomeX] or
    leaves [r.step] and the role alone. *)
Lemma nstate_wf_vote_resp_result id s from reject won lost ms :
  nstate_wf s → nstate_wf (vote_resp_result id s from reject won lost ms).
Proof.
  intros Hsf. rewrite /vote_resp_result.
  destruct won; [|destruct lost]; simpl; done.
Qed.

Lemma nstate_wf_campaign_state id s pre peers :
  nstate_wf (campaign_state id s pre peers).
Proof. rewrite /campaign_state. destruct pre; done. Qed.

Lemma nstate_wf_prevote_resp_result id s from reject won lost peers :
  nstate_wf s → nstate_wf (prevote_resp_result id s from reject won lost peers).
Proof.
  intros Hsf. rewrite /prevote_resp_result.
  destruct won; [apply nstate_wf_campaign_state|destruct lost]; simpl; done.
Qed.

(** ** Branch lemmas

    These are pure facts about the protocol, independent of the program
    logic; the WP proofs below feed them to [own_raft_ghost_step]. *)

(** Dropping a message is always legal. *)
Lemma step_drop id (s : pstate.t) : step cfg id s [] s.
Proof. constructor. Qed.

(** Sending pre-vote messages from oneself, one [step_send_free] each. *)
Lemma step_send_frees id (ps : pstate.t) (ms : list msg.t) :
  Forall (λ m, (m.(msg.ty) = mtype.PreVote ∨ m.(msg.ty) = mtype.PreVoteResp) ∧
               m.(msg.from) = id) ms →
  step cfg id ps [] (psend_msgs ps ms).
Proof.
  induction ms as [|m ms IH] using rev_ind; intros Hms.
  - rewrite /psend_msgs app_nil_r. destruct ps. apply step_refl.
  - apply Forall_app in Hms as [Hms Hm]. apply Forall_singleton in Hm as [Hty Hfrom].
    assert (psend_msgs ps (ms ++ [m]) = psend_msgs (psend_msgs ps ms) [m]) as ->.
    { rewrite /psend_msgs /= app_assoc //. }
    eapply (step_trans cfg id _ [] _ [] _); [by apply IH|].
    by apply step_send_free.
Qed.

(** [campaign(t)] from a non-leader: an election is [step_campaign]; a
    pre-election is [step_abandon] ([becomePreCandidate]) followed by its
    [MsgPreVote]s and the self-addressed [MsgPreVoteResp], all free. *)
Lemma step_campaign_state id s pre peers pvs :
  s.(nstate.role) ≠ prole.Leader →
  id ∈ cfg →
  uint.Z s.(nstate.term) + 1 < 2 ^ 64 →
  peers ≡ₚ elements (cfg ∖ {[id]}) →
  step cfg id (to_pstate s) [] (to_pstate (campaign_state id s pre peers <| nstate.prvals := pvs |>)).
Proof.
  intros Hnl Hin Hnw Hperm.
  rewrite to_pstate_prvals_nl; last (rewrite /campaign_state; destruct pre; done).
  rewrite /campaign_state. destruct pre.
  - rewrite to_pstate_send_msgs to_pstate_become_precandidate.
    eapply (step_trans cfg id _ [] _ [] _).
    { apply step_abandon. rewrite to_pstate_role. by apply prole_role_not_leader. }
    apply step_send_frees. apply Forall_app. split.
    + apply Forall_singleton. split; [by right|done].
    + apply Forall_fmap, Forall_forall. intros to _. split; [by left|done].
  - rewrite to_pstate_send_msgs to_pstate_become_candidate.
    apply (step_campaign cfg id (to_pstate s) peers); [|done..].
    rewrite to_pstate_role. by apply prole_role_not_leader.
Qed.

(** A pre-candidate's [MsgPreVoteResp]: pending is nothing, a loss is
    [step_abandon], a win is [step_campaign]. *)
Lemma step_prevote_resp_result id s from reject won lost peers pvs :
  s.(nstate.role) = prole.PreCandidate →
  id ∈ cfg →
  uint.Z s.(nstate.term) + 1 < 2 ^ 64 →
  (won = true → peers ≡ₚ elements (cfg ∖ {[id]})) →
  step cfg id (to_pstate s) []
    (to_pstate (prevote_resp_result id s from reject won lost peers <| nstate.prvals := pvs |>)).
Proof.
  intros Hpre Hin Hnw Hperm. rewrite /prevote_resp_result.
  set (s1 := s <| nstate.votes := record_vote s.(nstate.votes) from (negb reject) |>).
  assert (Hs1 : to_pstate s1 = to_pstate s) by (apply to_pstate_votes_pre; exact Hpre).
  destruct won; [|destruct lost].
  - rewrite -Hs1. apply step_campaign_state; [|done|done|by apply Hperm].
    rewrite /s1 /= Hpre. discriminate.
  - rewrite to_pstate_prvals_nl; last done.
    rewrite to_pstate_become_follower Hs1.
    apply step_abandon. rewrite to_pstate_role Hpre. discriminate.
  - rewrite to_pstate_prvals_nl; last (rewrite /s1 /= Hpre; discriminate).
    rewrite Hs1. apply step_refl.
Qed.

(** Stepping down and then answering a vote request, in one protocol step. *)
Lemma step_stepdown_then_vote id (s : pstate.t) (m : msg.t) :
  m.(msg.ty) = mtype.Vote →
  m.(msg.to) = id →
  m.(msg.from) ≠ W64 0 →
  uint.Z s.(pstate.term) < uint.Z m.(msg.term) →
  plog_up_to_date s.(pstate.base) s.(pstate.log)
    (raft.entryID.mk m.(msg.logterm) m.(msg.index)) = true →
  step cfg id s ([m] ++ [m])
       (psend_msgs ((pbecome_follower s m.(msg.term) (W64 0))
                     <| pstate.vote := m.(msg.from) |>)
          [msg.plain mtype.VoteResp id m.(msg.from) m.(msg.term) false]).
Proof.
  intros Hty Hto Hfrom Hlt Hutd.
  eapply step_trans with
    (s₁ := pbecome_follower s m.(msg.term)
             (if from_leader m.(msg.ty) then m.(msg.from) else W64 0)).
  { apply step_higher_term; [done|done|]. rewrite Hty /=. by intros [=]. }
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
          [msg.plain mtype.VoteResp id m.(msg.from) m.(msg.term) true]).
Proof.
  intros Hty Hto Hlt.
  eapply step_trans with
    (s₁ := pbecome_follower s m.(msg.term)
             (if from_leader m.(msg.ty) then m.(msg.from) else W64 0)).
  { apply step_higher_term; [done|done|]. rewrite Hty /=. by intros [=]. }
  rewrite Hty /=.
  by apply step_reject_vote.
Qed.

(** Recording a vote response and then winning. *)
Lemma step_record_then_win id (s : pstate.t) (m : msg.t) mt ms :
  m.(msg.ty) = mtype.VoteResp →
  m.(msg.to) = id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) = role.Candidate →
  let s1 := s <| pstate.votes :=
                  record_vote s.(pstate.votes) m.(msg.from) (negb m.(msg.reject)) |> in
  leader_match_ok id s1 mt →
  Forall (repl_ok id (pwin_state id s1 mt)) ms →
  is_quorum cfg (granted s1.(pstate.votes)) →
  step cfg id s ([m] ++ [])
       (psend_msgs (pwin_state id s1 mt) ([pself_ack id (pwin_state id s1 mt)] ++ ms)).
Proof.
  intros ???? s1 Hmt Hms Hq.
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
