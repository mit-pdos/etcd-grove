(** Pure lemmas shared by [Step]'s [MsgAppResp], [MsgHeartbeatResp] and
    [MsgBeat] branches: what the three [stepX] result relations say for
    those three types, turned into the [step] witness [Step] needs.  Proof
    structure, not specification: no [Module Type], no [Parameter]; only
    files in this directory may [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__Step.

Section resp_lemmas.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type s : nstate.t.

(** Close every arm of a result relation's [if decide (Type = …)] chain
    whose test contradicts [Hty] (a disjunction of type equations). *)
Local Ltac kill_type_arms Hty :=
  repeat (let Hd := fresh "Hd" in
          case_decide as Hd;
          [ try (exfalso; destruct Hty as [Hty|[Hty|Hty]]; rewrite Hty in Hd;
                 revert Hd; w32_ne) | ]).

(** [MsgBeat], [MsgAppResp] and [MsgHeartbeatResp] reach no arm of
    [stepFollower]. *)
Lemma follower_step_result_noop id s m ents sv dropped s' :
  m.(raftpb.Message.Type') = MsgBeat ∨ m.(raftpb.Message.Type') = MsgAppResp ∨
  m.(raftpb.Message.Type') = MsgHeartbeatResp →
  follower_step_result id s m ents sv dropped s' → dropped = false ∧ s' = s.
Proof.
  intros Hty. rewrite /follower_step_result.
  kill_type_arms Hty.
  all: try (intros H; exact H).
  all: try (intros []).
Qed.

(** Nor of [stepCandidate]. *)
Lemma candidate_step_result_noop id s m ents sv dropped s' :
  m.(raftpb.Message.Type') = MsgBeat ∨ m.(raftpb.Message.Type') = MsgAppResp ∨
  m.(raftpb.Message.Type') = MsgHeartbeatResp →
  candidate_step_result cfg id s m ents sv dropped s' → dropped = false ∧ s' = s.
Proof.
  intros Hty. rewrite /candidate_step_result.
  kill_type_arms Hty.
  all: try (intros H; exact H).
  all: try (intros []).
Qed.

(** [stepLeader] on [MsgBeat]: the heartbeats are [step_beat]'s. *)
Lemma leader_beat_step id s m ents dropped s' :
  s.(nstate.role) = role.Leader →
  m.(raftpb.Message.Type') = MsgBeat →
  nstate_wf s →
  leader_step_result cfg id s m ents dropped s' →
  dropped = false ∧ nstate_wf s' ∧ step cfg id (to_pstate s) [] (to_pstate s').
Proof.
  intros Hr Hty Hwf.
  rewrite /leader_step_result decide_False;
    last (rewrite Hty /MsgBeat /MsgProp; w32_ne).
  intros [-> Hres]. split; first done.
  destruct Hres as [[Hc _]|[[_ Hb]|[[Hc _]|[Hc _]]]].
  - exfalso. rewrite Hty in Hc. destruct Hc as [Hc|[Hc|Hc]]; revert Hc; w32_ne.
  - destruct Hb as (ms & pvs & -> & Hok & Hpm).
    split; first exact Hwf.
    rewrite to_pstate_prvals; last (intros _; exact Hpm).
    rewrite to_pstate_send_msgs.
    apply step_beat; [exact Hr|exact Hok].
  - exfalso. rewrite Hty in Hc. revert Hc. w32_ne.
  - exfalso. rewrite Hty in Hc. revert Hc. w32_ne.
Qed.

(** [stepLeader] on [MsgHeartbeatResp]: [sendAppend]'s messages, no [Match]
    moved -- [step_send_apps]. *)
Lemma leader_hbresp_step id s m ents dropped s' :
  s.(nstate.role) = role.Leader →
  m.(raftpb.Message.Type') = MsgHeartbeatResp →
  nstate_wf s →
  leader_step_result cfg id s m ents dropped s' →
  dropped = false ∧ nstate_wf s' ∧ step cfg id (to_pstate s) [] (to_pstate s').
Proof.
  intros Hr Hty Hwf.
  rewrite /leader_step_result decide_False;
    last (rewrite Hty /MsgHeartbeatResp /MsgProp; w32_ne).
  intros [-> Hres]. split; first done.
  destruct Hres as [[Hc _]|[[Hc _]|[[_ Hb]|[Hc _]]]].
  - exfalso. rewrite Hty in Hc. destruct Hc as [Hc|[Hc|Hc]]; revert Hc; w32_ne.
  - exfalso. rewrite Hty in Hc. revert Hc. w32_ne.
  - destruct Hb as (ms & pvs & -> & Hok & Hpm).
    split; first exact Hwf.
    rewrite to_pstate_prvals; last (intros _; exact Hpm).
    rewrite to_pstate_send_msgs.
    apply step_send_apps; [exact Hr|exact Hok].
  - exfalso. rewrite Hty in Hc. revert Hc. w32_ne.
Qed.

(** A leader's [matched] is its [Progress] values' [Match]. *)
Local Lemma to_pstate_matched_leader s :
  s.(nstate.role) = role.Leader →
  (to_pstate s).(pstate.matched) = prvals_match s.(nstate.prvals).
Proof.
  intros Hr. rewrite /to_pstate.
  case_decide as Hd; [reflexivity|exfalso; apply Hd; exact Hr].
Qed.

(** New [Progress] values at a leader: only [matched] moves. *)
Local Lemma to_pstate_prvals_leader s pvs :
  s.(nstate.role) = role.Leader →
  to_pstate (s <| nstate.prvals := pvs |>)
  = to_pstate s <| pstate.matched := prvals_match pvs |>.
Proof.
  intros Hr. rewrite /to_pstate.
  repeat (let Hd := fresh "Hd" in
          case_decide as Hd; [|exfalso; apply Hd; exact Hr]).
  reflexivity.
Qed.

(** A protocol state with its commit index set to what it already is. *)
Local Lemma pstate_commit_same (ps : pstate.t) :
  ps <| pstate.commit := ps.(pstate.commit) |> = ps.
Proof. by destruct ps. Qed.

(** [stepLeader] on [MsgAppResp] of the current term:

    - no [Progress] for the sender: nothing changes, [step_refl];
    - rejected: [Next] moves, [Match] does not, and the retries are
      [repl_sends] -- [step_send_apps] alone;
    - accepted: [step_app_resp] (the sender's [Match] raised, which is
      [to_pstate] at the new [Progress] values), then [step_commit] if
      [maybeCommit] moved the commit index ([commit_ok] is its premises,
      judged at the raised [Match] map), then [step_send_apps] for what
      was sent after the commit. *)
Lemma leader_appresp_step id s m ents0 ents dropped s' :
  s.(nstate.role) = role.Leader →
  m.(raftpb.Message.Type') = MsgAppResp →
  m.(raftpb.Message.To') = id →
  m.(raftpb.Message.Term') = s.(nstate.term) →
  nstate_wf s →
  leader_step_result cfg id s m ents0 dropped s' →
  dropped = false ∧ nstate_wf s' ∧
  ∃ recv, (∀ m', m' ∈ recv → m' = abs_msg mtype.AppResp m ents) ∧
          step cfg id (to_pstate s) recv (to_pstate s').
Proof.
  intros Hr Hty Hto Hteq Hwf.
  rewrite /leader_step_result decide_False;
    last (rewrite Hty /MsgAppResp /MsgProp; w32_ne).
  intros [-> Hres]. split; first done.
  destruct Hres as [[Hc _]|[[Hc _]|[[Hc _]|[_ Hres]]]].
  { exfalso. rewrite Hty in Hc. destruct Hc as [Hc|[Hc|Hc]]; revert Hc; w32_ne. }
  { exfalso. rewrite Hty in Hc. revert Hc. w32_ne. }
  { exfalso. rewrite Hty in Hc. revert Hc. w32_ne. }
  destruct Hres as [[_ ->]|[(_ & _ & Hb)|(_ & Hrej & Hacc)]].
  - (* no [Progress] for the sender *)
    split; first exact Hwf.
    exists []. split; last apply step_refl.
    intros ? Hin. by apply elem_of_nil in Hin.
  - (* rejected *)
    destruct Hb as (ms & pvs & -> & Hok & Hpm).
    split; first exact Hwf.
    exists []. split.
    { intros ? Hin. by apply elem_of_nil in Hin. }
    rewrite to_pstate_prvals; last (intros _; exact Hpm).
    rewrite to_pstate_send_msgs.
    apply step_send_apps; [exact Hr|exact Hok].
  - (* accepted *)
    destruct Hacc as (x & pvs & c & ms & Hx & Hpvs & Hc & Hms & ->).
    split; first exact Hwf.
    set (P1 := to_pstate (s <| nstate.prvals := pvs |>)).
    assert (step cfg id (to_pstate s) [abs_msg mtype.AppResp m ents] P1) as H1.
    { rewrite /P1 to_pstate_prvals_leader; last exact Hr.
      rewrite Hpvs -(to_pstate_matched_leader s Hr).
      replace (m.(raftpb.Message.From'))
        with (abs_msg mtype.AppResp m ents).(msg.from) by done.
      replace (m.(raftpb.Message.Index'))
        with (abs_msg mtype.AppResp m ents).(msg.index) by done.
      apply step_app_resp.
      - done.
      - exact Hto.
      - exact Hteq.
      - exact Hr.
      - exact Hrej.
      - rewrite (to_pstate_matched_leader s Hr). exact Hx. }
    assert (step cfg id P1 [] (P1 <| pstate.commit := c |>)) as H2.
    { destruct Hc as [->|(Hlt & Hle & Hterm & Hq)].
      - assert (P1 <| pstate.commit := s.(nstate.logst).(logstate.committed) |> = P1)
          as -> by apply (pstate_commit_same P1).
        apply step_refl.
      - apply step_commit; [exact Hr|exact Hlt|exact Hle|exact Hterm|exact Hq]. }
    assert (step cfg id (P1 <| pstate.commit := c |>) []
              (psend_msgs (P1 <| pstate.commit := c |>) ms)) as H3.
    { apply step_send_apps; first exact Hr.
      eapply Forall_impl; last exact Hms.
      intros m' Hm'. eapply repl_ok_proper; [..|exact Hm']; reflexivity. }
    exists ([abs_msg mtype.AppResp m ents] ++ ([] ++ [])). split.
    { intros ? Hin. rewrite !elem_of_app list_elem_of_singleton elem_of_nil in Hin.
      naive_solver. }
    eapply step_trans; first exact H1.
    eapply step_trans; first exact H2.
    exact H3.
Qed.

End resp_lemmas.
