(** Pure lemmas shared by [Step]'s [MsgApp] and [MsgHeartbeat] branches
    ([proof_raft__Step_MsgApp*.v], [proof_raft__Step_MsgHeartbeat*.v]).

    Proof structure, not specification: no [Module Type], no [Parameter],
    no Hoare triple.  Each lemma is about the result relations the [stepX]
    specs return ([follower_step_result], [candidate_step_result],
    [leader_step_result]) and the model rules they refine, and is proved
    here, outside any WP, where the [decide] chains are cheap to take
    apart.  Only files in this directory may [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__Step.

Section repl.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type s : nstate.t.

(** ** The model side

    [t] is the physical state the handler ([handleAppendEntries] /
    [handleHeartbeat]) starts in, after the node has adopted [m.From] as
    leader: [stepFollower]'s [r.lead = m.From], or [stepCandidate]'s /
    the term preamble's [becomeFollower(_, m.From)].  All three are
    [padopt_leader] of the protocol state before the adoption; the
    [stepX]-specific lemmas below establish that equation. *)

Lemma step_eq id (ps : pstate.t) recv (ps1 ps2 : pstate.t) :
  step cfg id ps recv ps1 → ps1 = ps2 → step cfg id ps recv ps2.
Proof. by intros ? <-. Qed.

(** [handle_app_result] refines [step_app_stale] / [step_app_accept] /
    [step_app_reject] at [ps]. *)
Lemma step_handle_app id (ps : pstate.t) t (m : raftpb.Message.t)
    (ents : list raftpb.Entry.t) s' :
  to_pstate t = padopt_leader ps m.(raftpb.Message.From') →
  m.(raftpb.Message.To') = id →
  m.(raftpb.Message.Term') = ps.(pstate.term) →
  ps.(pstate.role) ≠ role.Leader →
  (uint.Z ps.(pstate.commit) ≤ uint.Z m.(raftpb.Message.Index') →
   plog_matches ps.(pstate.base) ps.(pstate.log)
     (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) →
   plog_find_conflict ps.(pstate.base) ps.(pstate.log) ents = W64 0 ∨
   uint.Z ps.(pstate.commit) < uint.Z (plog_find_conflict ps.(pstate.base) ps.(pstate.log) ents)) →
  handle_app_result id t m ents s' →
  m.(raftpb.Message.From') ≠ id →
  step cfg id ps [abs_msg mtype.App m ents] (to_pstate s').
Proof.
  intros Ht Hto Hterm Hnl Hconf Hres Hfid.
  destruct ps as [pterm pvote plead prole pvotes pout pbase plog pcommit pmatched].
  rewrite /to_pstate /padopt_leader /= in Ht.
  injection Ht as Htm Hvt Hld Hrl Hvs Hout Hprev Hlog Hcm Hmt.
  simpl in *.
  rewrite /handle_app_result /= in Hres.
  destruct Hres as [[Hlt ->]|[[Hle (lastnewi & es' & ls' & Happ & Hprev' & Hes & _ & Hcm' & ->)]
                              |[Hle [Hnm (hint & hintterm & ->)]]]].
  - (* stale *)
    eapply step_eq.
    { apply (step_app_stale _ _ (abs_msg mtype.App m ents)); simpl; try done.
      rewrite -Hcm. exact Hlt. }
    rewrite /to_pstate /psend_msgs /send_msgs /padopt_leader /app_resp /abs_msg /abs_msg_from /=.
    rewrite Hmt Htm Hvt Hld Hrl Hvs Hout Hprev Hlog Hcm. done.
  - (* accept *)
    rewrite Hprev Hlog in Happ.
    assert (Hm : plog_matches pbase plog
                   (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index'))).
    { match goal with |- ?P => destruct (decide P) as [?|Hn]; [done|] end.
      revert Happ. rewrite /plog_maybe_append (decide_False _ _ Hn). by intros ?. }
    eapply step_eq.
    { apply (step_app_accept _ _ (abs_msg mtype.App m ents) _ lastnewi es'); simpl; try done.
      - rewrite -Hcm. exact Hle.
      - apply Hconf; [rewrite -Hcm; exact Hle|exact Hm]. }
    rewrite /to_pstate /psend_msgs /send_msgs /padopt_leader /app_resp /abs_msg /abs_msg_from /=.
    rewrite Hprev' Hes Hcm'.
    rewrite Hmt Htm Hvt Hld Hrl Hvs Hout Hprev Hcm. done.
  - (* reject *)
    rewrite Hprev Hlog in Hnm.
    eapply step_eq.
    { apply (step_app_reject _ _ (abs_msg mtype.App m ents) _ hint hintterm); simpl; try done.
      rewrite -Hcm. exact Hle. }
    rewrite /to_pstate /psend_msgs /send_msgs /padopt_leader /app_resp /abs_msg /abs_msg_from /=.
    rewrite Hmt Htm Hvt Hld Hrl Hvs Hout Hprev Hlog Hcm. done.
Qed.

(** [heartbeat_result] refines [step_heartbeat] at [ps]. *)
Lemma step_handle_heartbeat id (ps : pstate.t) t (m : raftpb.Message.t)
    (ents : list raftpb.Entry.t) :
  to_pstate t = padopt_leader ps m.(raftpb.Message.From') →
  m.(raftpb.Message.To') = id →
  m.(raftpb.Message.Term') = ps.(pstate.term) →
  ps.(pstate.role) ≠ role.Leader →
  uint.Z m.(raftpb.Message.Commit') ≤ plog_last_index_Z ps.(pstate.base) ps.(pstate.log) →
  m.(raftpb.Message.From') ≠ id →
  step cfg id ps [abs_msg mtype.Heartbeat m ents] (to_pstate (heartbeat_result id t m)).
Proof.
  intros Ht Hto Hterm Hnl Hc Hfid.
  destruct ps as [pterm pvote plead prole pvotes pout pbase plog pcommit pmatched].
  rewrite /to_pstate /padopt_leader /= in Ht.
  injection Ht as Htm Hvt Hld Hrl Hvs Hout Hprev Hlog Hcm Hmt.
  simpl in *.
  eapply step_eq.
  { apply (step_heartbeat _ _ (abs_msg mtype.Heartbeat m ents)); simpl; done. }
  rewrite /heartbeat_result /to_pstate /psend_msgs /send_msgs /padopt_leader
    /abs_msg /abs_msg_from /=.
  rewrite Hmt Htm Hvt Hld Hrl Hvs Hout Hprev Hlog Hcm. done.
Qed.

(** The term preamble's step-down for a message only a leader sends. *)
Lemma step_higher_term_leader id (ps : pstate.t) (ty : mtype.t)
    (m : raftpb.Message.t) (ents : list raftpb.Entry.t) :
  from_leader ty = true →
  uint.Z ps.(pstate.term) < uint.Z m.(raftpb.Message.Term') →
  m.(raftpb.Message.To') = id →
  m.(raftpb.Message.From') ≠ id →
  step cfg id ps [abs_msg ty m ents]
    (pbecome_follower ps m.(raftpb.Message.Term') m.(raftpb.Message.From')).
Proof.
  intros Hfl Hgt Hto Hfid.
  eapply step_eq.
  { apply (step_higher_term _ _ (abs_msg ty m ents)); [done|done|intros _; exact Hfid]. }
  rewrite /abs_msg /abs_msg_from /= Hfl //.
Qed.

(** ** The three adoptions are [padopt_leader] *)

(** After the term preamble's [becomeFollower(m.Term, m.From)], with
    [stepFollower]'s [r.lead = m.From] on top (a no-op there). *)
Lemma adopt_after_stepdown s (term from : w64) pvs :
  to_pstate (become_follower s term from <| nstate.prvals := pvs |>
               <| nstate.lead := from |>)
  = padopt_leader (pbecome_follower (to_pstate s) term from) from.
Proof. done. Qed.

(** [stepFollower]'s [r.lead = m.From] at the current term.  A follower's
    tally is empty -- [padopt_leader] clears it -- which [nstate.t] does not
    record by itself; it is the premise [Hvotes]. *)
Lemma adopt_follower s (from : w64) :
  s.(nstate.role) = prole.Follower →
  s.(nstate.votes) = ∅ →
  to_pstate (s <| nstate.lead := from |>) = padopt_leader (to_pstate s) from.
Proof.
  intros Hr Hv. rewrite /to_pstate /padopt_leader /= Hr Hv //.
Qed.

(** [stepCandidate]'s [becomeFollower(r.Term, m.From)]: the term does not
    move, so the vote is kept, and the tally is cleared. *)
Lemma adopt_candidate s (from : w64) pvs :
  to_pstate (become_follower s s.(nstate.term) from <| nstate.prvals := pvs |>)
  = padopt_leader (to_pstate s) from.
Proof.
  rewrite /to_pstate /padopt_leader /become_follower /reset_to /=.
  rewrite (decide_True _ _ (eq_refl s.(nstate.term))) //.
Qed.

(** ** Well-formedness is preserved by the handlers *)

Lemma nstate_wf_handle_app id t m ents s' :
  nstate_wf t → handle_app_result id t m ents s' → nstate_wf s'.
Proof.
  intros Hwf Hres. rewrite /handle_app_result in Hres. cbv zeta in Hres.
  destruct Hres as [[_ ->]|[[_ (? & ? & ? & _ & _ & _ & _ & _ & ->)]|[_ [_ (? & ? & ->)]]]]; done.
Qed.

Lemma nstate_wf_heartbeat_result id t m :
  nstate_wf t → nstate_wf (heartbeat_result id t m).
Proof. done. Qed.

(** ** Taking the [stepX] results apart, by type *)

Lemma follower_step_result_app id s m ents sv dropped s' :
  m.(raftpb.Message.Type') = MsgApp →
  follower_step_result id s m ents sv dropped s' →
  dropped = false ∧
  handle_app_result id (s <| nstate.lead := m.(raftpb.Message.From') |>) m ents s'.
Proof.
  intros Hty. rewrite /follower_step_result Hty.
  case_decide as H1; [exfalso; revert H1; w32_ne|].
  case_decide as H2; [exfalso; revert H2; w32_ne|].
  case_decide as H3; [done|]. done.
Qed.

Lemma follower_step_result_heartbeat id s m ents sv dropped s' :
  m.(raftpb.Message.Type') = MsgHeartbeat →
  follower_step_result id s m ents sv dropped s' →
  dropped = false ∧
  s' = heartbeat_result id (s <| nstate.lead := m.(raftpb.Message.From') |>) m.
Proof.
  intros Hty. rewrite /follower_step_result Hty.
  case_decide as H1; [exfalso; revert H1; w32_ne|].
  case_decide as H2; [exfalso; revert H2; w32_ne|].
  case_decide as H3; [exfalso; revert H3; w32_ne|].
  case_decide as H4; [done|]. done.
Qed.

Lemma candidate_step_result_app id s m ents sv dropped s' :
  m.(raftpb.Message.Type') = MsgApp →
  candidate_step_result cfg id s m ents sv dropped s' →
  dropped = false ∧
  ∃ pvs, handle_app_result id
           (become_follower s s.(nstate.term) m.(raftpb.Message.From')
              <| nstate.prvals := pvs |>) m ents s'.
Proof.
  intros Hty. rewrite /candidate_step_result Hty.
  case_decide as H1; [exfalso; revert H1; w32_ne|].
  case_decide as H2; [exfalso; revert H2; w32_ne|].
  case_decide as H3; [done|]. done.
Qed.

Lemma candidate_step_result_heartbeat id s m ents sv dropped s' :
  m.(raftpb.Message.Type') = MsgHeartbeat →
  candidate_step_result cfg id s m ents sv dropped s' →
  dropped = false ∧
  ∃ pvs, s' = heartbeat_result id
                (become_follower s s.(nstate.term) m.(raftpb.Message.From')
                   <| nstate.prvals := pvs |>) m.
Proof.
  intros Hty. rewrite /candidate_step_result Hty.
  case_decide as H1; [exfalso; revert H1; w32_ne|].
  case_decide as H2; [exfalso; revert H2; w32_ne|].
  case_decide as H3; [exfalso; revert H3; w32_ne|].
  case_decide as H4; [done|]. done.
Qed.

(** A leader ignores a [MsgApp] or [MsgHeartbeat] of its own term. *)
Lemma leader_step_result_app_hb id s m ents dropped s' :
  m.(raftpb.Message.Type') = MsgApp ∨ m.(raftpb.Message.Type') = MsgHeartbeat →
  leader_step_result cfg id s m ents dropped s' →
  dropped = false ∧ s' = s.
Proof.
  intros Hty. rewrite /leader_step_result.
  case_decide as H1.
  { exfalso. destruct Hty as [Hty|Hty]; rewrite Hty in H1; revert H1; w32_ne. }
  intros [-> Hres]. split; first done.
  destruct Hres as [[_ ->]|[[Hc _]|[[Hc _]|[Hc _]]]]; first done;
    exfalso; destruct Hty as [Hty|Hty]; rewrite Hty in Hc; revert Hc; w32_ne.
Qed.

(** ** Snapshots (2026-10-02)

    [handle_snap_result] at the adopted state [t] refines the three
    [step_snap_*] rules at [ps]; the term preamble's step-down for a
    [MsgSnap] is [step_higher_term] at [abs_snap]. *)
Lemma step_handle_snap id (ps : pstate.t) t (m : raftpb.Message.t)
    (sv : raftpb.Snapshot.t) (voters : list w64) s' :
  to_pstate t = padopt_leader ps m.(raftpb.Message.From') →
  m.(raftpb.Message.To') = id →
  m.(raftpb.Message.Term') = ps.(pstate.term) →
  ps.(pstate.role) ≠ role.Leader →
  m.(raftpb.Message.From') ≠ id →
  snap_scope cfg sv voters →
  id ∈ cfg →
  handle_snap_result id t m sv s' →
  step cfg id ps [abs_snap m sv voters] (to_pstate s').
Proof.
  intros Ht Hto Hterm Hnl Hfid Hscope Hin Hres.
  destruct Hscope as (Hperm & _).
  destruct ps as [pterm pvote plead prole pvotes pout pbase plog pcommit pmatched].
  rewrite /to_pstate /padopt_leader /= in Ht.
  injection Ht as Htm Hvt Hld Hrl Hvs Hout Hprev Hlog Hcm Hmt.
  simpl in *.
  rewrite /handle_snap_result /= in Hres.
  destruct Hres as [[Hle ->]|[[Hlt [Hm ->]]|[Hlt [Hnm (prs & pvs & ->)]]]].
  - (* obsolete *)
    eapply step_eq.
    { apply (step_snap_stale _ _ (abs_snap m sv voters)); simpl; try done.
      rewrite -Hcm. exact Hle. }
    rewrite /to_pstate /psend_msgs /send_msgs /padopt_leader /app_resp
      /abs_snap /abs_snap_from /=.
    rewrite Hmt Htm Hvt Hld Hrl Hvs Hout Hprev Hlog Hcm. done.
  - (* fast-forward *)
    rewrite Hprev Hlog in Hm.
    eapply step_eq.
    { apply (step_snap_fastfwd _ _ (abs_snap m sv voters)); simpl; try done.
      rewrite -Hcm. exact Hlt. }
    rewrite /to_pstate /psend_msgs /send_msgs /padopt_leader /app_resp
      /abs_snap /abs_snap_from /=.
    destruct (decide (t.(nstate.role) = prole.Leader)) as [Hd|Hd];
      [exfalso; rewrite Hd in Hrl; discriminate Hrl|].
    rewrite Htm Hvt Hld Hrl Hvs Hout Hprev Hlog. done.
  - (* restore *)
    rewrite Hprev Hlog in Hnm.
    eapply step_eq.
    { apply (step_snap_restore _ _ (abs_snap m sv voters)); simpl; try done.
      rewrite -Hcm. exact Hlt. }
    rewrite /to_pstate /psend_msgs /send_msgs /padopt_leader /app_resp
      /abs_snap /abs_snap_from /log_restore /snap_id /=.
    destruct (decide (t.(nstate.role) = prole.Leader)) as [Hd|Hd];
      [exfalso; rewrite Hd in Hrl; discriminate Hrl|].
    rewrite Htm Hvt Hld Hrl Hvs Hout. done.
Qed.

Lemma step_higher_term_snap id (ps : pstate.t) (m : raftpb.Message.t)
    (sv : raftpb.Snapshot.t) (voters : list w64) :
  uint.Z ps.(pstate.term) < uint.Z m.(raftpb.Message.Term') →
  m.(raftpb.Message.To') = id →
  m.(raftpb.Message.From') ≠ id →
  step cfg id ps [abs_snap m sv voters]
    (pbecome_follower ps m.(raftpb.Message.Term') m.(raftpb.Message.From')).
Proof.
  intros Hgt Hto Hfid.
  eapply step_eq.
  { apply (step_higher_term _ _ (abs_snap m sv voters)); [done|done|intros _; exact Hfid]. }
  rewrite /abs_snap /abs_snap_from /= //.
Qed.

Lemma nstate_wf_handle_snap id t m sv s' :
  nstate_wf t → handle_snap_result id t m sv s' → nstate_wf s'.
Proof.
  intros Hwf Hres. rewrite /handle_snap_result in Hres. cbv zeta in Hres.
  destruct Hres as [[_ ->]|[[_ [_ ->]]|[_ [_ (? & ? & ->)]]]]; done.
Qed.

Lemma follower_step_result_snap id s m ents sv dropped s' :
  m.(raftpb.Message.Type') = MsgSnap →
  follower_step_result id s m ents sv dropped s' →
  dropped = false ∧
  handle_snap_result id (s <| nstate.lead := m.(raftpb.Message.From') |>) m sv s'.
Proof.
  intros Hty. rewrite /follower_step_result Hty.
  case_decide as H1; [exfalso; revert H1; w32_ne|].
  case_decide as H2; [exfalso; revert H2; w32_ne|].
  case_decide as H3; [exfalso; revert H3; w32_ne|].
  case_decide as H4; [exfalso; revert H4; w32_ne|].
  case_decide as H5; [exfalso; destruct H5 as [H5|[H5|H5]]; revert H5; w32_ne|].
  case_decide as H6; done.
Qed.

Lemma candidate_step_result_snap id s m ents sv dropped s' :
  m.(raftpb.Message.Type') = MsgSnap →
  candidate_step_result cfg id s m ents sv dropped s' →
  dropped = false ∧
  ∃ pvs, handle_snap_result id
           (become_follower s s.(nstate.term) m.(raftpb.Message.From')
              <| nstate.prvals := pvs |>) m sv s'.
Proof.
  intros Hty. rewrite /candidate_step_result Hty.
  case_decide as H1; [exfalso; revert H1; w32_ne|].
  case_decide as H2; [exfalso; revert H2; w32_ne|].
  case_decide as H3; [exfalso; revert H3; w32_ne|].
  case_decide as H4; [exfalso; revert H4; w32_ne|].
  case_decide as H5; [exfalso; destruct H5 as [H5|[H5|H5]]; revert H5; w32_ne|].
  case_decide as H6; done.
Qed.

End repl.
