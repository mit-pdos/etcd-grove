Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__send.

Module SendProof (P : SEND_POSTULATES) : SEND.
Import P.

(** [defs.v] has the [msgsAfterAppend] half of this; a hidden message can
    also go on [msgs] (a [MsgSnap], a forwarded [MsgProp]). *)
Lemma abs_outbox_snoc_msgs_None (msgs msgsAA : list raftpb.Message.t) m :
  mtype_of m.(raftpb.Message.Type') = None →
  abs_outbox (msgs ++ [m]) msgsAA = abs_outbox msgs msgsAA.
Proof.
  intros Hty. rewrite /abs_outbox omap_app /= /abs_msg_opt Hty /=.
  by rewrite app_nil_r.
Qed.

(** What [mtype_of t = None] says about the four types the model sees. *)
Lemma mtype_of_None_ne (t : w32) :
  mtype_of t = None →
  t ≠ MsgVote ∧ t ≠ MsgVoteResp ∧ t ≠ MsgApp ∧ t ≠ MsgHeartbeat.
Proof.
  rewrite /mtype_of.
  repeat (case_decide; [discriminate|]). auto.
Qed.

  (** The common tail once the routing decision has been made: build the
      one-element slice literal, append it to the queue, trace, and open the
      postcondition's [own_raft_phys].  The [iExists] with the new queue and
      the pure outbox obligation are left to the caller -- an [Ltac] body
      cannot mention [rv]/[msgs] inside the record-update notation. *)
  Local Ltac send_tail_msgs :=
    wp_apply wp_slice_literal; iSplitR; first done;
    iIntros "%m_sl [m_sl _]";
    replace (sint.nat (W64 0)) with 0%nat by done;
    rewrite /go.array_literal_size /= /Z.max /= /Z.add /=;
    wp_auto;
    wp_apply (wp_slice_append with "[$Hmsgs $Hmsgs_cap $m_sl]")
      as "%msgs' (Hmsgs & Hmsgs_cap & _)";
    wp_apply (wp_traceSendMessage with "[$Hmisc]") as "Hmisc";
    iApply "HΦ"; rewrite /own_raft_phys.

  Local Ltac send_tail_msgsAA :=
    wp_apply wp_slice_literal; iSplitR; first done;
    iIntros "%m_sl [m_sl _]";
    replace (sint.nat (W64 0)) with 0%nat by done;
    rewrite /go.array_literal_size /= /Z.max /= /Z.add /=;
    wp_auto;
    wp_apply (wp_slice_append with "[$HmsgsAA $HmsgsAA_cap $m_sl]")
      as "%msgsAA' (HmsgsAA & HmsgsAA_cap & _)";
    wp_apply (wp_traceSendMessage with "[$Hmisc]") as "Hmisc";
    iApply "HΦ"; rewrite /own_raft_phys.

  Lemma wp_raft__send : wp_raft__send_body.
  Proof.
    intros_ambient.
    intros cfg r id s m out Hfrom Hok.
    wp_start as "@". iNamed "Hphys". wp_auto.
    (* [From] is unset, so [send] fills it in with [r.id]. *)
    rewrite Hfrom bool_decide_eq_true_2 //. wp_auto. rewrite Hid.
    destruct Hok as [(ty & Hvoty & Hty & Hmterm & Hself & ->)
                    |[(ty & Hlty & Hty & Hmterm & Hself & ->)
                     |(Hty & HnPV & HnPVR & Hmterm & Hself & ->)]].
    - (* (a) a vote message: [Term] is kept.  [MsgVote] goes onto [r.msgs],
         [MsgVoteResp] onto [r.msgsAfterAppend]; either way the abstract
         outbox grows by exactly that message -- up to permutation, since a
         [MsgVote] lands in front of whatever [msgsAfterAppend] holds. *)
      destruct Hvoty as [Hvt|Hvt].
      + (* [MsgVote] is not a response, so it goes onto [r.msgs]. *)
        rewrite Hvt /MsgVote bool_decide_eq_true_2 //. wp_auto.
        rewrite bool_decide_eq_false_2 //. wp_auto.
        (* [MsgVote] is none of the response types *)
        rewrite Hvt /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
        rewrite Hvt /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
        rewrite Hvt /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
        (* not self-addressed *)
        rewrite Hid bool_decide_eq_false_2; last exact (Hself Hvt). wp_auto.
        send_tail_msgs.
        iExists (rv <| raft.raft.msgs' := msgs' |>),
                (msgs ++ [m <| raftpb.Message.From' := id |>]), msgsAA, lok.
        iFrame "∗#%". iPureIntro.
        rewrite (abs_outbox_snoc_msgs _ _ _ ty) //= /send_msgs /=.
        by rewrite Houtbox.
      + (* [MsgVoteResp] is a response, so it goes onto [r.msgsAfterAppend]. *)
        rewrite Hvt /MsgVoteResp bool_decide_eq_false_2; last w32_ne.
        wp_auto.
        rewrite Hvt /MsgVoteResp bool_decide_eq_true_2 //. wp_auto.
        rewrite bool_decide_eq_false_2 //. wp_auto.
        rewrite Hvt /MsgVoteResp bool_decide_eq_false_2; last w32_ne.
        wp_auto.
        rewrite Hvt /MsgVoteResp bool_decide_eq_true_2 //. wp_auto.
        send_tail_msgsAA.
        iExists (rv <| raft.raft.msgsAfterAppend' := msgsAA' |>),
                msgs, (msgsAA ++ [m <| raftpb.Message.From' := id |>]), lok.
        iFrame "∗#%". iPureIntro.
        rewrite (abs_outbox_snoc_msgsAA _ _ _ ty) //= /send_msgs /=.
        by rewrite Houtbox.
    - (* (b) [MsgApp] / [MsgHeartbeat]: [Term] must be unset and is stamped
         with [r.Term] (= [s.term]); not a response, so onto [r.msgs] after
         the self-address check. *)
      assert (HnV : m.(raftpb.Message.Type') ≠ MsgVote)
        by (destruct Hlty as [->| ->]; w32_ne).
      assert (HnVR : m.(raftpb.Message.Type') ≠ MsgVoteResp)
        by (destruct Hlty as [->| ->]; w32_ne).
      assert (HnPV : m.(raftpb.Message.Type') ≠ MsgPreVote)
        by (destruct Hlty as [->| ->]; w32_ne).
      assert (HnPVR : m.(raftpb.Message.Type') ≠ MsgPreVoteResp)
        by (destruct Hlty as [->| ->]; w32_ne).
      assert (HnProp : m.(raftpb.Message.Type') ≠ MsgProp)
        by (destruct Hlty as [->| ->]; w32_ne).
      assert (HnRI : m.(raftpb.Message.Type') ≠ MsgReadIndex)
        by (destruct Hlty as [->| ->]; w32_ne).
      assert (HnAR : m.(raftpb.Message.Type') ≠ MsgAppResp)
        by (destruct Hlty as [->| ->]; w32_ne).
      (* not a vote type *)
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      (* [Term] is unset, so no panic *)
      rewrite Hmterm. wp_auto.
      (* neither [MsgProp] nor [MsgReadIndex]: [Term := r.Term] *)
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      (* not a response *)
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      (* not self-addressed *)
      rewrite Hid bool_decide_eq_false_2 //. wp_auto.
      send_tail_msgs.
      iExists (rv <| raft.raft.msgs' := msgs' |>), (msgs ++ [_]), msgsAA, lok.
      iFrame "∗#%". iPureIntro.
      rewrite (abs_outbox_snoc_msgs _ _ _ ty) //= /send_msgs /=.
      by rewrite Houtbox Hterm.
    - (* (c) a type the model does not see: whatever [send] does to [Term]
         and whichever queue it picks, [abs_msg_opt] drops the message. *)
      destruct (mtype_of_None_ne _ Hty) as (HnV & HnVR & HnA & HnH).
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite Hmterm. wp_auto.
      destruct (decide (m.(raftpb.Message.Type') = MsgProp)) as [HProp|HnProp].
      { (* a forwarded proposal: [Term] stays zero; not a response *)
        rewrite HProp /MsgProp bool_decide_eq_true_2 //. wp_auto.
        rewrite HProp /MsgProp bool_decide_eq_false_2; last w32_ne. wp_auto.
        rewrite HProp /MsgProp bool_decide_eq_false_2; last w32_ne. wp_auto.
        rewrite HProp /MsgProp bool_decide_eq_false_2; last w32_ne. wp_auto.
        assert (HnAR : m.(raftpb.Message.Type') ≠ MsgAppResp)
          by (rewrite HProp; w32_ne).
        rewrite Hid bool_decide_eq_false_2; last (intros Hto; exact (HnAR (Hself Hto))).
        wp_auto.
        send_tail_msgs.
        iExists (rv <| raft.raft.msgs' := msgs' |>), (msgs ++ [_]), msgsAA, lok.
        iFrame "∗#%". iPureIntro.
        rewrite abs_outbox_snoc_msgs_None //= /send_msgs /= app_nil_r //. }
      rewrite bool_decide_eq_false_2 //. wp_auto.
      destruct (decide (m.(raftpb.Message.Type') = MsgReadIndex)) as [HRI|HnRI].
      { (* a forwarded read-index request: [Term] stays zero; not a response *)
        rewrite HRI /MsgReadIndex bool_decide_eq_true_2 //. wp_auto.
        rewrite HRI /MsgReadIndex bool_decide_eq_false_2; last w32_ne. wp_auto.
        rewrite HRI /MsgReadIndex bool_decide_eq_false_2; last w32_ne. wp_auto.
        rewrite HRI /MsgReadIndex bool_decide_eq_false_2; last w32_ne. wp_auto.
        assert (HnAR : m.(raftpb.Message.Type') ≠ MsgAppResp)
          by (rewrite HRI; w32_ne).
        rewrite Hid bool_decide_eq_false_2; last (intros Hto; exact (HnAR (Hself Hto))).
        wp_auto.
        send_tail_msgs.
        iExists (rv <| raft.raft.msgs' := msgs' |>), (msgs ++ [_]), msgsAA, lok.
        iFrame "∗#%". iPureIntro.
        rewrite abs_outbox_snoc_msgs_None //= /send_msgs /= app_nil_r //. }
      (* anything else: [Term := r.Term] *)
      rewrite bool_decide_eq_false_2 //. wp_auto.
      destruct (decide (m.(raftpb.Message.Type') = MsgAppResp)) as [HAR|HnAR].
      { (* [MsgAppResp] is a response: onto [r.msgsAfterAppend], and it may be
           self-addressed ([appendEntry] does exactly that). *)
        rewrite HAR /MsgAppResp bool_decide_eq_true_2 //. wp_auto.
        send_tail_msgsAA.
        iExists (rv <| raft.raft.msgsAfterAppend' := msgsAA' |>),
                msgs, (msgsAA ++ [_]), lok.
        iFrame "∗#%". iPureIntro.
        rewrite abs_outbox_snoc_msgsAA_None //= /send_msgs /= app_nil_r //. }
      (* not a response ([MsgVoteResp]/[MsgPreVoteResp] are excluded above),
         so it must not be self-addressed, and goes onto [r.msgs]. *)
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite Hid bool_decide_eq_false_2; last (intros Hto; exact (HnAR (Hself Hto))).
      wp_auto.
      send_tail_msgs.
      iExists (rv <| raft.raft.msgs' := msgs' |>), (msgs ++ [_]), msgsAA, lok.
      iFrame "∗#%". iPureIntro.
      rewrite abs_outbox_snoc_msgs_None //= /send_msgs /= app_nil_r //.
  Qed.

End SendProof.
