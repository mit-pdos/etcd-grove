Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__send.

Module SendProof (P : SEND_POSTULATES) : SEND.
Import P.

(** What the abstract outbox grows by when one message is queued: the
    shape of [own_raft_phys_msgs]'s wand, for one message. *)
Lemma omap_abs_msg_opt_one m ty :
  mtype_of m.(raftpb.Message.Type') = Some ty →
  omap abs_msg_opt [m] = [abs_msg ty m].
Proof. intros Hty. rewrite /= /abs_msg_opt Hty //. Qed.

Lemma omap_abs_msg_opt_one_None m :
  mtype_of m.(raftpb.Message.Type') = None →
  omap abs_msg_opt [m] = [].
Proof. intros Hty. rewrite /= /abs_msg_opt Hty //. Qed.

(** What [mtype_of t = None] says about the four types the model sees. *)
Lemma mtype_of_None_ne (t : w32) :
  mtype_of t = None →
  t ≠ MsgVote ∧ t ≠ MsgVoteResp ∧ t ≠ MsgApp ∧ t ≠ MsgHeartbeat.
Proof.
  rewrite /mtype_of.
  repeat (case_decide; [discriminate|]). auto.
Qed.

  (** The common tail once the routing decision has been made: take the
      queue out of [own_raft_phys], build the one-element slice literal,
      append it, store the queue back, trace, and return the queue.  What is
      left is an [own_raft_phys_eq] from the wand's outbox,
      [s.outbox ++ omap abs_msg_opt [m']], to [send_msgs s out]. *)
  Local Ltac send_tail acc :=
    iDestruct (acc with "Hphys") as (sl ms) "(Hf & Hq & Hq_cap & Hback)";
    wp_auto;
    wp_apply wp_slice_literal; iSplitR; first done;
    iIntros "%m_sl [m_sl _]";
    replace (sint.nat (W64 0)) with 0%nat by done;
    rewrite /go.array_literal_size /= /Z.max /= /Z.add /=;
    wp_auto;
    wp_apply (wp_slice_append with "[$Hq $Hq_cap $m_sl]")
      as "%q' (Hq & Hq_cap & _)";
    wp_apply wp_traceSendMessage; try wp_auto;
    iApply "HΦ";
    iDestruct ("Hback" with "Hf Hq Hq_cap") as "Hphys";
    iApply (own_raft_phys_eq with "Hphys").

  Lemma wp_raft__send : wp_raft__send_body.
  Proof.
    intros_ambient.
    intros cfg r id s m out Hfrom Hok.
    wp_start as "@". wp_auto.
    (* [From] is unset, so [send] fills it in with [r.id]. *)
    rewrite Hfrom bool_decide_eq_true_2 //. wp_auto. wp_raft_field.
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
        wp_raft_field.
        rewrite bool_decide_eq_false_2; last exact (Hself Hvt). wp_auto.
        send_tail own_raft_phys_msgs.
        rewrite (omap_abs_msg_opt_one _ ty) //.
      + (* [MsgVoteResp] is a response, so it goes onto [r.msgsAfterAppend]. *)
        rewrite Hvt /MsgVoteResp bool_decide_eq_false_2; last w32_ne.
        wp_auto.
        rewrite Hvt /MsgVoteResp bool_decide_eq_true_2 //. wp_auto.
        rewrite bool_decide_eq_false_2 //. wp_auto.
        rewrite Hvt /MsgVoteResp bool_decide_eq_false_2; last w32_ne.
        wp_auto.
        rewrite Hvt /MsgVoteResp bool_decide_eq_true_2 //. wp_auto.
        send_tail own_raft_phys_msgsAA.
        rewrite (omap_abs_msg_opt_one _ ty) //.
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
      rewrite bool_decide_eq_false_2 //. wp_auto. wp_raft_field.
      (* not a response *)
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      (* not self-addressed *)
      wp_raft_field.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      send_tail own_raft_phys_msgs.
      rewrite (omap_abs_msg_opt_one _ ty) //.
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
        wp_raft_field.
      rewrite bool_decide_eq_false_2; last (intros Hto; exact (HnAR (Hself Hto))).
        wp_auto.
        send_tail own_raft_phys_msgs.
        rewrite omap_abs_msg_opt_one_None //. }
      rewrite bool_decide_eq_false_2 //. wp_auto.
      destruct (decide (m.(raftpb.Message.Type') = MsgReadIndex)) as [HRI|HnRI].
      { (* a forwarded read-index request: [Term] stays zero; not a response *)
        rewrite HRI /MsgReadIndex bool_decide_eq_true_2 //. wp_auto.
        rewrite HRI /MsgReadIndex bool_decide_eq_false_2; last w32_ne. wp_auto.
        rewrite HRI /MsgReadIndex bool_decide_eq_false_2; last w32_ne. wp_auto.
        rewrite HRI /MsgReadIndex bool_decide_eq_false_2; last w32_ne. wp_auto.
        assert (HnAR : m.(raftpb.Message.Type') ≠ MsgAppResp)
          by (rewrite HRI; w32_ne).
        wp_raft_field.
      rewrite bool_decide_eq_false_2; last (intros Hto; exact (HnAR (Hself Hto))).
        wp_auto.
        send_tail own_raft_phys_msgs.
        rewrite omap_abs_msg_opt_one_None //. }
      (* anything else: [Term := r.Term] *)
      rewrite bool_decide_eq_false_2 //. wp_auto. wp_raft_field.
      destruct (decide (m.(raftpb.Message.Type') = MsgAppResp)) as [HAR|HnAR].
      { (* [MsgAppResp] is a response: onto [r.msgsAfterAppend], and it may be
           self-addressed ([appendEntry] does exactly that). *)
        rewrite HAR /MsgAppResp bool_decide_eq_true_2 //. wp_auto.
        send_tail own_raft_phys_msgsAA.
        rewrite omap_abs_msg_opt_one_None //. }
      (* not a response ([MsgVoteResp]/[MsgPreVoteResp] are excluded above),
         so it must not be self-addressed, and goes onto [r.msgs]. *)
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      wp_raft_field.
      rewrite bool_decide_eq_false_2; last (intros Hto; exact (HnAR (Hself Hto))).
      wp_auto.
      send_tail own_raft_phys_msgs.
      rewrite omap_abs_msg_opt_one_None //.
  Qed.

End SendProof.
