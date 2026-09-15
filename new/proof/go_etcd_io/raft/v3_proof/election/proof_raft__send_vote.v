Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__send_vote.

Module SendVoteProof (P : SEND_VOTE_POSTULATES) : SEND_VOTE.

  Lemma wp_raft__send_vote : wp_raft__send_vote_body.
  Proof.
    intros ?????? sem package_sem γ r id s m ty.
    (* [send] fills in [From] (which is already [id], or [None]), leaves [Term]
       alone for vote messages, and appends to [msgsAfterAppend] (for
       [MsgVoteResp]) or to [msgs] (for [MsgVote]).  In both cases the new
       element of the queue is the message [Hm] certifies. *)
    intros Hfrom Hvoty Hty Hmterm Hself.
    wp_start as "@". iNamed "Hphys". wp_auto.
    (* [From] is unset, so [send] fills it in with [r.id]. *)
    rewrite Hfrom bool_decide_eq_true_2 //. wp_auto. rewrite Hid.
    destruct Hvoty as [Hvt|Hvt].
    - (* [MsgVote] is not a response, so it goes onto [r.msgs]. *)
      rewrite Hvt /MsgVote bool_decide_eq_true_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      (* [MsgVote] is none of the response types *)
      rewrite Hvt /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
      rewrite Hvt /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
      rewrite Hvt /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
      (* not self-addressed *)
      rewrite Hid bool_decide_eq_false_2; last exact (Hself Hvt). wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done.
      iIntros "%m_sl [m_sl _]".
      replace (sint.nat (W64 0)) with 0%nat by done.
      rewrite /go.array_literal_size /= /Z.max /= /Z.add /=.
      wp_auto.
      wp_apply (wp_slice_append with "[$Hmsgs $Hmsgs_cap $m_sl]")
        as "%msgs' (Hmsgs & Hmsgs_cap & _)".
      wp_apply (wp_traceSendMessage with "[$Hmisc]") as "Hmisc".
      iApply "HΦ". rewrite /own_raft_phys.
      iExists (rv <| raft.raft.msgs' := msgs' |>),
              (msgs ++ [m <| raftpb.Message.From' := id |>]), msgsAA, lok.
      rewrite big_sepL_app big_sepL_singleton /=.
      iFrame "∗#%".
    - (* [MsgVoteResp] is a response, so it goes onto [r.msgsAfterAppend]. *)
      rewrite Hvt /MsgVoteResp bool_decide_eq_false_2; last w32_ne.
      wp_auto.
      rewrite Hvt /MsgVoteResp bool_decide_eq_true_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite Hvt /MsgVoteResp bool_decide_eq_false_2; last w32_ne.
      wp_auto.
      rewrite Hvt /MsgVoteResp bool_decide_eq_true_2 //. wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done.
      iIntros "%m_sl [m_sl _]".
      replace (sint.nat (W64 0)) with 0%nat by done.
      rewrite /go.array_literal_size /= /Z.max /= /Z.add /=.
      wp_auto.
      wp_apply (wp_slice_append with "[$HmsgsAA $HmsgsAA_cap $m_sl]")
        as "%msgsAA' (HmsgsAA & HmsgsAA_cap & _)".
      wp_apply (wp_traceSendMessage with "[$Hmisc]") as "Hmisc".
      iApply "HΦ". rewrite /own_raft_phys.
      iExists (rv <| raft.raft.msgsAfterAppend' := msgsAA' |>),
              msgs, (msgsAA ++ [m <| raftpb.Message.From' := id |>]), lok.
      rewrite big_sepL_app big_sepL_singleton /=.
      iFrame "∗#%".
  Qed.

End SendVoteProof.
