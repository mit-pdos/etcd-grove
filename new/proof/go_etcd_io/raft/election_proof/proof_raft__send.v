Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__send.

Module SendProof (P : SEND_POSTULATES) : SEND.
Import P.

  (** The common tail once the routing decision has been made: take the
      queue out of [own_raft_phys], build the one-element slice literal,
      append it, store the queue back, trace, and return.  What is left is
      the queue accessor's wand ["Hback"], which wants the appended
      message's contribution to the abstract outbox ([msg_abs]). *)
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
    iApply "HΦ".

  (** A described type other than [MsgSnap]: the wand gets the abstraction
      of the queued message, whose [Entries] is [m]'s, and the outbox is then
      [send_msgs s out] by computation. *)
  Local Ltac finish_some ty :=
    iDestruct ("Hback" with "Hf Hq Hq_cap []") as "Hphys";
    [ iRight; iLeft; iExists ty, _; iFrame "Hents"; iPureIntro;
      split_and!; [ done | first [ (intros ?; discriminate)
                          | (intros ->; match goal with H : mtype_of _ = Some mtype.Snap |- _ =>
                               apply mtype_of_Snap in H; congruence end) ] | reflexivity ]
    | iApply (own_raft_phys_eq with "Hphys"); reflexivity ].

  (** An undescribed type: it contributes nothing. *)
  Local Ltac finish_none :=
    iDestruct ("Hback" with "Hf Hq Hq_cap []") as "Hphys";
    [ iLeft; iPureIntro; split; [ done | reflexivity ]
    | iApply (own_raft_phys_eq with "Hphys"); reflexivity ].

  Lemma wp_raft__send : wp_raft__send_body.
  Proof.
    intros_ambient.
    intros cfg r id s m ents out Hfrom Hok.
    wp_start as "@". wp_auto.
    (* [From] is unset, so [send] fills it in with [r.id]. *)
    rewrite Hfrom bool_decide_eq_true_2 //. wp_auto. wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
    destruct Hok as [(ty & Hvoty & Hty & Hmterm & Hself & ->)
                    |[(ty & Hlty & Hty & Hmterm & Hself & ->)
                     |[[(HSnap & Hmterm & Hself & sv & voters & ->)
                       |(Hty & Hmterm & Hself & ->)]
                      |[(HAR & Hmterm & ->)
                       |(HProp & Hmterm & Hself & ->)]]]].
    - (* (a) a vote message: [Term] is kept.  [MsgVote] goes onto [r.msgs],
         [MsgVoteResp] onto [r.msgsAfterAppend]; either way the abstract
         outbox grows by exactly that message -- up to permutation, since a
         [MsgVote] lands in front of whatever [msgsAfterAppend] holds. *)
      destruct Hvoty as [Hvt|Hvt].
      + (* [MsgVote] is not a response, so it goes onto [r.msgs]. *)
        assert (HnS : m.(raftpb.Message.Type') ≠ MsgSnap) by (rewrite Hvt; w32_ne).
        rewrite Hvt /MsgVote bool_decide_eq_true_2 //. wp_auto.
        rewrite bool_decide_eq_false_2 //. wp_auto.
        (* [MsgVote] is none of the response types *)
        rewrite Hvt /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
        rewrite Hvt /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
        rewrite Hvt /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
        (* not self-addressed *)
        wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
        rewrite bool_decide_eq_false_2; last exact (Hself Hvt). wp_auto.
        send_tail own_raft_phys_msgs.
        finish_some ty.
      + (* [MsgVoteResp] is a response, so it goes onto [r.msgsAfterAppend]. *)
        assert (HnS : m.(raftpb.Message.Type') ≠ MsgSnap) by (rewrite Hvt; w32_ne).
        rewrite Hvt /MsgVoteResp bool_decide_eq_false_2; last w32_ne.
        wp_auto.
        rewrite Hvt /MsgVoteResp bool_decide_eq_true_2 //. wp_auto.
        rewrite bool_decide_eq_false_2 //. wp_auto.
        rewrite Hvt /MsgVoteResp bool_decide_eq_false_2; last w32_ne.
        wp_auto.
        rewrite Hvt /MsgVoteResp bool_decide_eq_true_2 //. wp_auto.
        send_tail own_raft_phys_msgsAA.
        finish_some ty.
    - (* (b) [Term] must be unset and is stamped with [r.Term] (= [s.term]);
         not a response, so onto [r.msgs] after the self-address check. *)
      assert (HnV : m.(raftpb.Message.Type') ≠ MsgVote)
        by (destruct Hlty as [->|[->|[->| ->]]]; w32_ne).
      assert (HnVR : m.(raftpb.Message.Type') ≠ MsgVoteResp)
        by (destruct Hlty as [->|[->|[->| ->]]]; w32_ne).
      assert (HnPV : m.(raftpb.Message.Type') ≠ MsgPreVote)
        by (destruct Hlty as [->|[->|[->| ->]]]; w32_ne).
      assert (HnPVR : m.(raftpb.Message.Type') ≠ MsgPreVoteResp)
        by (destruct Hlty as [->|[->|[->| ->]]]; w32_ne).
      assert (HnProp : m.(raftpb.Message.Type') ≠ MsgProp)
        by (destruct Hlty as [->|[->|[->| ->]]]; w32_ne).
      assert (HnRI : m.(raftpb.Message.Type') ≠ MsgReadIndex)
        by (destruct Hlty as [->|[->|[->| ->]]]; w32_ne).
      assert (HnAR : m.(raftpb.Message.Type') ≠ MsgAppResp)
        by (destruct Hlty as [->|[->|[->| ->]]]; w32_ne).
      assert (HnS : m.(raftpb.Message.Type') ≠ MsgSnap)
        by (destruct Hlty as [->|[->|[->| ->]]]; w32_ne).
      (* not a vote type *)
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      (* [Term] is unset, so no panic *)
      rewrite Hmterm. wp_auto.
      (* neither [MsgProp] nor [MsgReadIndex]: [Term := r.Term] *)
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto. wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
      (* not a response *)
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      (* not self-addressed *)
      wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
      rewrite bool_decide_eq_false_2 //. wp_auto.
      send_tail own_raft_phys_msgs.
      finish_some ty.
    - (* (c') [MsgSnap]: (b)'s path through the body; the abstract message is
         the snapshot's, [abs_snap_from], at the caller's [sv]/[voters]. *)
      assert (HnV : m.(raftpb.Message.Type') ≠ MsgVote) by (rewrite HSnap; w32_ne).
      assert (HnVR : m.(raftpb.Message.Type') ≠ MsgVoteResp) by (rewrite HSnap; w32_ne).
      assert (HnPV : m.(raftpb.Message.Type') ≠ MsgPreVote) by (rewrite HSnap; w32_ne).
      assert (HnPVR : m.(raftpb.Message.Type') ≠ MsgPreVoteResp) by (rewrite HSnap; w32_ne).
      assert (HnProp : m.(raftpb.Message.Type') ≠ MsgProp) by (rewrite HSnap; w32_ne).
      assert (HnRI : m.(raftpb.Message.Type') ≠ MsgReadIndex) by (rewrite HSnap; w32_ne).
      assert (HnAR : m.(raftpb.Message.Type') ≠ MsgAppResp) by (rewrite HSnap; w32_ne).
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite Hmterm. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto. wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
      rewrite bool_decide_eq_false_2 //. wp_auto.
      send_tail own_raft_phys_msgs.
      iDestruct ("Hback" with "Hf Hq Hq_cap []") as "Hphys".
      { iRight; iRight; iPureIntro. split.
        - rewrite /= HSnap. done.
        - exists sv, voters. reflexivity. }
      iApply (own_raft_phys_eq with "Hphys"). reflexivity.
    - (* (c) a type the model does not see: stamped, onto [r.msgs], and it
         drops out of the abstract outbox. *)
      destruct (mtype_of_None_ne _ Hty)
        as (HnProp & HnA & HnAR & HnV & HnVR & HnS & HnH & HnHR & HnRI & HnRIR & HnPV & HnPVR).
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite Hmterm. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
      rewrite bool_decide_eq_false_2 //. wp_auto.
      send_tail own_raft_phys_msgs.
      finish_none.
    - (* (d) [MsgAppResp]: stamped, and a response, so onto
         [r.msgsAfterAppend]; it may be self-addressed ([appendEntry] does
         exactly that). *)
      assert (HnV : m.(raftpb.Message.Type') ≠ MsgVote) by (rewrite HAR; w32_ne).
      assert (HnVR : m.(raftpb.Message.Type') ≠ MsgVoteResp) by (rewrite HAR; w32_ne).
      assert (HnPV : m.(raftpb.Message.Type') ≠ MsgPreVote) by (rewrite HAR; w32_ne).
      assert (HnPVR : m.(raftpb.Message.Type') ≠ MsgPreVoteResp) by (rewrite HAR; w32_ne).
      assert (HnProp : m.(raftpb.Message.Type') ≠ MsgProp) by (rewrite HAR; w32_ne).
      assert (HnRI : m.(raftpb.Message.Type') ≠ MsgReadIndex) by (rewrite HAR; w32_ne).
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite Hmterm. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
      rewrite HAR /MsgAppResp bool_decide_eq_true_2 //. wp_auto.
      send_tail own_raft_phys_msgsAA.
      assert (Hty : mtype_of m.(raftpb.Message.Type') = Some mtype.AppResp) by (rewrite HAR; done).
      assert (HnS : m.(raftpb.Message.Type') ≠ MsgSnap) by (rewrite HAR; w32_ne).
      finish_some mtype.AppResp.
    - (* (e) a forwarded proposal: [Term] stays zero; not a response *)
      assert (HnV : m.(raftpb.Message.Type') ≠ MsgVote) by (rewrite HProp; w32_ne).
      assert (HnVR : m.(raftpb.Message.Type') ≠ MsgVoteResp) by (rewrite HProp; w32_ne).
      assert (HnPV : m.(raftpb.Message.Type') ≠ MsgPreVote) by (rewrite HProp; w32_ne).
      assert (HnPVR : m.(raftpb.Message.Type') ≠ MsgPreVoteResp) by (rewrite HProp; w32_ne).
      assert (HnAR : m.(raftpb.Message.Type') ≠ MsgAppResp) by (rewrite HProp; w32_ne).
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite bool_decide_eq_false_2 //. wp_auto.
      rewrite Hmterm. wp_auto.
      rewrite HProp /MsgProp bool_decide_eq_true_2 //. wp_auto.
      rewrite HProp /MsgProp bool_decide_eq_false_2; last w32_ne. wp_auto.
      rewrite HProp /MsgProp bool_decide_eq_false_2; last w32_ne. wp_auto.
      rewrite HProp /MsgProp bool_decide_eq_false_2; last w32_ne. wp_auto.
      wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
      rewrite bool_decide_eq_false_2 //. wp_auto.
      send_tail own_raft_phys_msgs.
      iDestruct ("Hback" with "Hf Hq Hq_cap []") as "Hphys".
      { iRight; iLeft; iExists mtype.Propose, _; iFrame "Hents"; iPureIntro.
        split_and!; [ rewrite /= HProp; done | (intros ?; discriminate) | reflexivity ]. }
      iApply (own_raft_phys_eq with "Hphys").
      rewrite /send_msgs /abs_msg /abs_msg_from /= Hmterm //.
  Qed.

End SendProof.
