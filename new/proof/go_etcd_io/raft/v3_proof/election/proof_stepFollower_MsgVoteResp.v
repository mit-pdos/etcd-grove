Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_stepFollower_MsgVoteResp.

Module StepFollowerProof (P : STEPFOLLOWER_POSTULATES) : STEPFOLLOWER.

  (** Walk the type switch and fall off the end.

      [own_raft_phys] never has to be unsealed: the nine arms of the switch
      are the only places [stepFollower] touches the struct, and a
      [MsgVoteResp] enters none of them, so [wp_auto] steps from the entry
      allocations straight to the trailing [return nil].

      Only the *first* comparison needs help.  [wp_auto] stops in front of
      [bool_decide (m.(Message.Type') = W32 2)] because [m.(Message.Type')] is
      an opaque projection; [rewrite Hty /MsgVoteResp] turns it into the
      literal [W32 6] **everywhere in the goal at once**, including the eight
      not-yet-stepped comparisons in the nested else-branches, and from then
      on [wp_auto] decides each of them by computation.  The one that is
      already frozen as a [bool_decide] has to be discharged by hand, and
      [w32_ne] rather than [word] -- see notes/gotchas.md. *)
  Lemma wp_stepFollower_MsgVoteResp : wp_stepFollower_MsgVoteResp_body.
  Proof.
    intros_ambient.
    intros cfg r id s m.
    intros Hty.
    wp_start as "Hphys".
    wp_auto.
    rewrite Hty /MsgVoteResp.
    rewrite bool_decide_eq_false_2; last w32_ne.
    wp_auto.
    iApply ("HΦ" $! interface.nil).
    iFrame "Hphys". done.
  Qed.

End StepFollowerProof.
