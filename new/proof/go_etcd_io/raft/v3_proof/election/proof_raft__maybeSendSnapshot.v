Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__maybeSendSnapshot.

Module RaftMaybeSendSnapshotProof (P : RAFT__MAYBESENDSNAPSHOT_POSTULATES)
  : RAFT__MAYBESENDSNAPSHOT.

  (** **Admitted.**  The statement is true and the ingredients are all in
      place -- [is_Storage] gained its [HSnapshot] triple and [base.v] gained
      [ErrSnapshotTemporarilyUnavailable] for exactly this proof -- but the
      script is not written.  What is left:

      - four collections, none of them hard: [raftLog.snapshot]
        (new/code/go_etcd_io/raft/v3.v:864 -- [unstable.snapshot] is [null]
        by [own_raftLog_at]'s [Hnosnap], so it is a straight call to
        [Storage.Snapshot]), [IsEmptySnap] (v3.v:2004, one field test),
        [Progress.BecomeSnapshot] (tracker.v:290, [ResetState] plus three
        stores) and a use of the existing [raftLog__firstIndex];
      - the two [panic] paths, both discharged by [HSnapshot]: the error is
        either [ErrSnapshotTemporarilyUnavailable] (handled) or [nil] with a
        non-empty snapshot;
      - three [Debugf] calls, via [wp_log] ([inv_raft_phys.v]);
      - the [send], through [send_ok]'s third clause ([MsgSnap] has no
        [mtype_of], [Term] is unset in the literal, and [to ≠ id]).

      [maybeSendAppend], [sendAppend] and [bcastAppend] are [Qed] against
      this statement. *)
  Lemma wp_raft__maybeSendSnapshot : wp_raft__maybeSendSnapshot_body.
  Proof.
    intros_ambient.
    intros cfg r id s to pr Hto.
  Admitted.

End RaftMaybeSendSnapshotProof.
