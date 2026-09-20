Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__maybeSendAppend.

Module RaftMaybeSendAppendProof (P : RAFT__MAYBESENDAPPEND_POSTULATES)
  : RAFT__MAYBESENDAPPEND.
Import P.

  (** **Admitted**, and this is the one that matters -- everything above it
      ([sendAppend], [bcastAppend]) is [Qed] against the statement.  The
      statement is the true one; what is missing is the script, and one
      spec change it needs.

      **The blocker, precisely.**  The body's third statement is

        prevTerm, err := r.raftLog.term(pr.Next - 1)

      and [spec_raftLog__term.v] is a *partial* triple: it takes
      [prev.index ≤ i ≤ prev.index + |sents| + |uents|] as a premise and
      concludes the error is [nil].  [maybeSendAppend] cannot supply that
      premise -- nothing in [own_progress] bounds a peer's [Next] against
      the log (see [inv_tracker.v]; [own_progress] is ownership of a
      [Progress] *value*, and the log is not in scope there) -- and the Go
      code does not assume it either: it branches on [err != nil] and falls
      back to [maybeSendSnapshot].  So the call cannot even be stepped.

      The fix is to make [raftLog.term]'s triple **total**, which it can be:
      the body ([raftLog__termⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:1063)
      returns [(0, ErrCompacted)] for [i+1 < firstIndex] and
      [(0, ErrUnavailable)] for [i > lastIndex] and only panics on an error
      from [Storage.Term] *inside* the range, which [is_Storage]'s [HTerm]
      excludes.  So

        {{{ own_raftLog_at l prev sents uents }}}
          l.term(i)
        {{{ (t : w64) (err : interface.t), RET (#t, #err);
            own_raftLog_at l prev sents uents ∗
            ⌜ in_range i → err = interface.nil ⌝ }}}

      is true and provable, and subsumes the present statement.  That is a
      change to another collection's spec, with [raftLog__lastEntryID] as
      the one dependent to re-check; it was not made here because the
      remaining work would not have fitted, not because it is doubtful.

      **The rest of the script**, for whoever picks this up.  All the other
      callees are in place ([Progress.IsPaused], [raftLog.entries],
      [Inflights.Full], [payloadsSize], [Progress.SentEntries],
      [Progress.SentCommit], [raft.send], [raft.maybeSendSnapshot]) and the
      shape is:

      - open [own_raft_phys]; take the progress map out of [own_tracker]
        with [own_tracker_progress_map] -- it is **persistent**, so the copy
        survives the [send] below, which is the only way to come back to the
        same [pr] pointer afterwards ([inv_tracker.v] explains why);
      - [r.trk.Progress[to]] hits because [to ∈ cfg]; borrow the
        [own_progress] with [own_tracker_lookup];
      - [pr.IsPaused()]: on [true] return [false] with [ms = []] (the outbox
        is unchanged up to [own_raft_phys_send_nil]); on [false] the answer
        [progress_paused pv = false] gives [pv.State ≠ StateSnapshot], which
        is exactly [Progress.SentEntries]'s first premise;
      - [r.raftLog.term(pr.Next-1)] as above; on an error, hand the whole
        tracker back and call [maybeSendSnapshot] (whose postcondition is at
        the same abstract state, [MsgSnap] being model-invisible);
      - [pr.State ≠ StateReplicate || !pr.Inflights.Full()] decides whether
        [r.raftLog.entries(pr.Next, r.maxMsgSize)] runs.  Note the
        conjunction the [SentEntries] premise needs: entries are fetched
        only when the window is *not* full, so in [StateReplicate] with a
        non-empty page [inflights_full iv = false] holds -- and nothing
        between the test and [SentEntries] touches the window;
      - [len(ents) == 0 && !sendIfEmpty] returns [false];
      - [r.send(pb.Message{To: to, Type: MsgApp, …})] with [send_ok]'s
        second clause: [Term] is unset in the literal, [To = to ≠ id], and
        [out = [msg.mk mtype.App id to s.term _]], which is [app_sends];
      - after the send, re-borrow [pr] through the kept persistent map and
        run [SentEntries] / [SentCommit]. *)
  Lemma wp_raft__maybeSendAppend : wp_raft__maybeSendAppend_body.
  Proof.
    intros_ambient.
    intros cfg r id s to sendIfEmpty Hto Hcfg.
  Admitted.

End RaftMaybeSendAppendProof.
