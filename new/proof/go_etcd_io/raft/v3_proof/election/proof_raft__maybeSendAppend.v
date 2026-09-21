Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__maybeSendAppend.

Module RaftMaybeSendAppendProof (P : RAFT__MAYBESENDAPPEND_POSTULATES)
  : RAFT__MAYBESENDAPPEND.
Import P.

  (** **Admitted**, and this is the one that matters -- everything above it
      ([sendAppend], [bcastAppend]) is [Qed] against the statement.  The
      statement is the true one.

      **The [raftLog.term] blocker is gone (2026-09-21).**
      [spec_raftLog__term.v] is now a *total* triple: no range premise, and
      the postcondition is the iff

        err = interface.nil ↔ prev.index ≤ i ≤ prev.index + |sents| + |uents|

      Both halves are used here -- [←] is not needed, but [→] is: it is what
      turns "the [term] call did not error" into
      [prev.index + 1 ≤ pr.Next], the premise of
      [wp_raftLog__entries_at].  ([pr.Next = 0] is excluded because then the
      argument is [pr.Next - 1 = 2^64 - 1], which [Hnowrap] puts out of
      range.)

      **Two blockers remain, and both are in *other* collections' specs.**
      Neither is about this function's script; both are about resources.

      *** (1) [spec_raft__maybeSendSnapshot.v]'s precondition cannot be met.

      It asks for

        own_raft_phys cfg r id s ∗ own_progress pr

      and at the only call site those two are **contradictory**.
      [own_raft_phys] contains [own_tracker cfg rv.(trk') s.(votes)]
      ([inv_raft_phys.v]), which contains
      [[∗ map] p ∈ prs, own_progress p] with [dom prs = cfg]
      ([inv_tracker.v]).  This function is called with [to ∈ cfg], and [pr]
      is exactly [prs !! to] -- it is what [r.trk.Progress[to]] returned.
      So [own_progress pr] is already inside [own_raft_phys], and
      [own_progress pr] is exclusive: it contains [pr ↦ pv] at
      [DfracOwn 1], and [iCombine] on two of those yields
      [✓ (DfracOwn 1 ⋅ DfracOwn 1)] (probed 2026-09-21).

      Concretely, at the [err ≠ nil] branch this proof holds
      [own_progress_at pr pv iv] borrowed out of the tracker plus the
      accessor wand [own_progress pr -∗ own_tracker …].  Cashing the wand
      rebuilds [own_raft_phys] and costs the [own_progress]; keeping the
      [own_progress] means there is no [own_raft_phys].  There is no third
      option, so [wp_raft__maybeSendSnapshot] as stated is unusable by its
      only caller (its own *proof* is fine -- the precondition is
      satisfiable for a [pr] outside the tracker, so the triple is true,
      just vacuous where it is needed).

      *** (2) [spec_raft__send.v] does not pin the tracker across the call.

      After [r.send(…)] the body calls [pr.SentEntries] and [pr.SentCommit]
      on the [*Progress] pointer it read *before* the send.  To own that
      [Progress] again the proof must find [pr] in the rebuilt tracker.
      [own_tracker_lookup] ([inv_tracker.v]) does that from
      [tv.(Progress') ↦$□ prs] and [prs !! to = Some pr] -- but at the
      *same* [tv].  [send]'s postcondition is
      [own_raft_phys cfg r id (send_msgs s out)], i.e.
      [∃ rv', r ↦ rv' ∗ … own_tracker cfg rv'.(trk') …], and nothing relates
      [rv'.(trk')] to [rv.(trk')].  The persistent progress map bought by
      the [↦$□] change (decisions.md, 2026-09-20) keeps [prs] alive, but it
      is anchored at the *old* [tv.(Progress')]; [progress_map_agree] needs
      the two map references to be the same location, and the spec does not
      say they are.  decisions.md states both halves of this in consecutive
      bullets -- "[prs !! to = Some pr] survives the rebuild" and "nothing
      says [rv'.(trk') = tv], because [send]'s spec cannot say it does not
      touch the field".  The second defeats the first.

      The *implementation* does preserve it: [proof_raft__send.v] re-seals
      with [iExists (rv <| msgs' := … |>) …] on every one of its exits, so
      [rv'.(trk') = rv.(trk')].  Only the spec throws it away.

      *** The fix both blockers want is the same one.

      Split the tracker out of [own_raft_phys] in [inv_raft_phys.v]:

        Definition own_raft_notrk r id s f tv : iProp Σ :=
          (* every conjunct of [own_raft_phys_at] except [Htrk],
             plus ⌜ rv.(raft.raft.trk') = tv ⌝ *)

        Lemma own_raft_phys_at_split r id s f :
          own_raft_phys_at r id s f ⊣⊢
          ∃ tv, own_raft_notrk r id s f tv ∗ own_tracker cfg tv s.(nstate.votes).

      and state [send] and [maybeSendSnapshot] on [own_raft_notrk] -- which
      is the truth about both: neither touches the tracker heap ([send]
      appends to [r.msgs]/[r.msgsAfterAppend]; [maybeSendSnapshot] writes
      the one [Progress] it is handed).  Then this proof borrows [pr] once,
      keeps it across everything, and never has to find it again:

        - [maybeSendSnapshot] gets [own_raft_notrk … tv ∗ own_progress pr] --
          disjoint, and it hands both back;
        - [send] gets [own_raft_notrk … tv] and returns it at the *same*
          [tv], so [own_progress_at pr pv iv] is still in hand for
          [SentEntries]/[SentCommit], with no second lookup;
        - the wand [own_progress pr -∗ own_tracker cfg tv votes] is cashed
          once, at the end, and [own_raft_phys_at_split] re-seals.

      Cost: [inv_raft_phys.v], [spec_raft__send.v] + [proof_raft__send.v]
      (same script, one extra existential), [spec_raft__maybeSendSnapshot.v]
      + its proof, and two extra lines at each of the eleven other
      [wp_raft__send] call sites ([proof_raft__campaign.v] ×3,
      [proof_raft__appendEntry.v] ×1, [proof_raft__Step_helpers/] ×6
      in three files) to split and re-seal.  [own_raft_phys]'s own signature
      does not change, so the other twenty spec files are untouched.

      It was not done here because [spec_raft__maybeSendSnapshot.v] belongs
      to a collection another agent is proving concurrently in this
      checkout, and the brief for this task says not to touch its files.

      *** The rest of the script, which is *not* in doubt.

      The body ([raft__maybeSendAppendⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:3096):

      - [pr := r.trk.Progress[to]] hits because [to ∈ cfg]; take the
        (persistent) progress map out with [own_tracker_progress_map], step
        the lookup with [wp_map_lookup1], then borrow the [own_progress]
        with [own_tracker_lookup];
      - [pr.IsPaused()]: on [true] return [false] with [ms = []] (the outbox
        is unchanged up to [own_raft_phys_send_nil]); on [false] the answer
        [progress_paused pv = false] gives [pv.State ≠ StateSnapshot], which
        is [Progress.SentEntries]'s first premise;
      - [r.raftLog.term(pr.Next-1)] through [own_raftLog_acc]; on an error,
        [maybeSendSnapshot] (whose postcondition is at the same abstract
        state, [MsgSnap] being model-invisible); on [nil], the iff gives the
        [entries] premise;
      - [pr.State ≠ StateReplicate || !pr.Inflights.Full()] decides whether
        [r.raftLog.entries(pr.Next, r.maxMsgSize)] runs.  Note the
        conjunction [SentEntries]'s second premise needs: entries are
        fetched only when the window is *not* full, so in [StateReplicate]
        with a non-empty page [inflights_full iv = false] holds -- and
        nothing between the test and [SentEntries] touches the window.  When
        the branch is not taken [ents] is the zero slice and
        [own_slice_nil] supplies its (empty) ownership;
      - [len(ents) == 0 && !sendIfEmpty] returns [false];
      - the second [if err != nil] is dead: [err] is [nil] from the [term]
        call and [raftLog.entries] returns [nil] too;
      - [r.send(pb.Message{To: to, Type: MsgApp, …})] with [send_ok]'s
        second clause: [Term] is unset in the literal, [To = to ≠ id], and
        [out = [msg.mk mtype.App id to s.term false]], which is [app_sends];
      - then [SentEntries (len ents) (payloadsSize ents)] and
        [SentCommit r.raftLog.committed], and [return true]. *)
  Lemma wp_raft__maybeSendAppend : wp_raft__maybeSendAppend_body.
  Proof.
    intros_ambient.
    intros cfg r id s to sendIfEmpty Hto Hcfg.
  Admitted.

End RaftMaybeSendAppendProof.
