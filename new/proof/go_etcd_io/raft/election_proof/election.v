(** * Refinement of etcd raft's leader election.

    This file is the aggregator.  Every Hoare triple lives in its own
    spec/postulates/proof/link quadruple under [election_proof/]; requiring
    every [link_*] here is what keeps CI honest, since [make ci] builds only
    what [new/should_build.v] reaches, and a link file nothing re-exported
    would silently go unchecked.

    The top-level result is [Step.wp_raft__Step]: running [Step] on an election
    message takes the physical raft struct from a state refining the protocol
    state [s] to one refining [s'], and the ghost protocol state can be moved
    from [s] to [s'] at the same time -- i.e. the implementation refines the
    protocol of [election_proof/protocol.v].

    Scope, matching [election_proof/protocol.v]:
      - no pre-vote, no check-quorum,
      - no proposals, no read-only requests,
      - no reconfiguration and no learners.

    Trust boundary.  Two kinds, and the layout keeps them apart:
      - [inv_*.v] holds the state axioms and the specs of raft components
        election does not reason about (the log, the tracker's non-vote state,
        the [Logger] and tracing helpers).  These are [Axiom]s.
      - A function that is in scope but unfinished is an [Admitted] inside its
        own [proof_*.v].
    Nothing in a [Module Type] is an assumption: a [Parameter] discharged by a
    real functor adds nothing to [Print Assumptions]. *)

Require Export New.proof.go_etcd_io.raft.election_proof.plog.
Require Export New.proof.go_etcd_io.raft.election_proof.defs.
Require Export New.proof.go_etcd_io.raft.election_proof.inv_raftlog.
Require Export New.proof.go_etcd_io.raft.election_proof.inv_tracker.
Require Export New.proof.go_etcd_io.raft.election_proof.inv_logger.
Require Export New.proof.go_etcd_io.raft.election_proof.inv_misc.
Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.step_lemmas.

(** The callee collections: one Go function each, in dependency order.
    A [link_*] file nothing re-exports is not built, so this list is
    load-bearing. *)
Require Export New.proof.go_etcd_io.raft.election_proof.link_unstable__maybeFirstIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_unstable__maybeLastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_unstable__maybeTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__firstIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__term.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastEntryID.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__isUpToDate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__hasNextOrInProgressSnapshot.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Entry__Size.
Require Export New.proof.go_etcd_io.raft.election_proof.link_unstable__mustCheckOutOfBounds.
Require Export New.proof.go_etcd_io.raft.election_proof.link_unstable__slice.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__mustCheckOutOfBounds.
Require Export New.proof.go_etcd_io.raft.election_proof.link_limitSize.
Require Export New.proof.go_etcd_io.raft.election_proof.link_entsSize.
Require Export New.proof.go_etcd_io.raft.election_proof.link_extend.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__slice.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__scan.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Inflights__reset.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__ResetState.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__BecomeReplicate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_ProgressTracker__ResetVotes.
Require Export New.proof.go_etcd_io.raft.election_proof.link_ProgressTracker__RecordVote.
Require Export New.proof.go_etcd_io.raft.election_proof.link_MajorityConfig__VoteResult.
Require Export New.proof.go_etcd_io.raft.election_proof.link_JointConfig__VoteResult.
Require Export New.proof.go_etcd_io.raft.election_proof.link_ProgressTracker__TallyVotes.
Require Export New.proof.go_etcd_io.raft.election_proof.link_ProgressTracker__Visit.
Require Export New.proof.go_etcd_io.raft.election_proof.link_tracker_NewInflights.
Require Export New.proof.go_etcd_io.raft.election_proof.link_JointConfig__IDs.
Require Export New.proof.go_etcd_io.raft.election_proof.link_slices_Sort.
Require Export New.proof.go_etcd_io.raft.election_proof.link_traceReceiveMessage.
Require Export New.proof.go_etcd_io.raft.election_proof.link_traceSendMessage.
Require Export New.proof.go_etcd_io.raft.election_proof.link_traceBecomeFollower.
Require Export New.proof.go_etcd_io.raft.election_proof.link_traceBecomeCandidate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_traceBecomeLeader.
Require Export New.proof.go_etcd_io.raft.election_proof.link_newReadOnly.
Require Export New.proof.go_etcd_io.raft.election_proof.link_big_NewInt.
Require Export New.proof.go_etcd_io.raft.election_proof.link_rand_Int.
Require Export New.proof.go_etcd_io.raft.election_proof.link_big_Int__Int64.
Require Export New.proof.go_etcd_io.raft.election_proof.link_lockedRand__Intn.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__resetRandomizedElectionTimeout.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__abortLeaderTransfer.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__promotable.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__hasUnappliedConfChanges.
(* [appendEntry]'s callees: the payload accounting, the tracing no-op, and
   the two log writes. *)
Require Export New.proof.go_etcd_io.raft.election_proof.link_payloadSize.
Require Export New.proof.go_etcd_io.raft.election_proof.link_payloadsSize.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__increaseUncommittedSize.
Require Export New.proof.go_etcd_io.raft.election_proof.link_traceReplicate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_unstable__truncateAndAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__append.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__appendEntry.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__IsPaused.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Inflights__Full.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Inflights__grow.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Inflights__Add.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__SentEntries.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__SentCommit.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__entries.
(* [maybeSendSnapshot]'s callees. *)
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__snapshot.
Require Export New.proof.go_etcd_io.raft.election_proof.link_IsEmptySnap.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__BecomeSnapshot.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__maybeSendSnapshot.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__maybeSendAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__sendAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__bcastAppend.

Require Export New.proof.go_etcd_io.raft.election_proof.link_voteRespMsgType.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__reset.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__becomeCandidate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__becomeLeader.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__send.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__poll.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__campaign.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__hup.
Require Export New.proof.go_etcd_io.raft.election_proof.link_stepCandidate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_stepFollower.
Require Export New.proof.go_etcd_io.raft.election_proof.link_stepLeader_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__Step.
(** The constructor: [newRaft] establishes [own_raft_phys]
    ([spec_newRaft.v]).  Its collection pulls in the fifteen callees
    written for it, four of them axioms for untranslated code. *)
Require Export New.proof.go_etcd_io.raft.election_proof.link_newRaft.

(** Log replication, wave 1 (2026-10-01): the tracker side.  [Progress]
    updates a leader makes on a [MsgAppResp], [Inflights.FreeLE], and the
    quorum commit index ([ProgressTracker.Committed] through
    [MajorityConfig]/[JointConfig.CommittedIndex] and
    [matchAckIndexer.AckedIndex]), plus the two pointer-reading helpers of
    [handleAppendEntries]. *)
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__MaybeUpdate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__MaybeDecrTo.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__BecomeProbe.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__CanBumpCommit.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Inflights__FreeLE.
Require Export New.proof.go_etcd_io.raft.election_proof.link_matchAckIndexer__AckedIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_MajorityConfig__CommittedIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_JointConfig__CommittedIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_ProgressTracker__Committed.
Require Export New.proof.go_etcd_io.raft.election_proof.link_pbEntryID.
Require Export New.proof.go_etcd_io.raft.election_proof.link_logSliceFromMsgApp.

(** Log replication, wave 1 (2026-10-01): the log side.  [raftLog.term],
    [lastEntryID], [isUpToDate] and [unstable.maybeTerm] now pin the terms
    they return; these are the follower's append decision and the commit
    index. *)
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__matchTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__zeroTermOnOutOfBounds.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__findConflictByTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__findConflict.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__commitTo.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__maybeCommit.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__maybeAppend.
(* Replication wave 2, follower side (2026-10-01): handleAppendEntries.
   stepFollower / stepCandidate, widened and renamed from *_MsgVoteResp,
   are required above. *)
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__handleAppendEntries.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Implicit Type γ : raft_election_names.
Implicit Type s : pstate.t.

(** ** Sanity check on the model: election safety.

    Two nodes that [Step] leaves in the leader role in the same term are the
    same node.

    This is **not** the result of the development -- [Step.wp_raft__Step],
    reached through [link_raft__Step] above, is, along with the other
    top-level function specs.  A verified spec for a Go
    function is what a client of this proof consumes; a protocol-level
    theorem is an internal detail in service of one.  What this corollary is
    for is evidence that [pstate.t] and [step] entail the property raft
    exists to provide, and so were not defined into triviality.  It cannot
    yet serve even that purpose: the [Section ghost] axioms of
    [election_proof/protocol.v] have no allocation lemma, so the trivial model
    satisfies them all.  See notes/decisions.md, 2026-09-21. *)
Corollary raft_election_safety γ id1 id2 s1 s2 :
  s1.(pstate.role) = role.Leader →
  s2.(pstate.role) = role.Leader →
  s1.(pstate.term) = s2.(pstate.term) →
  own_raft_ghost (Σ:=Σ) γ id1 s1 -∗ own_raft_ghost γ id2 s2 -∗ ⌜ id1 = id2 ⌝.
Proof.
  iIntros (Hl1 Hl2 Hterm) "H1 H2".
  iDestruct (own_raft_ghost_is_leader with "H1") as "#Hle1"; first done.
  iDestruct (own_raft_ghost_is_leader with "H2") as "#Hle2"; first done.
  rewrite Hterm.
  iApply (is_leader_unique with "Hle1 Hle2").
Qed.

End proof.

Section newRaft_post.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** [newRaft]'s postcondition, on a storage with no persisted [HardState]
    and an empty log, is the protocol's initial state.  (Since 2026-10-01
    the protocol state has the log, and [init_pstate]'s is empty: a node
    starting from a storage that already holds entries is not at
    [init_pstate], and [own_raft_ghost_alloc] does not cover it -- its
    entries would need [is_entry]s.) *)
Lemma newRaft_post_init (hs : raftpb.HardState.t) (s : nstate.t) :
  hs_empty hs →
  (nstate_wf s ∧
   s.(nstate.term) = hs.(raftpb.HardState.Term') ∧
   s.(nstate.vote) = hs.(raftpb.HardState.Vote') ∧
   s.(nstate.lead) = W64 0 ∧ s.(nstate.role) = role.Follower ∧
   s.(nstate.votes) = ∅ ∧ s.(nstate.outbox) = []) →
  s.(nstate.logst).(logstate.prev) = raft.entryID.mk (W64 0) (W64 0) →
  s.(nstate.logst).(logstate.sents) = [] →
  s.(nstate.logst).(logstate.uents) = [] →
  s.(nstate.logst).(logstate.committed) = W64 0 →
  nstate_rel s init_pstate.
Proof.
  intros (HT & HV & _) (Hwf & Ht & Hv & Hl & Hr & Hvs & Ho) Hp Hse Hue Hc.
  split; last done.
  destruct s as [?????? ??? [] ?]; simpl in *; subst. rewrite /to_pstate /init_pstate /=.
  by rewrite HT HV.
Qed.
End newRaft_post.

