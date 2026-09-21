(** * Refinement of etcd raft's leader election.

    This file is the aggregator.  Every Hoare triple lives in its own
    spec/postulates/proof/link quadruple under [v3_proof/election/]; requiring
    every [link_*] here is what keeps CI honest, since [make ci] builds only
    what [new/should_build.v] reaches, and a link file nothing re-exported
    would silently go unchecked.

    The top-level result is [Step.wp_raft__Step]: running [Step] on an election
    message takes the physical raft struct from a state refining the protocol
    state [s] to one refining [s'], and the ghost protocol state can be moved
    from [s] to [s'] at the same time -- i.e. the implementation refines the
    protocol of [election_protocol.v].

    Scope, matching [election_protocol.v]:
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

Require Export New.proof.go_etcd_io.raft.v3_proof.election.defs.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raftlog.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_tracker.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_logger.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_misc.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.step_lemmas.

(** The callee collections: one Go function each, in dependency order.
    A [link_*] file nothing re-exports is not built, so this list is
    load-bearing. *)
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_unstable__maybeFirstIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_unstable__maybeLastIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_unstable__maybeTerm.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__firstIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__term.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__lastEntryID.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__isUpToDate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__hasNextOrInProgressSnapshot.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Entry__Size.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_unstable__mustCheckOutOfBounds.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_unstable__slice.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__mustCheckOutOfBounds.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_limitSize.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_entsSize.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_extend.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__slice.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__scan.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Inflights__reset.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Progress__ResetState.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Progress__BecomeReplicate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_ProgressTracker__ResetVotes.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_ProgressTracker__RecordVote.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_MajorityConfig__VoteResult.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_JointConfig__VoteResult.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_ProgressTracker__TallyVotes.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_ProgressTracker__Visit.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_tracker_NewInflights.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_JointConfig__IDs.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_slices_Sort.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_traceReceiveMessage.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_traceSendMessage.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_traceBecomeFollower.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_traceBecomeCandidate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_traceBecomeLeader.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_newReadOnly.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_big_NewInt.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_rand_Int.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_big_Int__Int64.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_lockedRand__Intn.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__resetRandomizedElectionTimeout.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__abortLeaderTransfer.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__promotable.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__hasUnappliedConfChanges.
(* [appendEntry]'s callees: the payload accounting, the tracing no-op, and
   the two log writes. *)
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_payloadSize.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_payloadsSize.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__increaseUncommittedSize.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_traceReplicate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_unstable__truncateAndAppend.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__append.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__appendEntry.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Progress__IsPaused.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Inflights__Full.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Inflights__grow.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Inflights__Add.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Progress__SentEntries.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Progress__SentCommit.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__entries.
(* [maybeSendSnapshot]'s callees. *)
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__snapshot.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_IsEmptySnap.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Progress__BecomeSnapshot.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__maybeSendSnapshot.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__maybeSendAppend.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__sendAppend.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__bcastAppend.

Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_voteRespMsgType.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__reset.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__becomeCandidate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__becomeLeader.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__send.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__poll.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__campaign.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__hup.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_stepCandidate_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_stepFollower_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_stepLeader_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__Step.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Implicit Type γ : raft_election_names.
Implicit Type s : nstate.t.

(** ** Payoff: election safety.

    Two nodes that [Step] leaves in the leader role in the same term are the
    same node. *)
Corollary raft_election_safety γ id1 id2 s1 s2 :
  s1.(nstate.role) = role.Leader →
  s2.(nstate.role) = role.Leader →
  s1.(nstate.term) = s2.(nstate.term) →
  own_raft_ghost (Σ:=Σ) γ id1 s1 -∗ own_raft_ghost γ id2 s2 -∗ ⌜ id1 = id2 ⌝.
Proof.
  iIntros (Hl1 Hl2 Hterm) "H1 H2".
  iDestruct (own_raft_ghost_is_leader with "H1") as "#Hle1"; first done.
  iDestruct (own_raft_ghost_is_leader with "H2") as "#Hle2"; first done.
  rewrite Hterm.
  iApply (is_leader_unique with "Hle1 Hle2").
Qed.

End proof.
