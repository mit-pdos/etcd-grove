(** * Protocol-level model of etcd raft: election and log replication.

    This file is the specification side of the refinement proof in
    [New.proof.go_etcd_io.raft.election_proof.election]: it defines the abstract
    state machine that a single raft node is supposed to implement, the
    ghost state [own_raft_ghost] representing a node's protocol state, the
    knowledge [is_message] attached to a message that has legitimately been
    put on the network, and the single fancy-update lemma connecting them.

    Scope.  Everything here (and the proofs in [election.v]) assumes:
      - no pre-vote            ([r.preVote = false]),
      - no check-quorum        ([r.checkQuorum = false]),
      - no read-only requests  (no [MsgReadIndex] is ever stepped),
      - no reconfiguration     (the voter set [cfg] is fixed, no learners),
      - no snapshot received   (phase 2 of notes/raft-replication-model.md),
      - **no configuration change is ever requested** -- so the log contains
        no [EntryConfChange] or [EntryConfChangeV2] entry, and
        [r.hasUnappliedConfChanges()] is always [false].  See
        notes/raft-implementation-facts.md.

    **Since 2026-10-01 the model has a log** (notes/raft-replication-model.md):
    a node's protocol state is [(term, vote, lead, role, votes, outbox)] plus
    the log ([base], [log], [commit]) and, for a leader, each voter's
    [Progress.Match] ([matched]).  The log functions are [plog.v]'s, which
    the [raftLog] specs are stated with too.

    **Admitted.**  By the user's decision of 2026-10-01 this file may contain
    [Admitted] lemmas: the ghost-state obligations of some of the replication
    rules ([own_raft_ghost_step_<rule>]), the protocol facts the code's
    [Panicf]s rely on, and the replication safety statements.  Each says in
    its comment what the informal argument is.  Everything about election
    is still [Qed].

    **Deferred premises.**  Three premises the design calls for are *not*
    yet in the rules, because the [raftLog] specs that would let [Step]
    discharge them ([raftLog.term], [lastEntryID], [isUpToDate], and the
    entries [raftLog.slice] returns) do not pin their results yet (wave 1 of
    the design, in progress in parallel).  They are marked [DEFERRED] below:
    [step_grant_vote]'s [plog_up_to_date] check, [step_campaign]'s "the
    vote request carries the candidate's last entry id", and [app_ok]'s
    [logterm] and "entries are a prefix of the log after [index]" clauses.
    Until they are in, the model is more permissive than the code on those
    points, and the admitted replication-safety lemmas below are **not**
    consequences of it. *)

From RecordUpdate Require Import RecordSet.
From Perennial Require Import NamedProps.
Require Export New.proof.proof_prelude.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.
Import RecordSetNotations.

(** ** Roles *)

Module role.
Inductive t := Follower | Candidate | Leader.
#[global] Instance eq_dec : EqDecision t.
Proof. solve_decision. Defined.
End role.

(** ** Abstract messages

    One constructor per [raftpb.MessageType] raft sends between nodes.
    [Propose] is [MsgProp] ([Prop] is a keyword). *)

Module mtype.
Inductive t :=
  | Vote | VoteResp | App | AppResp | Heartbeat | HeartbeatResp
  | Propose | Snap
  | PreVote | PreVoteResp | ReadIndex | ReadIndexResp.
#[global] Instance eq_dec : EqDecision t.
Proof. solve_decision. Defined.
End mtype.

(** Every field of a [raftpb.Message] the protocol reads.  [entries] is the
    list behind [Message.Entries]; see [abs_msg] ([defs.v]) for why the
    abstraction of a physical message needs that list as an argument. *)
Module msg.
Record t :=
  mk {
      ty : mtype.t;
      from : w64;
      to : w64;
      term : w64;
      reject : bool;
      index : w64;               (** [Index] *)
      logterm : w64;             (** [LogTerm] *)
      commit : w64;              (** [Commit] *)
      rejecthint : w64;          (** [RejectHint] *)
      entries : list raftpb.Entry.t;   (** [Entries] *)
    }.

(** A message with no payload: every replication field zero. *)
Definition plain (ty : mtype.t) (from to term : w64) (reject : bool) : t :=
  mk ty from to term reject (W64 0) (W64 0) (W64 0) (W64 0) [].
End msg.

(** Message types whose sender claims to be the leader of [term]. *)
Definition from_leader (ty : mtype.t) : bool :=
  match ty with mtype.App | mtype.Heartbeat | mtype.Snap => true | _ => false end.

(** ** Protocol node state

    [pstate.t] is the **protocol** state of one node: what the state machine
    below and the ghost state [own_raft_ghost] are about, and nothing more.
    It is *not* the abstraction [own_raft_phys] is indexed by -- that is the
    physical abstract state [nstate.t] ([election_proof/defs.v]).  The two
    are connected by [nstate_rel] ([defs.v]); [Step]'s spec is the one place
    that crosses from one to the other.  See notes/decisions.md, "Three
    layers".

    [outbox] is the node's pending outgoing messages — the abstraction of the
    Go code's two queues, [r.msgs] and [r.msgsAfterAppend], together.

    [base]/[log]/[commit] are the log ([plog.v]): the compaction boundary,
    the entries after it, [raftLog.committed].  [matched] is each voter's
    [Progress.Match] **while the node is leader**, and [∅] otherwise (a
    non-leader's [Progress] values are left over from its last leadership
    and nothing reads them).  The field is not called [match], which is a
    keyword. *)

Module pstate.
Record t :=
  mk {
      term : w64;             (** [raft.Term] *)
      vote : w64;             (** [raft.Vote]; [W64 0] is the Go code's [None] *)
      lead : w64;             (** [raft.lead]; [W64 0] is the Go code's [None] *)
      role : role.t;          (** [raft.state] *)
      votes : gmap w64 bool;  (** [raft.trk.Votes] *)
      outbox : list msg.t;    (** [r.msgs] and [r.msgsAfterAppend], together *)
      base : raft.entryID.t;  (** the log's compaction boundary *)
      log : list raftpb.Entry.t;   (** the entries after [base] *)
      commit : w64;           (** [raftLog.committed] *)
      matched : gmap w64 w64; (** [Progress.Match] per voter, leaders only *)
    }.
#[global] Instance settable : Settable _ :=
  settable! mk <term; vote; lead; role; votes; outbox; base; log; commit; matched>.
End pstate.

(** [appendEntry]'s stamping loop: [es[k].Term = r.Term] and
    [es[k].Index = li+1+k]; nothing else about an entry changes, which is
    what keeps [Type = EntryNormal] true of the appended entries.  (Moved
    here from [defs.v] on 2026-10-01: the model's [step_win] and
    [step_propose] stamp too.) *)
Definition stamp (tm li : w64) (k : nat) (e : raftpb.Entry.t) : raftpb.Entry.t :=
  e <| raftpb.Entry.Term' := tm |>
    <| raftpb.Entry.Index' := word.add (word.add li (W64 1)) (W64 k) |>.

Section model.

(** [cfg] is the (fixed) set of voters; [id] the node being described. *)
Context (cfg : gset w64) (id : w64).

Definition is_quorum (q : gset w64) : Prop := size cfg < 2 * size (q ∩ cfg).

(** Two quorums meet.  This is the whole content of election safety; the same
    lemma, for the same [is_quorum], is proved in [readonly.v]. *)
Lemma quorums_intersect (q1 q2 : gset w64) :
  is_quorum q1 → is_quorum q2 → ∃ x, x ∈ q1 ∧ x ∈ q2.
Proof.
  intros Hsize1 Hsize2.
  destruct (decide (q1 ∩ q2 = ∅)) as [Hempty|Hne].
  2:{ apply set_choose_L in Hne as [x Hx]. exists x. set_solver. }
  exfalso.
  have Hunion : (q1 ∩ cfg) ∪ (q2 ∩ cfg) ⊆ cfg by set_solver.
  have Hdisj : (q1 ∩ cfg) ## (q2 ∩ cfg) by set_solver.
  apply subseteq_size in Hunion.
  rewrite size_union in Hunion; [|done].
  unfold is_quorum in *.
  lia.
Qed.

Definition granted (votes : gmap w64 bool) : gset w64 :=
  dom (filter (λ '(_, v), v = true) votes).
Definition rejected (votes : gmap w64 bool) : gset w64 :=
  dom (filter (λ '(_, v), v = false) votes).

(** Putting messages on the network. *)
Definition psend_msgs (s : pstate.t) (ms : list msg.t) : pstate.t :=
  s <| pstate.outbox := s.(pstate.outbox) ++ ms |>.

Lemma psend_msgs_outbox s ms : (psend_msgs s ms).(pstate.outbox) = s.(pstate.outbox) ++ ms.
Proof. done. Qed.
Lemma psend_msgs_term s ms : (psend_msgs s ms).(pstate.term) = s.(pstate.term).
Proof. done. Qed.
Lemma psend_msgs_role s ms : (psend_msgs s ms).(pstate.role) = s.(pstate.role).
Proof. done. Qed.
Lemma psend_msgs_votes s ms : (psend_msgs s ms).(pstate.votes) = s.(pstate.votes).
Proof. done. Qed.
Lemma psend_msgs_log s ms : (psend_msgs s ms).(pstate.log) = s.(pstate.log).
Proof. done. Qed.
Lemma psend_msgs_commit s ms : (psend_msgs s ms).(pstate.commit) = s.(pstate.commit).
Proof. done. Qed.
Lemma psend_msgs_matched s ms : (psend_msgs s ms).(pstate.matched) = s.(pstate.matched).
Proof. done. Qed.

(** [lastIndex()] of the log, as a [w64]. *)
Definition plast_index (s : pstate.t) : w64 :=
  W64 (plog_last_index_Z s.(pstate.base) s.(pstate.log)).

(** ** Role transitions

    These mirror the Go code exactly.  [reset(term)] clears [Vote] only when
    the term actually changes, always clears [lead] and the vote tally; the
    [becomeX] wrappers then set [lead] and [state].  None of them sends, so
    all three carry the outbox across unchanged, and none touches the log.
    A non-leader's [matched] is [∅] (see [pstate.t]); a new leader's is
    whatever [reset] left, which [step_win] pins with [leader_match_ok]. *)

Definition pbecome_follower (s : pstate.t) (term lead : w64) : pstate.t :=
  {| pstate.term := term;
     pstate.vote := if decide (term = s.(pstate.term))
                    then s.(pstate.vote) else W64 0;
     pstate.lead := lead;
     pstate.role := role.Follower;
     pstate.votes := ∅;
     pstate.outbox := s.(pstate.outbox);
     pstate.base := s.(pstate.base);
     pstate.log := s.(pstate.log);
     pstate.commit := s.(pstate.commit);
     pstate.matched := ∅ |}.

Definition pbecome_candidate (s : pstate.t) : pstate.t :=
  {| pstate.term := word.add s.(pstate.term) (W64 1);
     pstate.vote := id;
     pstate.lead := W64 0;
     pstate.role := role.Candidate;
     pstate.votes := ∅;
     pstate.outbox := s.(pstate.outbox);
     pstate.base := s.(pstate.base);
     pstate.log := s.(pstate.log);
     pstate.commit := s.(pstate.commit);
     pstate.matched := ∅ |}.

Definition pbecome_leader (s : pstate.t) (mt : gmap w64 w64) : pstate.t :=
  {| pstate.term := s.(pstate.term);
     pstate.vote := s.(pstate.vote);
     pstate.lead := id;
     pstate.role := role.Leader;
     pstate.votes := ∅;
     pstate.outbox := s.(pstate.outbox);
     pstate.base := s.(pstate.base);
     pstate.log := s.(pstate.log);
     pstate.commit := s.(pstate.commit);
     pstate.matched := mt |}.

(** What [reset] leaves in [Progress.Match] ([raft.go:779-808]): [0] for
    every voter, then [lastIndex()] for the node itself.  Stated without
    the voter set: a [0] claims nothing. *)
Definition leader_match_ok (s : pstate.t) (mt : gmap w64 w64) : Prop :=
  mt !! id = Some (plast_index s) ∧
  ∀ v x, v ≠ id → mt !! v = Some x → x = W64 0.

(** The empty entry a new leader appends ([pb.Entry{Data: nil}], the zero
    [Entry]), stamped at the leader's term and the log's next index; the
    protocol reading of [leader_entry] ([defs.v]). *)
Definition pleader_entry (s : pstate.t) : raftpb.Entry.t :=
  stamp s.(pstate.term) (plast_index s) 0 (zero_val raftpb.Entry.t).

Definition pappend (s : pstate.t) (es : list raftpb.Entry.t) : pstate.t :=
  s <| pstate.log := s.(pstate.log) ++ es |>.

(** A candidate that has just won: [becomeLeader] up to its [send]. *)
Definition pwin_state (s : pstate.t) (mt : gmap w64 w64) : pstate.t :=
  pappend (pbecome_leader s mt) [pleader_entry s].

(** [appendEntry]'s self-acknowledgement: a [MsgAppResp] to itself at the
    new last index, which [Step(MsgAppResp)] later turns into the leader's
    own [Match]. *)
Definition pself_ack (s : pstate.t) : msg.t :=
  msg.mk mtype.AppResp id id s.(pstate.term) false (plast_index s)
    (W64 0) (W64 0) (W64 0) [].

(** [campaign]'s vote request to [to], carrying the last entry id it read
    ([Index: last.index, LogTerm: last.term]). *)
Definition pvote_req (to term : w64) (last : raft.entryID.t) : msg.t :=
  msg.mk mtype.Vote id to term false
    last.(raft.entryID.index') last.(raft.entryID.term') (W64 0) (W64 0) [].

(** Receiving a message from the leader of the current term:
    [stepFollower]'s [r.lead = m.From] or [stepCandidate]'s
    [becomeFollower(m.Term, m.From)], which agree on [pstate] (a follower's
    [votes] are [∅]; the vote is kept at the same term). *)
Definition padopt_leader (s : pstate.t) (from : w64) : pstate.t :=
  s <| pstate.lead := from |> <| pstate.role := role.Follower |>
    <| pstate.votes := ∅ |> <| pstate.matched := ∅ |>.

Definition match_of (s : pstate.t) (v : w64) : w64 :=
  default (W64 0) (s.(pstate.matched) !! v).

(** The voters whose [Match] is at least [n]. *)
Definition acked_by (s : pstate.t) (n : w64) : gset w64 :=
  dom (filter (λ '(_, x), uint.Z n ≤ uint.Z x) s.(pstate.matched)).

(** [raft.trk.RecordVote]: the first vote recorded for a node wins; later
    ones are dropped. *)
Definition record_vote (votes : gmap w64 bool) (from : w64) (v : bool)
  : gmap w64 bool :=
  match votes !! from with Some _ => votes | None => <[from := v]> votes end.

(** A node may grant its vote to [from] in its current term when it has not
    already voted for somebody else and does not currently recognise a
    leader. *)
Definition pcan_vote (s : pstate.t) (from : w64) : Prop :=
  s.(pstate.vote) = from ∨ (s.(pstate.vote) = W64 0 ∧ s.(pstate.lead) = W64 0).

(** What a leader's [MsgApp] says ([maybeSendAppend]: [Index: pr.Next-1,
    LogTerm: term(pr.Next-1), Entries: entries(pr.Next, maxMsgSize),
    Commit: committed]).

    DEFERRED (see the header): the design's two log clauses,
      [plog_term_at s.base s.log m.index = Some m.logterm] and
      [m.entries `prefix_of` plog_from s.base s.log (word.add m.index (W64 1))],
    are not here yet: [raftLog.term] does not pin the term it returns, and
    [raftLog.entries] only says its entries are entries of the log.  What
    *is* here, [Forall (∈ s.log) m.entries], is what [raftLog.slice]
    gives. *)
Definition app_ok (s : pstate.t) (m : msg.t) : Prop :=
  m.(msg.ty) = mtype.App ∧ m.(msg.from) = id ∧ m.(msg.term) = s.(pstate.term) ∧
  m.(msg.to) ≠ id ∧
  uint.Z m.(msg.commit) ≤ uint.Z s.(pstate.commit) ∧
  Forall (λ e, e ∈ s.(pstate.log)) m.(msg.entries).

(** [maybeSendSnapshot]'s [MsgSnap].  Snapshots are phase 2; all the model
    records of one is that the leader of the current term sent it. *)
Definition snap_ok (s : pstate.t) (m : msg.t) : Prop :=
  m.(msg.ty) = mtype.Snap ∧ m.(msg.from) = id ∧ m.(msg.term) = s.(pstate.term) ∧
  m.(msg.to) ≠ id.

(** What [maybeSendAppend] may send: an [App], or (when the log no longer
    has what the peer needs) a [Snap]. *)
Definition repl_ok (s : pstate.t) (m : msg.t) : Prop := app_ok s m ∨ snap_ok s m.

(** [sendHeartbeat]: [Commit: min(pr.Match, committed)]. *)
Definition heartbeat_ok (s : pstate.t) (m : msg.t) : Prop :=
  m.(msg.ty) = mtype.Heartbeat ∧ m.(msg.from) = id ∧ m.(msg.term) = s.(pstate.term) ∧
  m.(msg.to) ≠ id ∧
  uint.Z m.(msg.commit) ≤ uint.Z s.(pstate.commit) ∧
  uint.Z m.(msg.commit) ≤ uint.Z (match_of s m.(msg.to)).

(** ** The transition relation

    [step s recv s'] says: a node in state [s], making use of the
    already-sent messages [recv], may move to state [s'].  Messages the node
    itself sends are not a separate output: they are the growth of
    [s'.(pstate.outbox)].

    Reflexivity and transitivity are part of the relation so that a single
    Go function which performs several protocol steps refines a single
    [step]. *)

Inductive step : pstate.t → list msg.t → pstate.t → Prop :=
(** Structural rules. *)
| step_refl s :
  step s [] s
| step_trans s₀ r₁ s₁ r₂ s₂ :
  step s₀ r₁ s₁ →
  step s₁ r₂ s₂ →
  step s₀ (r₁ ++ r₂) s₂

(** [Step]'s term preamble: a message from a higher term makes the node step
    down.  It adopts the sender as leader exactly when the message is one
    only a leader sends. *)
| step_higher_term m s :
  uint.Z s.(pstate.term) < uint.Z m.(msg.term) →
  m.(msg.to) = id →
  step s [m]
       (pbecome_follower s m.(msg.term)
          (if from_leader m.(msg.ty) then m.(msg.from) else W64 0))

(** [hup] / [campaign]: a non-leader starts an election.  It increments its
    term, votes for itself, and sends a [MsgVote] to every other voter plus a
    self-addressed [MsgVoteResp] (which the Go code routes through
    [msgsAfterAppend]).

    DEFERRED (see the header): the premise [∀ to, last to = plog_last
    s.base s.log].  [campaign] calls [lastEntryID()] once per peer, and its
    spec does not yet pin the result, so each request carries *some* entry
    id. *)
| step_campaign s peers (last : w64 → raft.entryID.t) :
  s.(pstate.role) ≠ role.Leader →
  id ∈ cfg →
  (** The term increments, and a term that wrapped round to one the node has
      already voted in would let it vote twice in that term. *)
  uint.Z s.(pstate.term) + 1 < 2 ^ 64 →
  peers ≡ₚ elements (cfg ∖ {[id]}) →
  let s' := pbecome_candidate s in
  step s []
       (psend_msgs s'
          ([msg.plain mtype.VoteResp id id s'.(pstate.term) false] ++
           ((λ to, pvote_req to s'.(pstate.term) (last to)) <$> peers)))

(** Granting a vote.

    DEFERRED (see the header): the premise
    [plog_up_to_date s.base s.log (raft.entryID.mk m.logterm m.index) = true];
    [raftLog.isUpToDate]'s spec does not pin its result yet. *)
| step_grant_vote m s :
  m.(msg.ty) = mtype.Vote →
  m.(msg.to) = id →
  (** [W64 0] is the Go code's [None], so a vote *for* it is not a vote at
      all. *)
  m.(msg.from) ≠ W64 0 →
  m.(msg.term) = s.(pstate.term) →
  pcan_vote s m.(msg.from) →
  step s [m]
       (psend_msgs (s <| pstate.vote := m.(msg.from) |>)
          [msg.plain mtype.VoteResp id m.(msg.from) s.(pstate.term) false])

(** Refusing a vote.  Always legal. *)
| step_reject_vote m s :
  m.(msg.ty) = mtype.Vote →
  m.(msg.to) = id →
  step s [m]
       (psend_msgs s
          [msg.plain mtype.VoteResp id m.(msg.from) s.(pstate.term) true])

(** [stepCandidate] / [poll]: record a vote response for the current term. *)
| step_record_vote m s :
  m.(msg.ty) = mtype.VoteResp →
  m.(msg.to) = id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) = role.Candidate →
  step s [m]
       (s <| pstate.votes :=
              record_vote s.(pstate.votes) m.(msg.from) (negb m.(msg.reject)) |>)

(** Winning: a quorum of grants makes the candidate leader ([becomeLeader]:
    [reset], whose [Match] values [leader_match_ok] pins, then [appendEntry]
    of the empty entry, which queues the self-acknowledgement), and it
    immediately broadcasts ([bcastAppend]).

    The broadcast is deliberately loose: **any** list of messages
    [maybeSendAppend] may send, including none at all; see
    [spec_raft__bcastAppend.v] for why one per peer would be false. *)
| step_win s mt ms :
  s.(pstate.role) = role.Candidate →
  is_quorum (granted s.(pstate.votes)) →
  leader_match_ok s mt →
  Forall (repl_ok (pwin_state s mt)) ms →
  step s [] (psend_msgs (pwin_state s mt) ([pself_ack (pwin_state s mt)] ++ ms))

(** Losing: [VoteLost] is "the voters who have not rejected are not a
    quorum" (see the 2026-09 history in notes/false-statements.md). *)
| step_lose s :
  s.(pstate.role) = role.Candidate →
  ¬ is_quorum (cfg ∖ rejected s.(pstate.votes)) →
  step s [] (pbecome_follower s s.(pstate.term) (W64 0))

(** [Ready] hands the pending messages to the transport, emptying the queues.
    Dropping messages from one's own outbox is always legal. *)
| step_drain s o' :
  o' ⊆+ s.(pstate.outbox) →
  step s [] (s <| pstate.outbox := o' |>)

(** *** Log replication (phase 1 of notes/raft-replication-model.md)

    Every rule below is about a message of the node's current term: a
    higher-term message has already been through [step_higher_term]. *)

(** [handleAppendEntries], accepting: [maybeAppend] matched [(logterm,
    index)].  The log becomes [plog_maybe_append]'s, [committed] moves to
    [min(m.Commit, lastnewi)] (never back), and the node acknowledges
    [lastnewi].  The conflict premise is what makes [maybeAppend]'s
    [Panicf] dead; [app_no_conflict_below_commit] is the protocol fact. *)
| step_app_accept m s lastnewi es' :
  m.(msg.ty) = mtype.App →
  m.(msg.to) = id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) ≠ role.Leader →
  uint.Z s.(pstate.commit) ≤ uint.Z m.(msg.index) →
  plog_maybe_append s.(pstate.base) s.(pstate.log)
    (raft.entryID.mk m.(msg.logterm) m.(msg.index)) m.(msg.entries)
    = Some (lastnewi, es') →
  (let ci := plog_find_conflict s.(pstate.base) s.(pstate.log) m.(msg.entries) in
   ci = W64 0 ∨ uint.Z s.(pstate.commit) < uint.Z ci) →
  let s1 := padopt_leader s m.(msg.from) in
  step s [m]
       (psend_msgs
          (s1 <| pstate.log := es' |>
              <| pstate.commit := plog_commit_to s.(pstate.commit)
                                    (if decide (uint.Z m.(msg.commit) < uint.Z lastnewi)
                                     then m.(msg.commit) else lastnewi) |>)
          [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) false lastnewi
             (W64 0) (W64 0) (W64 0) []])

(** [handleAppendEntries], [a.prev.index < committed]: acknowledge the
    commit index. *)
| step_app_stale m s :
  m.(msg.ty) = mtype.App →
  m.(msg.to) = id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) ≠ role.Leader →
  uint.Z m.(msg.index) < uint.Z s.(pstate.commit) →
  step s [m]
       (psend_msgs (padopt_leader s m.(msg.from))
          [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) false s.(pstate.commit)
             (W64 0) (W64 0) (W64 0) []])

(** [handleAppendEntries], rejecting: the log does not have [(logterm,
    index)].  The hint is an optimisation; any is allowed. *)
| step_app_reject m s (hint hintterm : w64) :
  m.(msg.ty) = mtype.App →
  m.(msg.to) = id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) ≠ role.Leader →
  uint.Z s.(pstate.commit) ≤ uint.Z m.(msg.index) →
  ¬ plog_matches s.(pstate.base) s.(pstate.log)
      (raft.entryID.mk m.(msg.logterm) m.(msg.index)) →
  step s [m]
       (psend_msgs (padopt_leader s m.(msg.from))
          [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) true m.(msg.index)
             hintterm (W64 0) hint []])

(** [handleHeartbeat]: [commitTo(m.Commit)], whose [Panicf] the premise
    rules out ([heartbeat_commit_le_last]). *)
| step_heartbeat m s :
  m.(msg.ty) = mtype.Heartbeat →
  m.(msg.to) = id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) ≠ role.Leader →
  uint.Z m.(msg.commit) ≤ plog_last_index_Z s.(pstate.base) s.(pstate.log) →
  step s [m]
       (psend_msgs
          (padopt_leader s m.(msg.from)
             <| pstate.commit := plog_commit_to s.(pstate.commit) m.(msg.commit) |>)
          [msg.plain mtype.HeartbeatResp id m.(msg.from) s.(pstate.term) false])

(** [MsgBeat] / [bcastHeartbeat]: any heartbeats [heartbeat_ok] allows. *)
| step_beat s ms :
  s.(pstate.role) = role.Leader →
  Forall (heartbeat_ok s) ms →
  step s [] (psend_msgs s ms)

(** [stepLeader]'s [MsgAppResp], accepting: [pr.MaybeUpdate(m.Index)]
    raises the sender's [Match].  A *rejecting* [AppResp] changes no
    protocol state ([MaybeDecrTo] moves [Next], not [Match]): [step_refl]. *)
| step_app_resp m s (x : w64) :
  m.(msg.ty) = mtype.AppResp →
  m.(msg.to) = id →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) = role.Leader →
  m.(msg.reject) = false →
  s.(pstate.matched) !! m.(msg.from) = Some x →
  step s [m]
       (s <| pstate.matched :=
              <[m.(msg.from) := if decide (uint.Z x < uint.Z m.(msg.index))
                                then m.(msg.index) else x]> s.(pstate.matched) |>)

(** [maybeCommit]: a quorum's [Match] reaches [n], and the entry there is of
    the leader's own term. *)
| step_commit s (n : w64) :
  s.(pstate.role) = role.Leader →
  uint.Z s.(pstate.commit) < uint.Z n →
  uint.Z n ≤ plog_last_index_Z s.(pstate.base) s.(pstate.log) →
  plog_term_at s.(pstate.base) s.(pstate.log) n = Some s.(pstate.term) →
  is_quorum (acked_by s n) →
  step s [] (s <| pstate.commit := n |>)

(** [bcastAppend] / [sendAppend] outside an election win. *)
| step_send_apps s ms :
  s.(pstate.role) = role.Leader →
  Forall (repl_ok s) ms →
  step s [] (psend_msgs s ms)

(** [MsgProp] at the leader: [appendEntry] of the batch, which queues the
    self-acknowledgement.  [EntryNormal] only: no conf change in phase 1. *)
| step_propose s ents :
  s.(pstate.role) = role.Leader →
  Forall (λ e, e.(raftpb.Entry.Type') = W32 0) ents →
  let s' := pappend s (imap (stamp s.(pstate.term) (plast_index s)) ents) in
  step s [] (psend_msgs s' [pself_ack s'])

(** [MsgProp] at a follower that knows a leader: forwarded, with [Term]
    left at [0] ([send]'s [MsgProp] exception) and [From] stamped. *)
| step_prop_forward m s :
  m.(msg.ty) = mtype.Propose →
  s.(pstate.role) = role.Follower →
  s.(pstate.lead) ≠ W64 0 →
  step s [m]
       (psend_msgs s
          [msg.mk mtype.Propose id s.(pstate.lead) (W64 0) m.(msg.reject)
             m.(msg.index) m.(msg.logterm) m.(msg.commit) m.(msg.rejecthint)
             m.(msg.entries)])
.

End model.

(** ** Ghost state

    The ghost state is deliberately *node-local*: there is no Iris invariant
    here and nothing global to open.  Each node owns the authority over its
    own histories, and that authority is the exclusive part of
    [own_raft_ghost].  Everything a step needs to *learn* is persistent
    knowledge, so it can ride on a message or be held across a step with
    nowhere to put it.

    Election:

    - [is_vote γ v term cand] — node [v] voted for [cand] in [term].  Frozen
      into [v]'s map when it is allocated, so it is persistent, and
      unforgeable because allocating it takes [v]'s own authority.
    - [is_leader γ id term] — a quorum of [is_vote]s for [id] at [term].

    Election safety is quorum intersection plus the agreement of two
    [is_vote]s for one node and term; that is all [is_leader_unique] is.
    What holds a node to one vote per term is [vote_hist_ok].

    Replication (2026-10-01):

    - [is_term_log γ v t γt] — node [v], as leader of term [t], keeps the
      entries it created in [t] in the ghost map [γt] ([index ↦ entry]).
      Frozen into [v]'s per-node map [re_terms] when [v] becomes leader in
      [t] ([step_win]); a node is leader in a term at most once, and
      [terms_ok] is what says so.
    - [is_entry γ e] — the leader of [e]'s term created [e] at [e]'s index.
      Two [is_entry]s at one [(term, index)] agree ([is_entry_agree]): the
      leaders agree by [is_leader_unique], their term logs by the frozen
      map, the entries by the term log's.
    - [is_acked γ v t i] — [v] acknowledged the leader of [t] up to [i]
      (frozen into [v]'s map [re_acks]); [i = 0] is free.
    - [is_committed γ i] — a quorum acknowledged some term's leader up to
      at least [i]; [i = 0] is free.

    [is_message] attaches these to the messages that report them, and
    [own_raft_ghost] keeps an [is_entry] for every entry of the node's log,
    the leader's [is_acked] for every [Match], and [is_committed] of its
    commit index.  These pieces do not yet carry the invariants that would
    make [log_matching] etc. provable (see the admitted lemmas at the end);
    what is proved is that every rule preserves them, for the rules whose
    case is [Qed]. *)

Record raft_election_names := {
    (** The voter set this ghost state is about.  It lives in [γ] rather than
        being a parameter of [own_raft_ghost_step]: a step free to choose its
        own [cfg] could choose a singleton one and elect itself. *)
    re_cfg : gset w64;
    (** [re_votes !! id] names the ghost map holding node [id]'s vote
        history, [term ↦ candidate].  A node absent from here has no ghost
        state at all. *)
    re_votes : gmap w64 gname;
    (** [re_terms !! id]: node [id]'s map [term ↦ γt] of the term logs it
        allocated as leader. *)
    re_terms : gmap w64 gname;
    (** [re_acks !! id]: node [id]'s acknowledgements, [(term, index) ↦ ()]. *)
    re_acks : gmap w64 gname;
  }.

Section ghost.
Context `{!invGS Σ, !allG Σ}.

Implicit Type γ : raft_election_names.

(** *** Votes *)

Definition is_vote γ (v term cand : w64) : iProp Σ :=
  ∃ γv, ⌜ γ.(re_votes) !! v = Some γv ⌝ ∗ term ↪[γv]□ cand.

Global Instance is_vote_pers γ v term cand : Persistent (is_vote γ v term cand).
Proof. apply _. Qed.
Global Instance is_vote_timeless γ v term cand : Timeless (is_vote γ v term cand).
Proof. apply _. Qed.

(** One vote per node per term.  This is the other half of election safety. *)
Lemma is_vote_agree γ v term c1 c2 :
  is_vote γ v term c1 -∗ is_vote γ v term c2 -∗ ⌜ c1 = c2 ⌝.
Proof.
  iIntros "(%γ1 & %Hγ1 & H1) (%γ2 & %Hγ2 & H2)".
  rewrite Hγ1 in Hγ2. injection Hγ2 as <-.
  iApply (ghost_map_elem_agree with "H1 H2").
Qed.

(** *** Leadership *)

Definition is_leader γ (id term : w64) : iProp Σ :=
  ∃ q, ⌜ is_quorum γ.(re_cfg) q ⌝ ∗ [∗ set] v ∈ q, is_vote γ v term id.

Global Instance is_leader_pers γ id term : Persistent (is_leader γ id term).
Proof. apply _. Qed.
Global Instance is_leader_timeless γ id term : Timeless (is_leader γ id term).
Proof. apply _. Qed.

(** ** Election safety

    Two leaders in one term were each elected by a quorum; the quorums meet
    in a voter that cast one vote. *)
Lemma is_leader_unique γ id1 id2 term :
  is_leader γ id1 term -∗ is_leader γ id2 term -∗ ⌜ id1 = id2 ⌝.
Proof.
  iIntros "(%q1 & %Hq1 & #H1) (%q2 & %Hq2 & #H2)".
  destruct (quorums_intersect _ _ _ Hq1 Hq2) as (v & Hv1 & Hv2).
  iDestruct (big_sepS_elem_of _ _ _ Hv1 with "H1") as "Hv1".
  iDestruct (big_sepS_elem_of _ _ _ Hv2 with "H2") as "Hv2".
  iApply (is_vote_agree with "Hv1 Hv2").
Qed.

(** *** Entries, acknowledgements, commitment *)

Definition is_term_log γ (v t : w64) (γt : gname) : iProp Σ :=
  ∃ γm, ⌜ γ.(re_terms) !! v = Some γm ⌝ ∗ t ↪[γm]□ γt.

Definition is_entry γ (e : raftpb.Entry.t) : iProp Σ :=
  ∃ ldr γt, is_leader γ ldr e.(raftpb.Entry.Term') ∗
            is_term_log γ ldr e.(raftpb.Entry.Term') γt ∗
            e.(raftpb.Entry.Index') ↪[γt]□ e.

Definition is_acked γ (v t i : w64) : iProp Σ :=
  ⌜ uint.Z i = 0 ⌝ ∨
  ∃ γa, ⌜ γ.(re_acks) !! v = Some γa ⌝ ∗ (t, i) ↪[γa]□ ().

Definition is_committed γ (i : w64) : iProp Σ :=
  ⌜ uint.Z i = 0 ⌝ ∨
  ∃ (t : w64) q, ⌜ is_quorum γ.(re_cfg) q ⌝ ∗
    [∗ set] v ∈ q, ∃ i', ⌜ uint.Z i ≤ uint.Z i' ⌝ ∗ is_acked γ v t i'.

Global Instance is_term_log_pers γ v t γt : Persistent (is_term_log γ v t γt).
Proof. apply _. Qed.
Global Instance is_term_log_timeless γ v t γt : Timeless (is_term_log γ v t γt).
Proof. apply _. Qed.
Global Instance is_entry_pers γ e : Persistent (is_entry γ e).
Proof. apply _. Qed.
Global Instance is_entry_timeless γ e : Timeless (is_entry γ e).
Proof. apply _. Qed.
Global Instance is_acked_pers γ v t i : Persistent (is_acked γ v t i).
Proof. apply _. Qed.
Global Instance is_acked_timeless γ v t i : Timeless (is_acked γ v t i).
Proof. apply _. Qed.
Global Instance is_committed_pers γ i : Persistent (is_committed γ i).
Proof. apply _. Qed.
Global Instance is_committed_timeless γ i : Timeless (is_committed γ i).
Proof. apply _. Qed.

(** Log matching at one index: two entries with the same term and index
    are the same entry. *)
Lemma is_entry_agree γ e1 e2 :
  e1.(raftpb.Entry.Term') = e2.(raftpb.Entry.Term') →
  e1.(raftpb.Entry.Index') = e2.(raftpb.Entry.Index') →
  is_entry γ e1 -∗ is_entry γ e2 -∗ ⌜ e1 = e2 ⌝.
Proof.
  iIntros (Ht Hi) "(%l1 & %γ1 & #Hl1 & #Ht1 & #He1) (%l2 & %γ2 & #Hl2 & #Ht2 & #He2)".
  iEval (rewrite Ht) in "Hl1 Ht1". iEval (rewrite Hi) in "He1".
  iDestruct (is_leader_unique with "Hl1 Hl2") as %<-.
  iDestruct "Ht1" as (γm1 Hγm1) "Ht1". iDestruct "Ht2" as (γm2 Hγm2) "Ht2".
  rewrite Hγm1 in Hγm2. injection Hγm2 as <-.
  iDestruct (ghost_map_elem_agree with "Ht1 Ht2") as %<-.
  iApply (ghost_map_elem_agree with "He1 He2").
Qed.

Lemma is_committed_0 γ : ⊢ is_committed γ (W64 0).
Proof. iLeft. done. Qed.

(** What is committed up to [i] is committed up to anything below. *)
Lemma is_committed_le γ (i j : w64) :
  uint.Z j ≤ uint.Z i → is_committed γ i -∗ is_committed γ j.
Proof.
  iIntros (Hle) "[%H0 | (%t & %q & %Hq & #Hq)]".
  - iLeft. iPureIntro. word.
  - iRight. iExists t, q. iSplit; first done.
    iApply (big_sepS_impl with "Hq"). iIntros "!> %v %Hv (%i' & %Hi' & #Ha)".
    iExists i'. iFrame "Ha". iPureIntro. lia.
Qed.

(** *** Messages *)

Definition is_message γ (m : msg.t) : iProp Σ :=
  match m.(msg.ty) with
  | mtype.VoteResp =>
      if m.(msg.reject) then True%I
      else is_vote γ m.(msg.from) m.(msg.term) m.(msg.to)
  | mtype.App =>
      is_leader γ m.(msg.from) m.(msg.term) ∗
      ([∗ list] e ∈ m.(msg.entries), is_entry γ e) ∗
      is_committed γ m.(msg.commit)
  | mtype.AppResp =>
      if m.(msg.reject) then True%I
      else is_acked γ m.(msg.from) m.(msg.term) m.(msg.index)
  | mtype.Heartbeat =>
      is_leader γ m.(msg.from) m.(msg.term) ∗ is_committed γ m.(msg.commit)
  | mtype.Snap => is_leader γ m.(msg.from) m.(msg.term)
  | _ => True%I
  end.

Global Instance is_message_pers γ m : Persistent (is_message γ m).
Proof.
  rewrite /is_message. destruct (m.(msg.ty)), (m.(msg.reject)); apply _.
Qed.
Global Instance is_message_timeless γ m : Timeless (is_message γ m).
Proof.
  rewrite /is_message. destruct (m.(msg.ty)), (m.(msg.reject)); apply _.
Qed.

(** The message types that carry nothing. *)
Definition msg_free (ty : mtype.t) : bool :=
  match ty with
  | mtype.Vote | mtype.HeartbeatResp | mtype.Propose | mtype.PreVote
  | mtype.PreVoteResp | mtype.ReadIndex | mtype.ReadIndexResp => true
  | _ => false
  end.

Lemma is_message_free γ m : msg_free m.(msg.ty) = true → ⊢ is_message γ m.
Proof.
  rewrite /is_message. intros Hty. destruct (m.(msg.ty)); try discriminate; done.
Qed.

(** A *rejecting* [VoteResp] is free too: it reports no vote. *)
Lemma is_message_reject γ (from to term : w64) :
  ⊢ is_message γ (msg.plain mtype.VoteResp from to term true).
Proof. rewrite /is_message /=. done. Qed.

(** A granting [VoteResp] carries the vote it reports, and nothing else. *)
Lemma is_message_grant γ (from to term : w64) :
  is_vote γ from term to ⊢ is_message γ (msg.plain mtype.VoteResp from to term false).
Proof. by rewrite /is_message /=. Qed.

Lemma is_message_grant_inv γ m :
  m.(msg.ty) = mtype.VoteResp →
  m.(msg.reject) = false →
  is_message γ m -∗ is_vote γ m.(msg.from) m.(msg.term) m.(msg.to).
Proof. intros Hty Hrej. rewrite /is_message Hty Hrej. by iIntros "$". Qed.

(** *** A node's protocol state *)

Definition vote_hist_ok (voted : gmap w64 w64) (s : pstate.t) : Prop :=
  (∀ t, is_Some (voted !! t) → uint.Z t ≤ uint.Z s.(pstate.term)) ∧
  voted !! s.(pstate.term) =
    (if decide (s.(pstate.vote) = W64 0) then None else Some s.(pstate.vote)).

(** [pbecome_follower] keeps the vote only when the term does not move. *)
Local Lemma pbecome_follower_vote_ne s term lead :
  term ≠ s.(pstate.term) → (pbecome_follower s term lead).(pstate.vote) = W64 0.
Proof. intros Hne. rewrite /pbecome_follower /=. rewrite decide_False //. Qed.

Local Lemma pbecome_follower_vote_same s lead :
  (pbecome_follower s s.(pstate.term) lead).(pstate.vote) = s.(pstate.vote).
Proof. rewrite /pbecome_follower /=. rewrite decide_True //. Qed.

(** A term the node has not reached yet is free to vote in. *)
Lemma vote_hist_fresh voted s t :
  vote_hist_ok voted s →
  uint.Z s.(pstate.term) < uint.Z t →
  voted !! t = None.
Proof.
  intros [Hdom _] Hlt. destruct (voted !! t) eqn:Ht; last done.
  exfalso. unshelve epose proof (Hdom t _) as Hle; [by eexists|]. lia.
Qed.

(** [vote_hist_ok] reads only [term] and [vote]. *)
Local Lemma vote_hist_ok_eq voted s1 s2 :
  vote_hist_ok voted s1 →
  s2.(pstate.term) = s1.(pstate.term) →
  s2.(pstate.vote) = s1.(pstate.vote) →
  vote_hist_ok voted s2.
Proof. rewrite /vote_hist_ok. intros H -> ->. exact H. Qed.

Definition leader_wit γ id s : iProp Σ :=
  match s.(pstate.role) with
  | role.Leader => is_leader γ id s.(pstate.term)
  | _ => True%I
  end.

Global Instance leader_wit_pers γ id s : Persistent (leader_wit γ id s).
Proof. rewrite /leader_wit. destruct (s.(pstate.role)); apply _. Qed.
Global Instance leader_wit_timeless γ id s : Timeless (leader_wit γ id s).
Proof. rewrite /leader_wit. destruct (s.(pstate.role)); apply _. Qed.

(** The terms a node has allocated a term log for: ones it has left behind,
    or the current one if it is leader in it. *)
Definition terms_ok (terms : gmap w64 gname) (s : pstate.t) : Prop :=
  ∀ t, is_Some (terms !! t) →
    uint.Z t < uint.Z s.(pstate.term) ∨
    (t = s.(pstate.term) ∧ s.(pstate.role) = role.Leader).

(** A leader owns the term log of its term. *)
Definition lead_log_own γ (s : pstate.t) (terms : gmap w64 gname) : iProp Σ :=
  match s.(pstate.role) with
  | role.Leader =>
      ∃ γt (M : gmap w64 raftpb.Entry.t),
        ⌜ terms !! s.(pstate.term) = Some γt ⌝ ∗ ghost_map_auth γt 1 M ∗
        ([∗ map] i ↦ e ∈ M, i ↪[γt]□ e)
  | _ => True%I
  end.

Global Instance lead_log_own_timeless γ s terms : Timeless (lead_log_own γ s terms).
Proof. rewrite /lead_log_own. destruct (s.(pstate.role)); apply _. Qed.

(** A leader's [Match] values are backed by acknowledgements. *)
Definition matched_ok γ (s : pstate.t) : iProp Σ :=
  match s.(pstate.role) with
  | role.Leader => [∗ map] v ↦ i ∈ s.(pstate.matched), is_acked γ v s.(pstate.term) i
  | _ => True%I
  end.

Global Instance matched_ok_pers γ s : Persistent (matched_ok γ s).
Proof. rewrite /matched_ok. destruct (s.(pstate.role)); apply _. Qed.
Global Instance matched_ok_timeless γ s : Timeless (matched_ok γ s).
Proof. rewrite /matched_ok. destruct (s.(pstate.role)); apply _. Qed.

Definition own_log_ghost γ (id : w64) (s : pstate.t) : iProp Σ :=
  ∃ γm terms γa (acks : gmap (w64 * w64) unit),
    "%Htname"  ∷ ⌜ γ.(re_terms) !! id = Some γm ⌝ ∗
    "Hterms"   ∷ ghost_map_auth γm 1 terms ∗
    "#Htfrags" ∷ ([∗ map] t ↦ γt ∈ terms, t ↪[γm]□ γt) ∗
    "%Hterms_ok" ∷ ⌜ terms_ok terms s ⌝ ∗
    "Htlog"    ∷ lead_log_own γ s terms ∗
    "%Haname"  ∷ ⌜ γ.(re_acks) !! id = Some γa ⌝ ∗
    "Hacks"    ∷ ghost_map_auth γa 1 acks ∗
    "#Hafrags" ∷ ([∗ map] k ↦ u ∈ acks, k ↪[γa]□ u) ∗
    "#Hents"   ∷ ([∗ list] e ∈ s.(pstate.log), is_entry γ e) ∗
    "#Hmatched" ∷ matched_ok γ s ∗
    "#Hcommit" ∷ is_committed γ s.(pstate.commit).

Global Instance own_log_ghost_timeless γ id s : Timeless (own_log_ghost γ id s).
Proof. apply _. Qed.

Definition own_raft_ghost γ (id : w64) (s : pstate.t) : iProp Σ :=
  ∃ γv voted,
    "%Hname"  ∷ ⌜ γ.(re_votes) !! id = Some γv ⌝ ∗
    "%Hidnz"  ∷ ⌜ id ≠ W64 0 ⌝ ∗
    "Hvoted"  ∷ ghost_map_auth γv 1 voted ∗
    "%Hhist"  ∷ ⌜ vote_hist_ok voted s ⌝ ∗
    "#Hfrags" ∷ ([∗ map] t ↦ c ∈ voted, is_vote γ id t c) ∗
    "#Hout"   ∷ ([∗ list] m ∈ s.(pstate.outbox), is_message γ m) ∗
    "#Htally" ∷ ([∗ set] v ∈ granted s.(pstate.votes), is_vote γ v s.(pstate.term) id) ∗
    "#Hlead"  ∷ leader_wit γ id s ∗
    "Hlg"     ∷ own_log_ghost γ id s.

Global Instance own_raft_ghost_timeless γ id s : Timeless (own_raft_ghost γ id s).
Proof. apply _. Qed.

Lemma own_raft_ghost_intro γ id s γv voted :
  γ.(re_votes) !! id = Some γv →
  id ≠ W64 0 →
  ghost_map_auth γv 1 voted -∗
  ⌜ vote_hist_ok voted s ⌝ -∗
  ([∗ map] t ↦ c ∈ voted, is_vote γ id t c) -∗
  ([∗ list] m ∈ s.(pstate.outbox), is_message γ m) -∗
  ([∗ set] v ∈ granted s.(pstate.votes), is_vote γ v s.(pstate.term) id) -∗
  leader_wit γ id s -∗
  own_log_ghost γ id s -∗
  own_raft_ghost γ id s.
Proof.
  iIntros (??) "H1 %H2 #H3 #H4 #H5 #H6 H7". iExists γv, voted. by iFrame "∗#%".
Qed.

Lemma own_raft_ghost_excl γ id s1 s2 :
  own_raft_ghost γ id s1 -∗ own_raft_ghost γ id s2 -∗ False.
Proof.
  iIntros "(%γ1 & %v1 & %Hn1 & _ & H1 & _) (%γ2 & %v2 & %Hn2 & _ & H2 & _)".
  rewrite Hn1 in Hn2. injection Hn2 as <-.
  iDestruct (ghost_map_auth_valid_2 with "H1 H2") as %[Hq _].
  exfalso. by apply Qp.not_add_le_l in Hq.
Qed.

(** Everything in a node's outbox was legitimately put there. *)
Lemma own_raft_ghost_outbox γ id s :
  own_raft_ghost γ id s -∗ ([∗ list] m ∈ s.(pstate.outbox), is_message γ m).
Proof. iIntros "(% & % & _ & _ & _ & _ & _ & #H & _)". iFrame "#". Qed.

Lemma own_raft_ghost_is_leader γ id s :
  s.(pstate.role) = role.Leader →
  own_raft_ghost γ id s -∗ is_leader γ id s.(pstate.term).
Proof.
  iIntros (Hrole) "(% & % & _ & _ & _ & _ & _ & _ & _ & #H & _)".
  rewrite /leader_wit Hrole. iFrame "#".
Qed.

(** *** Pure facts about the vote tally *)

Lemma elem_of_granted (votes : gmap w64 bool) v :
  v ∈ granted votes ↔ votes !! v = Some true.
Proof.
  rewrite /granted elem_of_dom. split.
  - intros [b Hb]. apply map_lookup_filter_Some in Hb as [Hv Hb].
    simpl in Hb. by subst.
  - intros Hv. eexists. apply map_lookup_filter_Some. done.
Qed.

Lemma granted_empty : granted ∅ = ∅.
Proof. rewrite /granted map_filter_empty dom_empty_L //. Qed.

Lemma elem_of_granted_record_vote votes from b v :
  v ∈ granted (record_vote votes from b) →
  v ∈ granted votes ∨ (v = from ∧ b = true).
Proof.
  rewrite /record_vote. destruct (votes !! from) eqn:Hf; first by left.
  rewrite !elem_of_granted. destruct (decide (v = from)) as [->|Hne].
  - rewrite lookup_insert_eq. intros [= ->]. by right.
  - assert (Hne' : from ≠ v) by congruence.
    rewrite lookup_insert_ne //. by left.
Qed.

(** *** The log ghost state across a step *)

(** The log part of the ghost state across a step that leaves the log
    alone and does not make the node leader, or keeps it leader in the same
    term.  A leader that stops being one must have moved to a higher term:
    that is what keeps it from ever allocating a second term log for one
    term.  The caller supplies the new state's [Match] and commit facts. *)
Lemma own_log_ghost_upd γ id s s' :
  (s'.(pstate.role) = role.Leader →
     s.(pstate.role) = role.Leader ∧ s'.(pstate.term) = s.(pstate.term)) →
  (s'.(pstate.role) ≠ role.Leader → s.(pstate.role) = role.Leader →
     uint.Z s.(pstate.term) < uint.Z s'.(pstate.term)) →
  uint.Z s.(pstate.term) ≤ uint.Z s'.(pstate.term) →
  own_log_ghost γ id s -∗
  ([∗ list] e ∈ s'.(pstate.log), is_entry γ e) -∗
  matched_ok γ s' -∗ is_committed γ s'.(pstate.commit) -∗
  own_log_ghost γ id s'.
Proof.
  iIntros (Hlead Hdown Hle) "H #He' #Hm' #Hc'". iDestruct "H" as (γm terms γa acks) "H". iNamed "H".
  iExists γm, terms, γa, acks. iFrame "Hterms Hacks Htfrags Hafrags He' Hm' Hc'".
  iSplit; first done.
  iSplit.
  { iPureIntro. intros t Ht. destruct (Hterms_ok t Ht) as [Hlt | [-> Hr]].
    - left. lia.
    - destruct (decide (s'.(pstate.role) = role.Leader)) as [Hr'|Hr'].
      + destruct (Hlead Hr') as (_ & ->). by right.
      + left. by apply Hdown. }
  iSplitL "Htlog".
  { rewrite /lead_log_own.
    destruct (decide (s'.(pstate.role) = role.Leader)) as [Hr'|Hr'].
    - destruct (Hlead Hr') as (Hr & Ht).
      iEval (rewrite /lead_log_own Hr) in "Htlog". rewrite Hr' Ht. iExact "Htlog".
    - destruct (s'.(pstate.role)); [done|done|congruence]. }
  done.
Qed.

(** The same, for a step that leaves the log alone. *)
Lemma own_log_ghost_mono' γ id s s' :
  s'.(pstate.log) = s.(pstate.log) →
  (s'.(pstate.role) = role.Leader →
     s.(pstate.role) = role.Leader ∧ s'.(pstate.term) = s.(pstate.term)) →
  (s'.(pstate.role) ≠ role.Leader → s.(pstate.role) = role.Leader →
     uint.Z s.(pstate.term) < uint.Z s'.(pstate.term)) →
  uint.Z s.(pstate.term) ≤ uint.Z s'.(pstate.term) →
  own_log_ghost γ id s -∗ matched_ok γ s' -∗ is_committed γ s'.(pstate.commit) -∗
  own_log_ghost γ id s'.
Proof.
  iIntros (Hlog Hlead Hdown Hle) "H #Hm' #Hc'".
  iAssert ([∗ list] e ∈ s.(pstate.log), is_entry γ e)%I as "#He".
  { iDestruct "H" as (γm terms γa acks) "H". iNamed "H". iFrame "#". }
  iApply (own_log_ghost_upd with "H [] Hm' Hc'"); [done..|].
  rewrite Hlog. iFrame "#".
Qed.


(** The same, when [Match] and the commit index do not change either. *)
Lemma own_log_ghost_mono γ id s s' :
  s'.(pstate.log) = s.(pstate.log) →
  s'.(pstate.commit) = s.(pstate.commit) →
  (s'.(pstate.role) = role.Leader →
     s.(pstate.role) = role.Leader ∧ s'.(pstate.term) = s.(pstate.term) ∧
     s'.(pstate.matched) = s.(pstate.matched)) →
  (s'.(pstate.role) ≠ role.Leader → s.(pstate.role) = role.Leader →
     uint.Z s.(pstate.term) < uint.Z s'.(pstate.term)) →
  uint.Z s.(pstate.term) ≤ uint.Z s'.(pstate.term) →
  own_log_ghost γ id s -∗ own_log_ghost γ id s'.
Proof.
  iIntros (Hlog Hcm Hlead Hdown Hle) "H".
  iAssert (matched_ok γ s ∗ is_committed γ s.(pstate.commit))%I as "#[Hm Hc]".
  { iNamed "H". iFrame "#". }
  iApply (own_log_ghost_mono' with "H [] []").
  - done.
  - intros Hr'. destruct (Hlead Hr') as (? & ? & ?). done.
  - done.
  - done.
  - rewrite /matched_ok. destruct (decide (s'.(pstate.role) = role.Leader)) as [Hr'|Hr'].
    + destruct (Hlead Hr') as (Hr & Ht & Hmt).
      iEval (rewrite /matched_ok Hr) in "Hm". rewrite Hr' Ht Hmt. iExact "Hm".
    + destruct (s'.(pstate.role)); [done|done|congruence].
  - rewrite Hcm. iExact "Hc".
Qed.

(** Discharging [own_log_ghost_mono]'s premises for a concrete step. *)
Local Ltac log_mono_tac :=
  simpl; intros; first [ done | congruence | lia | word | (split_and!; done) ].

(** Adding an acknowledgement to one's own map: fresh, or already there. *)
Local Lemma acks_add γa (acks : gmap (w64 * w64) unit) (k : w64 * w64) :
  ghost_map_auth γa 1 acks -∗ ([∗ map] k ↦ u ∈ acks, k ↪[γa]□ u) ==∗
  ∃ acks' : gmap (w64 * w64) unit,
    ghost_map_auth γa 1 acks' ∗ ([∗ map] k ↦ u ∈ acks', k ↪[γa]□ u) ∗
    k ↪[γa]□ ().
Proof.
  iIntros "Hauth #Hfr".
  destruct (acks !! k) as [[]|] eqn:Hk.
  - iModIntro. iExists acks. iFrame "Hauth Hfr".
    iApply (big_sepM_lookup with "Hfr"). done.
  - iMod (ghost_map_insert_persist k () Hk with "Hauth") as "[Hauth #Hnew]".
    iModIntro. iExists _. iFrame "Hauth Hnew".
    rewrite big_sepM_insert //. by iFrame "#".
Qed.

(** [own_log_ghost] lets the node acknowledge anything, at any term.  (That
    an acknowledgement is *justified* is the content of the admitted safety
    lemmas, not of this resource.) *)
Local Lemma own_log_ghost_ack γ id s t i :
  own_log_ghost γ id s ==∗ own_log_ghost γ id s ∗ is_acked γ id t i.
Proof.
  iIntros "H". iDestruct "H" as (γm terms γa acks) "H". iNamed "H".
  iMod (acks_add _ _ (t, i) with "Hacks Hafrags") as (acks') "(Hacks & #Hafr' & #Hk)".
  iModIntro. iSplitR "Hk".
  - iExists γm, terms, γa, acks'. by iFrame "∗#%".
  - iRight. iExists γa. by iFrame "#%".
Qed.

Local Lemma own_log_ghost_ents γ id s :
  own_log_ghost γ id s -∗ [∗ list] e ∈ s.(pstate.log), is_entry γ e.
Proof. iIntros "H". iNamed "H". iFrame "#". Qed.

Local Lemma own_log_ghost_committed γ id s :
  own_log_ghost γ id s -∗ is_committed γ s.(pstate.commit).
Proof. iIntros "H". iNamed "H". iFrame "#". Qed.

Local Lemma own_log_ghost_matched γ id s :
  own_log_ghost γ id s -∗ matched_ok γ s.
Proof. iIntros "H". iNamed "H". iFrame "#". Qed.

Local Lemma pleader_entry_term s :
  (pleader_entry s).(raftpb.Entry.Term') = s.(pstate.term).
Proof. done. Qed.

(** What a leader's broadcast carries, from what the leader holds. *)
Local Lemma repl_ok_message γ id s m :
  s.(pstate.role) = role.Leader →
  repl_ok id s m →
  is_leader γ id s.(pstate.term) -∗
  ([∗ list] e ∈ s.(pstate.log), is_entry γ e) -∗
  is_committed γ s.(pstate.commit) -∗
  is_message γ m.
Proof.
  iIntros (Hr Hok) "#Hl #Hents #Hc".
  destruct Hok as [(Hty & Hfrom & Hterm & _ & Hcm & Hes) | (Hty & Hfrom & Hterm & _)].
  - rewrite /is_message Hty Hfrom Hterm. iFrame "Hl". iSplit.
    + iApply big_sepL_intro. iIntros "!> %k %e %Hk".
      pose proof (Forall_lookup_1 _ _ _ _ Hes Hk) as Hin.
      iApply (big_sepL_elem_of with "Hents"). done.
    + by iApply (is_committed_le with "Hc").
  - rewrite /is_message Hty Hfrom Hterm. iFrame "Hl".
Qed.

(** Every entry [plog_maybe_append] leaves in the log was there or came
    with the message. *)
Local Lemma plog_maybe_append_elem b es prev ents li es' :
  plog_maybe_append b es prev ents = Some (li, es') →
  ∀ e, e ∈ es' → e ∈ es ∨ e ∈ ents.
Proof.
  rewrite /plog_maybe_append. case_decide; [|done]. intros [= <- <-] e.
  case_decide; [by left|].
  rewrite /plog_truncate_append.
  match goal with
  | |- context [drop ?k ents] =>
      destruct (drop k ents) as [|e0 tl] eqn:Hd;
      [ by left
      | rewrite elem_of_app; intros [Hin|Hin];
        [ left; eapply subseteq_take; exact Hin
        | right; apply (subseteq_drop k ents); rewrite Hd; done ] ]
  end.
Qed.

(** *** The refinement obligation, one rule at a time

    The election rules are proved inline in [own_raft_ghost_step]; the
    replication rules each have a lemma here. *)

Local Ltac destruct_ghost :=
  iDestruct "Hown" as (γv voted)
    "(%Hname & %Hidnz & Hvoted & %Hhist & #Hfrags & #Hout & #Htally & #Hlead & Hlg)".

(** [step_win]: allocate the term log, holding the leader's entry, and
    acknowledge the old and the new last index. *)
Local Lemma own_raft_ghost_step_win γ id s mt ms :
  s.(pstate.role) = role.Candidate →
  is_quorum γ.(re_cfg) (granted s.(pstate.votes)) →
  leader_match_ok id s mt →
  Forall (repl_ok id (pwin_state id s mt)) ms →
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id (psend_msgs (pwin_state id s mt)
                         ([pself_ack id (pwin_state id s mt)] ++ ms)).
Proof.
  intros Hrole Hq [Hmid Hmoth] Hms.
  (* name the new state and record what it is, then forget its body, so
     that no [simpl] below unfolds it on one side of a match only *)
  set (s2 := pwin_state id s mt) in *.
  assert (Hs2log : s2.(pstate.log) = s.(pstate.log) ++ [pleader_entry s]) by reflexivity.
  assert (Hs2out : s2.(pstate.outbox) = s.(pstate.outbox)) by reflexivity.
  assert (Hs2term : s2.(pstate.term) = s.(pstate.term)) by reflexivity.
  assert (Hs2vote : s2.(pstate.vote) = s.(pstate.vote)) by reflexivity.
  assert (Hs2votes : s2.(pstate.votes) = ∅) by reflexivity.
  assert (Hs2role : s2.(pstate.role) = role.Leader) by reflexivity.
  assert (Hs2commit : s2.(pstate.commit) = s.(pstate.commit)) by reflexivity.
  assert (Hs2matched : s2.(pstate.matched) = mt) by reflexivity.
  clearbody s2.
  iIntros "Hown". destruct_ghost.
  iAssert (is_leader γ id s.(pstate.term)) as "#Hnewlead".
  { iExists (granted s.(pstate.votes)). by iFrame "#". }
  iDestruct "Hlg" as (γm terms γa acks) "Hlg". iNamed "Hlg".
  (* the current term has no term log: the node was not leader in it *)
  assert (Hfree : terms !! s.(pstate.term) = None).
  { destruct (terms !! s.(pstate.term)) eqn:Ht; last done.
    exfalso. destruct (Hterms_ok s.(pstate.term) ltac:(by eexists)) as [Hlt | [_ Hr]].
    - lia.
    - congruence. }
  set (e := pleader_entry s).
  iMod (ghost_map_alloc {[ e.(raftpb.Entry.Index') := e ]}) as (γt) "[Htauth Htel]".
  rewrite big_sepM_singleton.
  iMod (ghost_map_elem_persist with "Htel") as "#Htel".
  iMod (ghost_map_insert_persist s.(pstate.term) γt Hfree with "Hterms") as "[Hterms #Htnew]".
  iMod (acks_add _ _ (s.(pstate.term), plast_index s) with "Hacks Hafrags")
    as (acks1) "(Hacks & #Hafr1 & #Hk1)".
  iMod (acks_add _ _ (s.(pstate.term), plast_index s2) with "Hacks Hafr1")
    as (acks2) "(Hacks & #Hafr2 & #Hk2)".
  iAssert (is_entry γ e) as "#He".
  { iExists id, γt. rewrite /e pleader_entry_term. iFrame "Hnewlead Htel".
    iExists γm. by iFrame "#". }
  iAssert ([∗ list] x ∈ s2.(pstate.log), is_entry γ x)%I as "#Hents2".
  { rewrite Hs2log big_sepL_app big_sepL_singleton. iFrame "#". }
  iAssert (is_leader γ id s2.(pstate.term)) as "#Hnewlead2".
  { rewrite Hs2term. iFrame "#". }
  iAssert (is_committed γ s2.(pstate.commit)) as "#Hcommit2".
  { rewrite Hs2commit. iFrame "#". }
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [-]").
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); [exact Hs2term|exact Hs2vote].
  - rewrite psend_msgs_outbox Hs2out big_sepL_app.
    iSplitR; [iFrame "#"|]. rewrite big_sepL_cons. iSplitR.
    + rewrite /is_message /pself_ack /=. iRight. iExists γa. rewrite -Hs2term. by iFrame "#%".
    + iApply big_sepL_intro. iIntros "!> %k %x %Hk".
      iApply (repl_ok_message _ id s2 with "Hnewlead2 Hents2 Hcommit2").
      * done.
      * exact (Forall_lookup_1 _ _ _ _ Hms Hk).
  - rewrite psend_msgs_votes Hs2votes granted_empty big_sepS_empty //.
  - rewrite /leader_wit psend_msgs_role Hs2role psend_msgs_term. iFrame "#".
  - iExists γm, (<[s.(pstate.term) := γt]> terms), γa, acks2.
    iFrame "Hterms Hacks #". iSplit; first done.
    iSplit; first (rewrite big_sepM_insert //; by iFrame "#").
    iSplit.
    { iPureIntro. intros t Ht. rewrite psend_msgs_term psend_msgs_role Hs2term Hs2role.
      destruct (decide (t = s.(pstate.term))) as [->|Hne]; first by right.
      rewrite lookup_insert_ne // in Ht.
      destruct (Hterms_ok t Ht) as [Hlt | [-> Hr]]; [by left | congruence]. }
    iSplitL "Htauth".
    { rewrite /lead_log_own psend_msgs_role psend_msgs_term Hs2role Hs2term.
      iExists γt, _. iFrame "Htauth".
      rewrite lookup_insert_eq. iSplit; first done.
      rewrite big_sepM_singleton. iFrame "#". }
    iSplit; first done.
    (* [iFrame "#"] above may already have framed [Hents2]/[Hcommit2], up to
       conversion *)
    try (iSplit; first (rewrite psend_msgs_log; iFrame "#")).
    try (iSplit; last (rewrite psend_msgs_commit; iFrame "#")).
    rewrite /matched_ok psend_msgs_role psend_msgs_matched psend_msgs_term
      Hs2role Hs2matched Hs2term.
    iApply big_sepM_intro. iIntros "!> %v %x %Hv".
    destruct (decide (v = id)) as [->|Hne].
    + rewrite Hmid in Hv. injection Hv as <-.
      iRight. iExists γa. by iFrame "#%".
    + rewrite (Hmoth v x Hne Hv). iLeft. done.
Qed.

(** [step_beat]: a heartbeat carries the leadership and a commit index the
    leader has. *)
Local Lemma own_raft_ghost_step_beat γ id s ms :
  s.(pstate.role) = role.Leader →
  Forall (heartbeat_ok id s) ms →
  own_raft_ghost γ id s ==∗ own_raft_ghost γ id (psend_msgs s ms).
Proof.
  intros Hrole Hms. iIntros "Hown". destruct_ghost.
  iDestruct (own_log_ghost_committed with "Hlg") as "#Hc".
  iAssert (is_leader γ id s.(pstate.term)) as "#Hl".
  { rewrite /leader_wit Hrole. iFrame "#". }
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg]").
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    iApply big_sepL_intro. iIntros "!> %k %m %Hk".
    destruct (Forall_lookup_1 _ _ _ _ Hms Hk) as (Hty & Hfrom & Hterm & _ & Hcm & _).
    rewrite /is_message Hty Hfrom Hterm. iFrame "Hl".
    by iApply (is_committed_le with "Hc").
  - rewrite /psend_msgs /=. iFrame "#".
  - rewrite /leader_wit /psend_msgs /=. iFrame "#".
  - iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
Qed.

(** [step_send_apps]: as [step_win]'s broadcast. *)
Local Lemma own_raft_ghost_step_send_apps γ id s ms :
  s.(pstate.role) = role.Leader →
  Forall (repl_ok id s) ms →
  own_raft_ghost γ id s ==∗ own_raft_ghost γ id (psend_msgs s ms).
Proof.
  intros Hrole Hms. iIntros "Hown". destruct_ghost.
  iDestruct (own_log_ghost_committed with "Hlg") as "#Hc".
  iDestruct (own_log_ghost_ents with "Hlg") as "#Hents".
  iAssert (is_leader γ id s.(pstate.term)) as "#Hl".
  { rewrite /leader_wit Hrole. iFrame "#". }
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg]").
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    iApply big_sepL_intro. iIntros "!> %k %m %Hk".
    iApply (repl_ok_message _ id s with "Hl Hents Hc"); first done.
    exact (Forall_lookup_1 _ _ _ _ Hms Hk).
  - rewrite /psend_msgs /=. iFrame "#".
  - rewrite /leader_wit /psend_msgs /=. iFrame "#".
  - iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
Qed.

(** [step_prop_forward]: a proposal carries nothing. *)
Local Lemma own_raft_ghost_step_prop_forward γ id s m :
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id
    (psend_msgs s
       [msg.mk mtype.Propose id s.(pstate.lead) (W64 0) m.(msg.reject)
          m.(msg.index) m.(msg.logterm) m.(msg.commit) m.(msg.rejecthint)
          m.(msg.entries)]).
Proof.
  iIntros "Hown". destruct_ghost.
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg]").
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    rewrite big_sepL_singleton. by iApply is_message_free.
  - rewrite /psend_msgs /=. iFrame "#".
  - rewrite /leader_wit /psend_msgs /=. iFrame "#".
  - iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
Qed.

(** [step_app_resp]: the new [Match] is the old one or the acknowledgement
    the message carries. *)
Local Lemma own_raft_ghost_step_app_resp γ id s m x :
  m.(msg.ty) = mtype.AppResp →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) = role.Leader →
  m.(msg.reject) = false →
  s.(pstate.matched) !! m.(msg.from) = Some x →
  is_message γ m -∗
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id
    (s <| pstate.matched :=
           <[m.(msg.from) := if decide (uint.Z x < uint.Z m.(msg.index))
                             then m.(msg.index) else x]> s.(pstate.matched) |>).
Proof.
  intros Hty Hterm Hrole Hrej Hx. iIntros "#Hm Hown". destruct_ghost.
  iAssert (is_acked γ m.(msg.from) s.(pstate.term) m.(msg.index)) as "#Hack".
  { rewrite /is_message Hty Hrej -Hterm. iFrame "#". }
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg]").
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - simpl. iFrame "#".
  - simpl. iFrame "#".
  - rewrite /leader_wit /=. iFrame "#".
  - iDestruct (own_log_ghost_matched with "Hlg") as "#Hmatched".
    iDestruct (own_log_ghost_committed with "Hlg") as "#Hc".
    iApply (own_log_ghost_mono' with "Hlg [] []"); [log_mono_tac..| |];
      last (simpl; iFrame "#").
    rewrite /matched_ok /= Hrole.
    iEval (rewrite /matched_ok ?Hrole) in "Hmatched".
    iApply big_sepM_insert_2; last done.
    case_decide; first done.
    iApply (big_sepM_lookup with "Hmatched"). done.
Qed.

(** [step_commit]: a quorum of [Match]es at least [n] is [is_committed n]. *)
Local Lemma own_raft_ghost_step_commit γ id s n :
  s.(pstate.role) = role.Leader →
  is_quorum γ.(re_cfg) (acked_by s n) →
  own_raft_ghost γ id s ==∗ own_raft_ghost γ id (s <| pstate.commit := n |>).
Proof.
  intros Hrole Hq. iIntros "Hown". destruct_ghost.
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg]").
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - simpl. iFrame "#".
  - simpl. iFrame "#".
  - rewrite /leader_wit /=. iFrame "#".
  - iDestruct (own_log_ghost_matched with "Hlg") as "#Hmatched".
    iApply (own_log_ghost_mono' with "Hlg [] []"); [log_mono_tac..| |].
    { rewrite /matched_ok /= Hrole. iEval (rewrite /matched_ok ?Hrole) in "Hmatched".
      iFrame "#". }
    simpl.
    iEval (rewrite /matched_ok ?Hrole) in "Hmatched".
    iRight. iExists s.(pstate.term), (acked_by s n). iSplit; first done.
    iApply big_sepS_intro. iIntros "!> %v %Hv".
    rewrite /acked_by elem_of_dom in Hv. destruct Hv as [x Hx].
    apply map_lookup_filter_Some in Hx as [Hx Hle].
    iExists x. iSplit; first done.
    iApply (big_sepM_lookup with "Hmatched"). done.
Qed.

(** [step_app_stale]: back to follower of [m.from] in the same term, and
    acknowledge the commit index. *)
Local Lemma own_raft_ghost_step_app_stale γ id s m :
  m.(msg.ty) = mtype.App →
  s.(pstate.role) ≠ role.Leader →
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id
    (psend_msgs (padopt_leader s m.(msg.from))
       [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) false s.(pstate.commit)
          (W64 0) (W64 0) (W64 0) []]).
Proof.
  intros Hty Hrole. iIntros "Hown". destruct_ghost.
  iMod (own_log_ghost_ack _ _ _ s.(pstate.term) s.(pstate.commit) with "Hlg")
    as "[Hlg #Hack]".
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg]").
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    rewrite big_sepL_singleton /is_message /=. iFrame "#".
  - rewrite /psend_msgs /padopt_leader /= granted_empty big_sepS_empty //.
  - rewrite /leader_wit /psend_msgs /padopt_leader /=. done.
  - iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
Qed.

(** [step_app_reject]: back to follower of [m.from]; a rejection carries
    nothing. *)
Local Lemma own_raft_ghost_step_app_reject γ id s m hint hintterm :
  s.(pstate.role) ≠ role.Leader →
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id
    (psend_msgs (padopt_leader s m.(msg.from))
       [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) true m.(msg.index)
          hintterm (W64 0) hint []]).
Proof.
  intros Hrole. iIntros "Hown". destruct_ghost.
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg]").
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    rewrite big_sepL_singleton /is_message /=. done.
  - rewrite /psend_msgs /padopt_leader /= granted_empty big_sepS_empty //.
  - rewrite /leader_wit /psend_msgs /padopt_leader /=. done.
  - iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.
Qed.

(** [step_heartbeat]: back to follower of [m.from]; the new commit index is
    the old one or the heartbeat's, which carries [is_committed]. *)
Local Lemma own_raft_ghost_step_heartbeat γ id s m :
  m.(msg.ty) = mtype.Heartbeat →
  s.(pstate.role) ≠ role.Leader →
  is_message γ m -∗
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id
    (psend_msgs
       (padopt_leader s m.(msg.from)
          <| pstate.commit := plog_commit_to s.(pstate.commit) m.(msg.commit) |>)
       [msg.plain mtype.HeartbeatResp id m.(msg.from) s.(pstate.term) false]).
Proof.
  intros Hty Hrole. iIntros "#Hm Hown". destruct_ghost.
  iAssert (is_committed γ m.(msg.commit)) as "#Hmc".
  { rewrite /is_message Hty. iDestruct "Hm" as "[_ $]". }
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg]").
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    rewrite big_sepL_singleton /is_message /=. done.
  - rewrite /psend_msgs /padopt_leader /= granted_empty big_sepS_empty //.
  - rewrite /leader_wit /psend_msgs /padopt_leader /=. done.
  - iDestruct (own_log_ghost_committed with "Hlg") as "#Hc".
    iApply (own_log_ghost_mono' with "Hlg [] []"); [log_mono_tac..| |].
    + rewrite /matched_ok /=. done.
    + rewrite /= /plog_commit_to. case_decide; iFrame "#".
Qed.

(** [step_app_accept].  ADMITTED.  Informal argument: the new log is a
    prefix of the old one followed by a suffix of [m.entries]
    ([plog_maybe_append]), and [is_message] gives an [is_entry] for every
    entry of [m.entries], so every entry of the new log has its [is_entry];
    the new commit index is the old one or [≤ m.commit], which [is_message]
    gives [is_committed] for; the acknowledgement is the node's own to
    allocate ([own_log_ghost_ack]).  What is missing is only the list
    lemma "every element of [plog_truncate_append b es ents] is in [es] or
    in [ents]" and its [drop] variant. *)
Local Lemma own_raft_ghost_step_app_accept γ id s m lastnewi es' :
  m.(msg.ty) = mtype.App →
  m.(msg.term) = s.(pstate.term) →
  s.(pstate.role) ≠ role.Leader →
  plog_maybe_append s.(pstate.base) s.(pstate.log)
    (raft.entryID.mk m.(msg.logterm) m.(msg.index)) m.(msg.entries)
    = Some (lastnewi, es') →
  is_message γ m -∗
  own_raft_ghost γ id s ==∗
  own_raft_ghost γ id
    (psend_msgs
       (padopt_leader s m.(msg.from) <| pstate.log := es' |>
          <| pstate.commit := plog_commit_to s.(pstate.commit)
                                (if decide (uint.Z m.(msg.commit) < uint.Z lastnewi)
                                 then m.(msg.commit) else lastnewi) |>)
       [msg.mk mtype.AppResp id m.(msg.from) s.(pstate.term) false lastnewi
          (W64 0) (W64 0) (W64 0) []]).
Proof.
  intros Hty Hterm Hrole Happ. iIntros "#Hm Hown". destruct_ghost.
  iAssert (([∗ list] e ∈ m.(msg.entries), is_entry γ e) ∗ is_committed γ m.(msg.commit))%I
    as "#[Hments Hmc]".
  { rewrite /is_message Hty. iDestruct "Hm" as "(_ & $ & $)". }
  iDestruct (own_log_ghost_ents with "Hlg") as "#Hents".
  iDestruct (own_log_ghost_committed with "Hlg") as "#Hc".
  iMod (own_log_ghost_ack _ _ _ s.(pstate.term) lastnewi with "Hlg") as "[Hlg #Hack]".
  iModIntro.
  iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
           with "Hvoted [] Hfrags [] [] [] [Hlg]").
  - iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
  - rewrite /psend_msgs /= big_sepL_app. iSplitR; [iFrame "#"|].
    rewrite big_sepL_singleton /is_message /=. iFrame "#".
  - rewrite /psend_msgs /padopt_leader /= granted_empty big_sepS_empty //.
  - rewrite /leader_wit /psend_msgs /padopt_leader /=. done.
  - iApply (own_log_ghost_upd with "Hlg [] [] []"); [log_mono_tac..| | |].
    + (* every entry of the new log is an old one or one the leader sent *)
      simpl. iApply big_sepL_intro. iIntros "!> %k %e %Hk".
      apply list_elem_of_lookup_2 in Hk.
      destruct (plog_maybe_append_elem _ _ _ _ _ _ Happ e Hk) as [Hin|Hin].
      * iApply (big_sepL_elem_of with "Hents"). done.
      * iApply (big_sepL_elem_of with "Hments"). done.
    + rewrite /matched_ok /=. done.
    + (* the old commit index, or at most [m.commit] *)
      rewrite /= /plog_commit_to. case_decide; last iFrame "#".
      iApply (is_committed_le with "Hmc"). case_decide; [lia|lia].
Qed.

(** [step_propose].  ADMITTED.  Informal argument: the leader owns the term
    log of its term ([lead_log_own]); each stamped entry is at an index
    past the leader's last index, hence (by an invariant [own_log_ghost]
    does not yet state: the term log's domain is below [plast_index + 1])
    fresh in the term log, so it can be inserted and frozen, giving its
    [is_entry]; the self-acknowledgement is the node's own to allocate.
    The missing piece is that domain invariant, which [step_win] (one
    entry at the new last index) and [step_propose] (entries past the last
    index) preserve, and which the follower rules -- where the node is not
    leader -- do not mention. *)
Local Lemma own_raft_ghost_step_propose γ id s ents :
  s.(pstate.role) = role.Leader →
  let s' := pappend s (imap (stamp s.(pstate.term) (plast_index s)) ents) in
  own_raft_ghost γ id s ==∗ own_raft_ghost γ id (psend_msgs s' [pself_ack id s']).
Proof.
Admitted.

(** *** The refinement obligation *)

Lemma own_raft_ghost_step γ (id : w64) s recv s' :
  step γ.(re_cfg) id s recv s' →
  ([∗ list] m ∈ recv, is_message γ m) -∗
  own_raft_ghost γ id s ={⊤}=∗
  own_raft_ghost γ id s'.
Proof.
  intros Hstep.
  induction Hstep as
    [ s
    | s0 r1 s1 r2 s2 Hst1 IH1 Hst2 IH2
    | m s Hlt Hto
    | s peers last Hrole Hin Hnowrap Hperm
    | m s Hty Hto Hfrom Hterm Hcan
    | m s Hty Hto
    | m s Hty Hto Hterm Hrole
    | s mt ms Hrole Hq Hmt Hms
    | s Hrole Hnq
    | s o' Hsub
    | m s lastnewi es' Hty Hto Hterm Hrole Hcm Happ Hci
    | m s Hty Hto Hterm Hrole Hidx
    | m s hint hintterm Hty Hto Hterm Hrole Hcm Hnm
    | m s Hty Hto Hterm Hrole Hcm
    | s ms Hrole Hms
    | m s x Hty Hto Hterm Hrole Hrej Hx
    | s n Hrole Hlt Hle Htm Hq
    | s ms Hrole Hms
    | s ents Hrole Hnorm
    | m s Hty Hrole Hlead ].

  - (* step_refl *)
    iIntros "_ Hown". by iFrame.

  - (* step_trans *)
    iIntros "Hrecv Hown".
    iEval (rewrite big_sepL_app) in "Hrecv".
    iDestruct "Hrecv" as "[Hr1 Hr2]".
    iMod (IH1 with "Hr1 Hown") as "Hown".
    by iMod (IH2 with "Hr2 Hown") as "$".

  - (* step_higher_term: a strictly greater term, so the vote is cleared and
       the new term is fresh in the history *)
    iIntros "_ Hown". destruct_ghost.
    assert (Hne : m.(msg.term) ≠ s.(pstate.term)).
    { intros Heq. rewrite Heq in Hlt. lia. }
    pose proof Hhist as Hh; destruct Hh as [Hdom Heq].
    assert (Hhist' : vote_hist_ok voted (pbecome_follower s m.(msg.term)
                       (if from_leader m.(msg.ty) then m.(msg.from) else W64 0))).
    { rewrite /vote_hist_ok (pbecome_follower_vote_ne _ _ _ Hne).
      split.
      - simpl. intros t Ht. specialize (Hdom t Ht). lia.
      - simpl. rewrite ?decide_True //.
        eapply (vote_hist_fresh voted s); [exact Hhist|done]. }
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] [] [Hlg]").
    + iPureIntro. exact Hhist'.
    + by rewrite /pbecome_follower /=.
    + rewrite /pbecome_follower /= granted_empty big_sepS_empty //.
    + rewrite /leader_wit /pbecome_follower /=. done.
    + iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.

  - (* step_campaign: the term goes up by one, so it is fresh, and the node
       votes for itself there *)
    iIntros "_ Hown". destruct_ghost.
    set (t' := word.add s.(pstate.term) (W64 1)).
    assert (Ht' : uint.Z t' = uint.Z s.(pstate.term) + 1) by (subst t'; word).
    assert (Hcterm : (pbecome_candidate id s).(pstate.term) = t') by reflexivity.
    assert (Hcvote : (pbecome_candidate id s).(pstate.vote) = id) by reflexivity.
    assert (Hfree : voted !! t' = None).
    { eapply (vote_hist_fresh voted s); [done|lia]. }
    iMod (ghost_map_insert_persist t' id Hfree with "Hvoted") as "[Hvoted #Hself]".
    iAssert (is_vote γ id t' id) as "#Hisvote".
    { iExists γv. by iFrame "#". }
    assert (Hhist' : vote_hist_ok (<[t' := id]> voted) (pbecome_candidate id s)).
    { destruct Hhist as [Hdom _]. rewrite /vote_hist_ok Hcterm Hcvote. split.
      - intros t [c Hc]. destruct (decide (t = t')) as [->|Hne]; first lia.
        assert (Hne' : t' ≠ t) by congruence.
        rewrite lookup_insert_ne // in Hc.
        unshelve epose proof (Hdom t _) as Hle; [by eexists|]. lia.
      - rewrite lookup_insert_eq decide_False //. }
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv (<[t' := id]> voted) Hname Hidnz
             with "Hvoted [] [] [] [] [] [Hlg]").
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist'); reflexivity.
    + rewrite big_sepM_insert //. by iFrame "#".
    + rewrite /psend_msgs /pbecome_candidate /=.
      rewrite big_sepL_app. iSplitR; [iFrame "#"|].
      rewrite big_sepL_cons. iSplitR.
      * by iApply is_message_grant.
      * rewrite big_sepL_fmap. iApply big_sepL_intro.
        iIntros "!> %k %x %Hk". by iApply is_message_free.
    + rewrite /psend_msgs /pbecome_candidate /= granted_empty big_sepS_empty //.
    + rewrite /leader_wit /psend_msgs /pbecome_candidate /=. done.
    + iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.

  - (* step_grant_vote: either the node has already voted this way, or the
       current term is free in the history *)
    iIntros "_ Hown". destruct_ghost.
    iAssert (|==> ∃ voted', ghost_map_auth γv 1 voted' ∗
                  ⌜ vote_hist_ok voted' (s <| pstate.vote := m.(msg.from) |>) ⌝ ∗
                  ([∗ map] t ↦ c ∈ voted', is_vote γ id t c) ∗
                  is_vote γ id s.(pstate.term) m.(msg.from))%I
      with "[Hvoted]" as ">(%voted' & Hvoted & %Hhist' & #Hfrags' & #Hgrant)".
    { destruct Hcan as [Hsame | [Hnovote _]].
      - (* already voted for this candidate *)
        destruct Hhist as [Hdom Heq].
        assert (Hvnz : s.(pstate.vote) ≠ W64 0) by (rewrite Hsame; exact Hfrom).
        assert (Hlook : voted !! s.(pstate.term) = Some m.(msg.from)).
        { rewrite Heq decide_False //. by rewrite Hsame. }
        iExists voted. iFrame "Hvoted Hfrags".
        iDestruct (big_sepM_lookup _ _ _ _ Hlook with "Hfrags") as "#Hone".
        iFrame "Hone". iPureIntro.
        split; [exact Hdom|]. simpl. rewrite -Hsame. exact Heq.
      - (* first vote of this term *)
        assert (Hfree : voted !! s.(pstate.term) = None).
        { destruct Hhist as [_ Heq]. rewrite Heq decide_True //. }
        iMod (ghost_map_insert_persist s.(pstate.term) m.(msg.from) Hfree
               with "Hvoted") as "[Hvoted #Hnew]".
        iAssert (is_vote γ id s.(pstate.term) m.(msg.from)) as "#Hisvote".
        { iExists γv. by iFrame "#". }
        iModIntro. iExists (<[s.(pstate.term) := m.(msg.from)]> voted).
        iFrame "Hvoted Hisvote".
        iSplitR.
        + iPureIntro. destruct Hhist as [Hdom _]. split.
          * simpl. intros t [c Hc]. destruct (decide (t = s.(pstate.term)))
              as [->|Hne]; first lia.
            assert (Hne' : s.(pstate.term) ≠ t) by congruence.
            rewrite lookup_insert_ne // in Hc.
            unshelve epose proof (Hdom t _) as Hle; [by eexists|]. lia.
          * simpl. rewrite lookup_insert_eq decide_False //.
        + rewrite big_sepM_insert //. by iFrame "#". }
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted' Hname Hidnz
             with "Hvoted [] Hfrags' [] [] [] [Hlg]").
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist'); reflexivity.
    + rewrite /psend_msgs /=. rewrite big_sepL_app. iSplitR; [iFrame "#"|].
      rewrite big_sepL_singleton. by iApply is_message_grant.
    + rewrite /psend_msgs /=. iFrame "#".
    + rewrite /leader_wit /psend_msgs /=. iFrame "#".
    + iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.

  - (* step_reject_vote: a rejection carries nothing *)
    iIntros "_ Hown". destruct_ghost.
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] [] [Hlg]").
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
    + rewrite /psend_msgs /=. rewrite big_sepL_app. iSplitR; [iFrame "#"|].
      rewrite big_sepL_singleton. by iApply is_message_reject.
    + rewrite /psend_msgs /=. iFrame "#".
    + rewrite /leader_wit /psend_msgs /=. iFrame "#".
    + iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.

  - (* step_record_vote: a granting response is backed by the voter's vote *)
    iIntros "Hrecv Hown".
    iDestruct "Hrecv" as "[#Hm _]".
    destruct_ghost.
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] [] [Hlg]").
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
    + iFrame "#".
    + simpl. iApply big_sepS_intro. iIntros "!> %v %Hv".
      apply elem_of_granted_record_vote in Hv as [Hv | [-> Hb]].
      * by iApply (big_sepS_elem_of _ _ _ Hv with "Htally").
      * assert (Hrej : m.(msg.reject) = false)
          by (destruct (m.(msg.reject)); [discriminate Hb|reflexivity]).
        rewrite -Hterm -Hto.
        iApply (is_message_grant_inv γ m Hty Hrej with "Hm").
    + rewrite /leader_wit /=. iFrame "#".
    + iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.

  - (* step_win *)
    iIntros "_ Hown".
    by iMod (own_raft_ghost_step_win with "Hown") as "$".

  - (* step_lose: back to follower in the same term, so the vote stands *)
    iIntros "_ Hown". destruct_ghost.
    assert (Hhist' : vote_hist_ok voted
                       (pbecome_follower s s.(pstate.term) (W64 0))).
    { destruct Hhist as [Hdom Heq].
      rewrite /vote_hist_ok pbecome_follower_vote_same.
      split; simpl; [done|exact Heq]. }
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] [] [Hlg]").
    + iPureIntro. exact Hhist'.
    + by rewrite /pbecome_follower /=.
    + rewrite /pbecome_follower /= granted_empty big_sepS_empty //.
    + rewrite /leader_wit /pbecome_follower /=. done.
    + iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.

  - (* step_drain: the messages kept are messages that were there *)
    iIntros "_ Hown". destruct_ghost.
    iModIntro.
    iApply (own_raft_ghost_intro _ _ _ γv voted Hname Hidnz
             with "Hvoted [] Hfrags [] [] [] [Hlg]").
    + iPureIntro. apply (vote_hist_ok_eq _ _ _ Hhist); reflexivity.
    + simpl. iApply big_sepL_intro. iIntros "!> %k %x %Hk".
      iApply (big_sepL_elem_of with "Hout").
      eapply elem_of_submseteq; [by eapply list_elem_of_lookup_2|done].
    + simpl. iFrame "#".
    + rewrite /leader_wit /=. iFrame "#".
    + iApply (own_log_ghost_mono with "Hlg"); log_mono_tac.

  - (* step_app_accept (admitted lemma) *)
    iIntros "Hrecv Hown". iDestruct "Hrecv" as "[#Hm _]".
    by iMod (own_raft_ghost_step_app_accept with "Hm Hown") as "$".

  - (* step_app_stale *)
    iIntros "_ Hown".
    by iMod (own_raft_ghost_step_app_stale with "Hown") as "$".

  - (* step_app_reject *)
    iIntros "_ Hown".
    by iMod (own_raft_ghost_step_app_reject with "Hown") as "$".

  - (* step_heartbeat *)
    iIntros "Hrecv Hown". iDestruct "Hrecv" as "[#Hm _]".
    by iMod (own_raft_ghost_step_heartbeat with "Hm Hown") as "$".

  - (* step_beat *)
    iIntros "_ Hown".
    by iMod (own_raft_ghost_step_beat with "Hown") as "$".

  - (* step_app_resp *)
    iIntros "Hrecv Hown". iDestruct "Hrecv" as "[#Hm _]".
    by iMod (own_raft_ghost_step_app_resp with "Hm Hown") as "$".

  - (* step_commit *)
    iIntros "_ Hown".
    by iMod (own_raft_ghost_step_commit with "Hown") as "$".

  - (* step_send_apps *)
    iIntros "_ Hown".
    by iMod (own_raft_ghost_step_send_apps with "Hown") as "$".

  - (* step_propose (admitted lemma) *)
    iIntros "_ Hown".
    by iMod (own_raft_ghost_step_propose with "Hown") as "$".

  - (* step_prop_forward *)
    iIntros "_ Hown".
    by iMod (own_raft_ghost_step_prop_forward with "Hown") as "$".
Qed.

(** *** Protocol facts the code needs

    Each is a [Panicf] in the replication code that is dead only by protocol
    reasoning (notes/raft-replication-model.md, "Protocol facts the code
    needs").  A callee's spec takes the fact as a premise; [Step] derives it
    here, from the node's ghost state and the incoming message.  All three
    are ADMITTED. *)

(** [handleHeartbeat]'s [commitTo(m.Commit)] panics if [lastIndex() <
    m.Commit].  Informal argument: the leader sends [Commit: min(pr.Match,
    committed)], and [pr.Match] is acknowledged by the follower
    ([is_acked]) for this term; within one term a follower's log only grows
    past what it acknowledged to that term's leader (it only truncates on a
    conflict with an [App] of a different term), so its last index is at
    least the [Match]. *)
Lemma heartbeat_commit_le_last γ id ps m :
  m.(msg.ty) = mtype.Heartbeat →
  m.(msg.to) = id →
  m.(msg.term) = ps.(pstate.term) →
  ps.(pstate.role) ≠ role.Leader →
  own_raft_ghost γ id ps -∗ is_message γ m -∗
  ⌜ uint.Z m.(msg.commit) ≤ plog_last_index_Z ps.(pstate.base) ps.(pstate.log) ⌝.
Proof.
Admitted.

(** [maybeAppend]'s [commitTo(min(committed, lastnewi))] panics if the log
    ends before it.  Informal argument: after [plog_maybe_append] the log
    holds [m.entries] at indices [m.index+1 .. lastnewi] -- either they
    were all there already (no conflict) or they were appended -- provided
    [m.entries] has consecutive indices from [m.index+1], which is
    [app_ok]'s DEFERRED prefix clause carried by the message. *)
Lemma app_commit_le_lastnewi γ id ps m lastnewi es' :
  m.(msg.ty) = mtype.App →
  m.(msg.to) = id →
  m.(msg.term) = ps.(pstate.term) →
  plog_maybe_append ps.(pstate.base) ps.(pstate.log)
    (raft.entryID.mk m.(msg.logterm) m.(msg.index)) m.(msg.entries)
    = Some (lastnewi, es') →
  own_raft_ghost γ id ps -∗ is_message γ m -∗
  ⌜ uint.Z lastnewi ≤ plog_last_index_Z ps.(pstate.base) es' ⌝.
Proof.
Admitted.

(** [maybeAppend] panics if the first conflicting index is at or below the
    commit index ([ci ≤ l.committed]).  Informal argument: everything up
    to [committed] is committed (State Machine Safety) and hence in the
    log of every later leader (Leader Completeness), so the leader of
    [m.term] -- whose entries [m.entries] are -- agrees with this log up to
    [committed]; a conflict can only be above it. *)
Lemma app_no_conflict_below_commit γ id ps m lastnewi es' :
  m.(msg.ty) = mtype.App →
  m.(msg.to) = id →
  m.(msg.term) = ps.(pstate.term) →
  uint.Z ps.(pstate.commit) ≤ uint.Z m.(msg.index) →
  plog_maybe_append ps.(pstate.base) ps.(pstate.log)
    (raft.entryID.mk m.(msg.logterm) m.(msg.index)) m.(msg.entries)
    = Some (lastnewi, es') →
  own_raft_ghost γ id ps -∗ is_message γ m -∗
  ⌜ let ci := plog_find_conflict ps.(pstate.base) ps.(pstate.log) m.(msg.entries) in
    ci = W64 0 ∨ uint.Z ps.(pstate.commit) < uint.Z ci ⌝.
Proof.
Admitted.

(** *** Replication safety

    The three properties replication is for, as entailments between the
    ghost states of nodes.  ADMITTED, and -- while the DEFERRED premises in
    the rules are missing -- **not consequences of the model** (a vote
    request may carry any last-entry id, and an [App] any [logterm] and any
    entries of the leader's log).  They are stated so that the shape of the
    goal is fixed; the per-index half of Log Matching, [is_entry_agree], is
    proved. *)

(** The entry at index [i] of a log, if it is in the stored suffix. *)
Definition plog_entry_at (b : raft.entryID.t) (es : list raftpb.Entry.t) (i : w64)
  : option raftpb.Entry.t :=
  if decide (uint.Z i ≤ uint.Z b.(raft.entryID.index')) then None
  else es !! Z.to_nat (uint.Z i - uint.Z b.(raft.entryID.index') - 1).

(** Log Matching: two logs that have the same term at an index agree on
    every entry up to it.  Informal argument: by induction on the leader's
    term, using that a follower accepts an [App] only when it matches at
    [(logterm, index)] and that a leader never overwrites its own log. *)
Lemma log_matching γ id1 id2 s1 s2 (i t : w64) :
  plog_term_at s1.(pstate.base) s1.(pstate.log) i = Some t →
  plog_term_at s2.(pstate.base) s2.(pstate.log) i = Some t →
  own_raft_ghost γ id1 s1 -∗ own_raft_ghost γ id2 s2 -∗
  ⌜ ∀ j : w64, uint.Z j ≤ uint.Z i →
      uint.Z s1.(pstate.base).(raft.entryID.index') < uint.Z j →
      uint.Z s2.(pstate.base).(raft.entryID.index') < uint.Z j →
      plog_entry_at s1.(pstate.base) s1.(pstate.log) j =
      plog_entry_at s2.(pstate.base) s2.(pstate.log) j ⌝.
Proof.
Admitted.

(** Leader Completeness: an entry another node has committed, at a term no
    later than the leader's, is in the leader's log.  Informal argument:
    it was acknowledged by a quorum; the leader was elected by a quorum;
    the two meet in a voter whose log had the entry when it voted, and the
    [isUpToDate] check (DEFERRED premise of [step_grant_vote]) then puts
    the entry in the candidate's log. *)
Lemma leader_completeness γ id1 id2 s1 s2 (i : w64) e :
  s1.(pstate.role) = role.Leader →
  uint.Z s2.(pstate.term) ≤ uint.Z s1.(pstate.term) →
  uint.Z i ≤ uint.Z s2.(pstate.commit) →
  plog_entry_at s2.(pstate.base) s2.(pstate.log) i = Some e →
  uint.Z s1.(pstate.base).(raft.entryID.index') < uint.Z i →
  own_raft_ghost γ id1 s1 -∗ own_raft_ghost γ id2 s2 -∗
  ⌜ plog_entry_at s1.(pstate.base) s1.(pstate.log) i = Some e ⌝.
Proof.
Admitted.

(** State Machine Safety: two nodes agree on every index both have
    committed.  Informal argument: Log Matching plus Leader Completeness,
    as in the Raft paper (§5.4.3). *)
Lemma state_machine_safety γ id1 id2 s1 s2 (i : w64) :
  uint.Z i ≤ uint.Z s1.(pstate.commit) →
  uint.Z i ≤ uint.Z s2.(pstate.commit) →
  uint.Z s1.(pstate.base).(raft.entryID.index') < uint.Z i →
  uint.Z s2.(pstate.base).(raft.entryID.index') < uint.Z i →
  own_raft_ghost γ id1 s1 -∗ own_raft_ghost γ id2 s2 -∗
  ⌜ plog_entry_at s1.(pstate.base) s1.(pstate.log) i =
    plog_entry_at s2.(pstate.base) s2.(pstate.log) i ⌝.
Proof.
Admitted.

(** *** Allocation

    Nothing above says the ghost state is inhabited, and an empty
    [own_raft_ghost] would make every lemma here true and useless.  This is
    what rules that out: a fresh ghost state for any set of nodes, each in the
    initial protocol state -- an empty log. *)

Definition init_pstate : pstate.t :=
  {| pstate.term := W64 0; pstate.vote := W64 0; pstate.lead := W64 0;
     pstate.role := role.Follower; pstate.votes := ∅; pstate.outbox := [];
     pstate.base := raft.entryID.mk (W64 0) (W64 0); pstate.log := [];
     pstate.commit := W64 0; pstate.matched := ∅ |}.

Local Lemma alloc_maps {K V} `{Countable K} (ids : gset w64) :
  ⊢ |==> ∃ (names : gmap w64 gname),
      [∗ set] x ∈ ids, ∃ γx, ⌜ names !! x = Some γx ⌝ ∗
                             ghost_map_auth γx 1 (∅ : gmap K V).
Proof.
  induction ids as [|x ids Hx IH] using set_ind_L.
  - iModIntro. iExists ∅. rewrite big_sepS_empty. done.
  - iMod IH as (names) "Hm".
    iMod (ghost_map_alloc_empty (K:=K) (V:=V)) as (γx) "Hauth".
    iModIntro. iExists (<[x := γx]> names).
    rewrite big_sepS_insert //. iSplitL "Hauth".
    + iExists γx. rewrite lookup_insert_eq. by iFrame.
    + iApply (big_sepS_impl with "Hm"). iIntros "!> %y %Hy (%γy & %Hγy & Ha)".
      iExists γy. iFrame "Ha". iPureIntro.
      rewrite lookup_insert_ne //. intros ->. done.
Qed.

Lemma own_raft_ghost_alloc (cfg : gset w64) (ids : gset w64) :
  W64 0 ∉ ids →
  ⊢ |==> ∃ γ, ⌜ γ.(re_cfg) = cfg ⌝ ∗
      [∗ set] id ∈ ids, own_raft_ghost γ id init_pstate.
Proof.
  iIntros (Hnz).
  iMod (alloc_maps (K:=w64) (V:=w64) ids) as (nv) "Hv".
  iMod (alloc_maps (K:=w64) (V:=gname) ids) as (nt) "Ht".
  iMod (alloc_maps (K:=w64 * w64) (V:=unit) ids) as (na) "Ha".
  iModIntro. iExists {| re_cfg := cfg; re_votes := nv; re_terms := nt; re_acks := na |}.
  iSplit; first done.
  iCombine "Hv Ht Ha" as "H". rewrite -!big_sepS_sep.
  iApply (big_sepS_impl with "H").
  iIntros "!> %id %Hid ((%γv & %Hγv & Hav) & (%γm & %Hγm & Hat) & (%γa & %Hγa & Haa))".
  iExists γv, ∅.
  iSplit; first done.
  iSplit.
  { iPureIntro. intros ->. by apply Hnz. }
  iFrame "Hav".
  iSplit.
  { iPureIntro. split; [by intros t []|]. rewrite lookup_empty //. }
  rewrite big_sepM_empty big_sepL_nil granted_empty big_sepS_empty.
  rewrite /leader_wit /=.
  iSplit; first done. iSplit; first done. iSplit; first done. iSplit; first done.
  iExists γm, ∅, γa, ∅. iFrame "Hat Haa".
  rewrite !big_sepM_empty big_sepL_nil /lead_log_own /matched_ok /=.
  iSplit; first done. iSplit; first done.
  iSplit; first (iPureIntro; by intros t []).
  iSplit; first done. iSplit; first done. iSplit; first done. iSplit; first done.
  iApply is_committed_0.
Qed.

End ghost.

(** ** Derived conveniences used by [election.v] *)

Section lemmas.
Context `{!invGS Σ, !allG Σ}.
Implicit Type γ : raft_election_names.

(** Taking a step that consumes a single known message. *)
Lemma own_raft_ghost_step_1 γ id s m s' :
  step γ.(re_cfg) id s [m] s' →
  is_message γ m -∗
  own_raft_ghost γ id s ={⊤}=∗
  own_raft_ghost γ id s'.
Proof.
  iIntros (Hstep) "#Hm Hown".
  iMod (own_raft_ghost_step _ _ _ _ _ Hstep with "[] Hown") as "$".
  { by iFrame "#". }
  done.
Qed.

(** Taking a step that consumes nothing. *)
Lemma own_raft_ghost_step_0 γ id s s' :
  step γ.(re_cfg) id s [] s' →
  own_raft_ghost γ id s ={⊤}=∗ own_raft_ghost γ id s'.
Proof.
  iIntros (Hstep) "Hown".
  iMod (own_raft_ghost_step _ _ _ _ _ Hstep with "[] Hown") as "$".
  { done. }
  done.
Qed.

End lemmas.
