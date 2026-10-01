(** * Shared vocabulary for the election proof *)

Require Export New.proof.go_etcd_io.raft.v3_proof.base.
Require Export New.proof.go_etcd_io.raft.election_proof.protocol.

(** Discharge a goal [¬ (W32 a = W32 b)] for distinct literals. *)
Ltac w32_ne :=
  intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate.

(** Introduce the binders every [wp_<fn>_body] opens with.  The one place this
    list is written; see notes/gotchas.md. *)
Ltac intros_ambient :=
  intros ext ffi ffi_interp0 Σ hG ffi_semantics0 sem package_sem.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** ** Message-type constants, as Rocq values

    [raftpb.MessageType] is a [w32]; the Goose constants are opaque [val]s,
    so we name the underlying numbers ([raftpb.v:74-120]). *)
Definition MsgHup : w32 := W32 0.
Definition MsgProp : w32 := W32 2.
Definition MsgApp : w32 := W32 3.
Definition MsgAppResp : w32 := W32 4.
Definition MsgVote : w32 := W32 5.
Definition MsgVoteResp : w32 := W32 6.
Definition MsgSnap : w32 := W32 7.
Definition MsgHeartbeat : w32 := W32 8.
Definition MsgHeartbeatResp : w32 := W32 9.
Definition MsgReadIndex : w32 := W32 15.
Definition MsgReadIndexResp : w32 := W32 16.
Definition MsgPreVote : w32 := W32 17.
Definition MsgPreVoteResp : w32 := W32 18.
Definition MsgStorageAppendResp : w32 := W32 20.

Definition StateFollower : w64 := W64 0.
Definition StateCandidate : w64 := W64 1.
Definition StateLeader : w64 := W64 2.

Definition campaignElection : raft.CampaignType.t := "CampaignElection"%go.
Definition campaignPreElection : raft.CampaignType.t := "CampaignPreElection"%go.
Definition campaignTransfer : raft.CampaignType.t := "CampaignTransfer"%go.

Definition VotePending : w8 := W8 1.
Definition VoteLost : w8 := W8 2.
Definition VoteWon : w8 := W8 3.

Definition state_w64 (ro : role.t) : w64 :=
  match ro with
  | role.Follower => StateFollower
  | role.Candidate => StateCandidate
  | role.Leader => StateLeader
  end.

(** ** Abstraction of physical messages

    Every message type raft sends between nodes has an abstraction
    ([mtype.t]); the local ones ([MsgHup], [MsgBeat], [MsgStorage*],
    [MsgCheckQuorum], ...) do not, and [own_raft_phys] lets them drop out
    of the abstract outbox.  (Until 2026-10-01 only the four election types
    had one, and [MsgAppResp] -- which [appendEntry] queues -- dropped out
    too.) *)
Definition mtype_of (t : w32) : option mtype.t :=
  match uint.Z t with
  | 2 => Some mtype.Propose
  | 3 => Some mtype.App
  | 4 => Some mtype.AppResp
  | 5 => Some mtype.Vote
  | 6 => Some mtype.VoteResp
  | 7 => Some mtype.Snap
  | 8 => Some mtype.Heartbeat
  | 9 => Some mtype.HeartbeatResp
  | 15 => Some mtype.ReadIndex
  | 16 => Some mtype.ReadIndexResp
  | 17 => Some mtype.PreVote
  | 18 => Some mtype.PreVoteResp
  | _ => None
  end%Z.

Lemma mtype_of_MsgVote : mtype_of MsgVote = Some mtype.Vote.
Proof. reflexivity. Qed.
Lemma mtype_of_MsgVoteResp : mtype_of MsgVoteResp = Some mtype.VoteResp.
Proof. reflexivity. Qed.
Lemma mtype_of_MsgApp : mtype_of MsgApp = Some mtype.App.
Proof. reflexivity. Qed.
Lemma mtype_of_MsgAppResp : mtype_of MsgAppResp = Some mtype.AppResp.
Proof. reflexivity. Qed.
Lemma mtype_of_MsgHeartbeat : mtype_of MsgHeartbeat = Some mtype.Heartbeat.
Proof. reflexivity. Qed.
Lemma mtype_of_MsgHeartbeatResp : mtype_of MsgHeartbeatResp = Some mtype.HeartbeatResp.
Proof. reflexivity. Qed.
Lemma mtype_of_MsgSnap : mtype_of MsgSnap = Some mtype.Snap.
Proof. reflexivity. Qed.
Lemma mtype_of_MsgProp : mtype_of MsgProp = Some mtype.Propose.
Proof. reflexivity. Qed.

(** A message type the model does not describe is none of the ones it does. *)
Lemma mtype_of_None_ne (t : w32) :
  mtype_of t = None →
  t ≠ MsgProp ∧ t ≠ MsgApp ∧ t ≠ MsgAppResp ∧ t ≠ MsgVote ∧ t ≠ MsgVoteResp ∧
  t ≠ MsgSnap ∧ t ≠ MsgHeartbeat ∧ t ≠ MsgHeartbeatResp ∧ t ≠ MsgReadIndex ∧
  t ≠ MsgReadIndexResp ∧ t ≠ MsgPreVote ∧ t ≠ MsgPreVoteResp.
Proof. intros Hn. split_and!; intros ->; vm_compute in Hn; discriminate Hn. Qed.

(** The abstraction of a physical message [m] whose [Entries] slice holds
    [ents], with the sender and term given separately: [send] stamps both
    ([From := r.id] when unset, [Term := r.Term] for most types), so what
    reaches the queue is [m] with those two fields replaced. *)
Definition abs_msg_from (ty : mtype.t) (m : raftpb.Message.t) (from term : w64)
    (ents : list raftpb.Entry.t) : msg.t :=
  msg.mk ty from m.(raftpb.Message.To') term m.(raftpb.Message.Reject')
    m.(raftpb.Message.Index') m.(raftpb.Message.LogTerm')
    m.(raftpb.Message.Commit') m.(raftpb.Message.RejectHint') ents.

(** The abstraction of a physical message.  Not a function of [m] alone:
    [m.Entries] is a slice, and [ents] is the list it points to --
    [own_raft_phys] holds [m.Entries ↦*□ ents] for every queued message
    ([outbox_rel], [inv_raft_phys.v]). *)
Definition abs_msg (ty : mtype.t) (m : raftpb.Message.t)
    (ents : list raftpb.Entry.t) : msg.t :=
  abs_msg_from ty m m.(raftpb.Message.From') m.(raftpb.Message.Term') ents.

End proof.

(** The abstract state of a [raftLog]: what every [raftLog] spec is stated
    at.

    - [prev], [sents], [uents]: the entry list, as described above.
    - [committed], [applied]: [l.committed] and [l.applied].  Nothing on the
      election path writes them; they are in the state because
      [hasUnappliedConfChanges] and [maybeSendAppend] read them and a spec
      has to be able to say what was read.

    Every field is physical.  Until 2026-09-29 there was a sixth, [page]:
    a slice [raftLog.slice] had handed out while sharing memory with the
    log, on loan, with a wand back in [own_raftLog].  It went when the log
    started holding its entries read-only ([↦*□], [inv_raftlog.v]): a
    slice [slice] returns is then the caller's for good, and there is no
    loan to record.

    (Until 2026-09-23 the log had three shapes: [own_raftLog_at l prev sents
    uents], the existential [own_raftLog l], and the "page out" shape that
    [slice]/[entries] returned as [l ↦ lv ∗ s ↦*{dq} es ∗ (l ↦ lv -∗ s ↦*{dq}
    es -∗ own_raftLog_at …)].  notes/decisions.md, "One predicate per
    object".) *)
Module logstate.
Record t :=
  mk {
      prev : raft.entryID.t;
      sents : list raftpb.Entry.t;
      uents : list raftpb.Entry.t;
      committed : w64;
      applied : w64;
    }.
#[global] Instance settable : Settable t :=
  settable! mk <prev; sents; uents; committed; applied>.
End logstate.

(** After [destruct ls as [prev sents uents …]], reduce the projections the
    specs are written with.  Restricted to the five projections: a plain
    [simpl in *] near a struct points-to can run for minutes
    (notes/gotchas.md). *)
Ltac logstate_simpl :=
  cbn [logstate.prev logstate.sents logstate.uents logstate.committed
       logstate.applied] in *.

(** ** Physical transitions of the log

    [log_last ls] is [lastIndex()] of a log at [ls], as a [w64]; the
    [raftLog] specs return it as a [Z] equation, and [own_raftLog]'s
    [Hnowrap] says the [W64] does not wrap. *)
Definition log_last (ls : logstate.t) : w64 :=
  W64 (uint.Z ls.(logstate.prev).(raft.entryID.index')
       + Z.of_nat (length ls.(logstate.sents))
       + Z.of_nat (length ls.(logstate.uents))).

(** [raftLog.append] at the end of the log: the batch joins the unstable
    suffix ([spec_raftLog__append.v]). *)
Definition log_append (ls : logstate.t) (ents : list raftpb.Entry.t) : logstate.t :=
  ls <| logstate.uents := ls.(logstate.uents) ++ ents |>.

(** [stamp], [appendEntry]'s stamping loop, is in [protocol.v] (since
    2026-10-01: the model's [step_win] and [step_propose] stamp too). *)

(** * The physical abstract state

    [nstate.t] is what [own_raft_phys r id s] ([inv_raft_phys.v]) is indexed
    by: the **most abstract description of the raft struct and the heap
    hanging off it that still lets every Go-level spec be stated on
    [own_raft_phys] alone**.  It is the first of three layers
    (notes/decisions.md, "Three layers"):

      Go code and heap  --own_raft_phys-->  [nstate.t]
      [nstate.t]        --nstate_rel----->  [pstate.t]  (election_protocol.v)
      [pstate.t]        --own_raft_ghost->  protocol properties

    **The rule.**  If a function cannot be specified with [own_raft_phys],
    refine [nstate.t] (and [own_raft_phys] with it) until it can.  Do *not*
    introduce a variant predicate -- a second ownership predicate for the
    struct, or one with an extra parameter -- for one caller's benefit.
    Until 2026-09-22 there were three ([own_raft_phys_at] with a free
    [r.step], [own_raft_bare] and [own_raft_notrk] with the tracker and/or the
    log cut out), and every spec stated on one of them was a spec its callers
    had to convert into and out of.  The three fields below that are not
    protocol state replace them:

    - [stepfn] is [r.step].  [becomeFollower] writes it *before* calling
      [reset], and [newRaft] calls [becomeFollower] while it is still nil,
      so it cannot be a function of [role].
    - [progress] is the progress map, id to [*Progress].  Nothing on the
      election path inserts into or deletes from it, so it is stable across
      every call, and a proof that borrows one peer's [Progress] can hand it
      back before a call and borrow it again after, at the same key.
    - [prvals] is each peer's [Progress] *value*, with its [Inflights]
      value: what [*pr] and [*pr.Inflights] hold for the [pr] that
      [progress] maps the peer to.  [own_tracker] is indexed by it
      ([inv_tracker.v]), so a spec says how it changes the [Progress]es,
      or quantifies the new values.  [maybeSendAppend] needs it: it reads
      [pr] before [r.send] and calls [pr.SentEntries] after, which panics
      in [StateSnapshot] and, through [Inflights.Add], on a full window --
      so it must know, after a call made with the struct sealed, that [pr]
      still holds what it read.  (Until 2026-09-29 that was done by a field
      [lent : option ProgressTracker.t]: the tracker's heap was *lent* out
      of [own_raft_phys] to the caller, and every function that touched the
      tracker took [lent = None]; before 2026-09-21, the variant predicate
      [own_raft_bare].  A proposed replacement, a "pin" recording one
      [Progress] value, was rejected: [nstate.t] holds only physical
      state.)
    - [log] is [r.raftLog], the log's location (it never changes).
    - [logst] is the log's state ([logstate.t]).

    The first six fields are exactly [pstate.t]'s, with the same names, so
    that a spec's [s.(nstate.term)] reads the same as it always did. *)
Module nstate.
Section defn.
Context {ext : ffi_syntax}.
Record t :=
  mk {
      term : w64;
      vote : w64;
      lead : w64;
      role : role.t;
      votes : gmap w64 bool;
      outbox : list msg.t;
      stepfn : func.t;                (** [r.step] *)
      progress : gmap w64 loc;        (** [r.trk.Progress], as a map *)
      log : loc;                      (** [r.raftLog] *)
      logst : logstate.t;             (** the log's abstract state *)
      prvals : gmap w64 (tracker.Progress.t * tracker.Inflights.t);
                                      (** [*pr], [*pr.Inflights], per peer *)
    }.
End defn.
#[global] Instance settable {ext : ffi_syntax} : Settable (@t ext) :=
  settable! (@mk ext) <term; vote; lead; role; votes; outbox; stepfn; progress; log; logst; prvals>.
End nstate.

Section phys_state.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Implicit Type s : nstate.t.

(** Which of the three [stepX] functions [r.step] holds in each role.  The
    [becomeX] functions assign these, and [Step] dispatches a message it does
    not handle inline through [r.step(m)]. *)
Definition step_func_of (ro : role.t) : func.t :=
  match ro with
  | role.Follower => functions raft.stepFollower []
  | role.Candidate => functions raft.stepCandidate []
  | role.Leader => functions raft.stepLeader []
  end.

(** ** Transitions of the physical state

    Each mirrors a Go function exactly, [r.step] included, and leaves the
    fields the function does not write alone. *)

Definition send_msgs s (ms : list msg.t) : nstate.t :=
  s <| nstate.outbox := s.(nstate.outbox) ++ ms |>.

(** [reset(term)]: clears [Vote] only when the term actually changes, always
    clears [lead] and the tally. *)
Definition reset_to s (term : w64) : nstate.t :=
  s <| nstate.term := term |>
    <| nstate.vote := if decide (term = s.(nstate.term))
                      then s.(nstate.vote) else W64 0 |>
    <| nstate.lead := W64 0 |>
    <| nstate.votes := ∅ |>.

Definition become_follower s (term lead : w64) : nstate.t :=
  reset_to s term
    <| nstate.lead := lead |>
    <| nstate.role := role.Follower |>
    <| nstate.stepfn := step_func_of role.Follower |>.

Definition become_candidate (id : w64) s : nstate.t :=
  reset_to s (word.add s.(nstate.term) (W64 1))
    <| nstate.vote := id |>
    <| nstate.role := role.Candidate |>
    <| nstate.stepfn := step_func_of role.Candidate |>.

(** [becomeLeader] up to its [appendEntry]: what [reset], the [lead] and
    [state] writes and [r.step] leave. *)
Definition become_leader_pre (id : w64) s : nstate.t :=
  reset_to s s.(nstate.term)
    <| nstate.lead := id |>
    <| nstate.role := role.Leader |>
    <| nstate.stepfn := step_func_of role.Leader |>.

(** The empty entry a new leader appends ([pb.Entry{Data: nil}], the zero
    [Entry]), stamped at the leader's term and the log's next index. *)
Definition leader_entry s : raftpb.Entry.t :=
  stamp s.(nstate.term) (log_last s.(nstate.logst)) 0 (zero_val raftpb.Entry.t).

(** [appendEntry]'s self-acknowledgement, at a state whose log already holds
    the appended batch: a [MsgAppResp] to itself at the last index
    ([r.send(pb.Message{To: r.id, Type: pb.MsgAppResp, Index: li})], with
    [li] what [raftLog.append] returned).  Visible in the abstract outbox
    since 2026-10-01. *)
Definition self_ack (id : w64) s : msg.t :=
  msg.mk mtype.AppResp id id s.(nstate.term) false (log_last s.(nstate.logst))
    (W64 0) (W64 0) (W64 0) [].

(** [becomeLeader] up to [appendEntry]'s [send]: [become_leader_pre], then
    the empty entry appended. *)
Definition become_leader_log (id : w64) s : nstate.t :=
  become_leader_pre id s
    <| nstate.logst := log_append s.(nstate.logst) [leader_entry s] |>.

(** [becomeLeader]: the empty entry appended and self-acknowledged. *)
Definition become_leader (id : w64) s : nstate.t :=
  send_msgs (become_leader_log id s) [self_ack id (become_leader_log id s)].

(** ** The connection to the protocol state *)

(** Each peer's [Progress.Match]. *)
Definition prvals_match (pvs : gmap w64 (tracker.Progress.t * tracker.Inflights.t))
  : gmap w64 w64 :=
  (λ p, p.1.(tracker.Progress.Match')) <$> pvs.

(** Writing one peer's [Progress] without moving its [Match]. *)
Lemma prvals_match_insert_same pvs i p p' :
  pvs !! i = Some p →
  p'.1.(tracker.Progress.Match') = p.1.(tracker.Progress.Match') →
  prvals_match (<[i := p']> pvs) = prvals_match pvs.
Proof.
  intros Hi Hm. rewrite /prvals_match fmap_insert Hm.
  apply insert_id. rewrite lookup_fmap Hi //.
Qed.

(** What [reset] leaves in [Match] ([raft.go:779-808]): [0] for every peer
    in the progress map, then [lastIndex()] for the node itself. *)
Definition reset_matched (id li : w64)
    (pvs : gmap w64 (tracker.Progress.t * tracker.Inflights.t)) : gmap w64 w64 :=
  map_imap (λ k _, Some (if decide (k = id) then li else W64 0)) pvs.

(** [reset]'s [Match] values are what [step_win] asks of a new leader, when
    the node is in the progress map. *)
Lemma reset_matched_leader_ok id s :
  id ∈ dom s.(nstate.prvals) →
  ∀ ps, ps.(pstate.base) = s.(nstate.logst).(logstate.prev) →
        ps.(pstate.log) = s.(nstate.logst).(logstate.sents) ++ s.(nstate.logst).(logstate.uents) →
  leader_match_ok id ps (reset_matched id (log_last s.(nstate.logst)) s.(nstate.prvals)).
Proof.
  intros Hid ps Hb Hl. split.
  - apply elem_of_dom in Hid as [p Hp].
    rewrite /reset_matched map_lookup_imap Hp /=.
    rewrite decide_True; last done.
    rewrite /plast_index /plog_last_index_Z /log_last Hb Hl length_app.
    do 2 f_equal. lia.
  - intros v x Hne. rewrite /reset_matched map_lookup_imap.
    destruct (s.(nstate.prvals) !! v); simpl; [|done].
    rewrite decide_False; last done. intros Hx. by injection Hx as <-.
Qed.

(** [matched] is [Match] for a leader and [∅] otherwise ([pstate.t]): a
    non-leader's [Progress] values are whatever its last [reset] left, and
    no rule reads them.  This is what lets every non-leader spec leave the
    [Progress] values unconstrained. *)
Definition to_pstate s : pstate.t :=
  pstate.mk s.(nstate.term) s.(nstate.vote) s.(nstate.lead) s.(nstate.role)
            s.(nstate.votes) s.(nstate.outbox)
            s.(nstate.logst).(logstate.prev)
            (s.(nstate.logst).(logstate.sents) ++ s.(nstate.logst).(logstate.uents))
            s.(nstate.logst).(logstate.committed)
            (if decide (s.(nstate.role) = role.Leader)
             then prvals_match s.(nstate.prvals) else ∅).

(** A physical state that can take a protocol step: [r.step] agrees with
    the role.  Every [becomeX] establishes it. *)
Definition nstate_wf s : Prop :=
  s.(nstate.stepfn) = step_func_of s.(nstate.role).

(** [s] refines the protocol state [ps]. *)
Definition nstate_rel s (ps : pstate.t) : Prop :=
  to_pstate s = ps ∧ nstate_wf s.

(** What [maybeSendAppend] and its callers may send, at the state [s] they
    were called in: [repl_ok] ([protocol.v]) of the protocol reading of
    [s].  Replaced [app_sends] on 2026-10-01. *)
Definition repl_sends (id : w64) s (ms : list msg.t) : Prop :=
  Forall (repl_ok id (to_pstate s)) ms.

(** Each physical transition is its protocol counterpart on [to_pstate].
    Stated so that proofs rewrite rather than unfold. *)
Lemma to_pstate_send_msgs s ms :
  to_pstate (send_msgs s ms) = psend_msgs (to_pstate s) ms.
Proof. done. Qed.

Lemma to_pstate_become_follower s term lead :
  to_pstate (become_follower s term lead)
  = pbecome_follower (to_pstate s) term lead.
Proof. done. Qed.

(** [reset]'s conditional clear of the vote is overwritten by [vote := id]. *)
Lemma to_pstate_become_candidate id s :
  to_pstate (become_candidate id s) = pbecome_candidate id (to_pstate s).
Proof. done. Qed.

(** [lastIndex()] as the two layers write it. *)
Lemma plast_index_to_pstate s :
  plast_index (to_pstate s) = log_last s.(nstate.logst).
Proof.
  rewrite /plast_index /plog_last_index_Z /log_last /= length_app. f_equal. lia.
Qed.

Lemma leader_entry_to_pstate s :
  leader_entry s = pleader_entry (to_pstate s).
Proof. rewrite /leader_entry /pleader_entry plast_index_to_pstate //. Qed.

(** [becomeLeader], with the [Progress] values [reset] left: the protocol's
    win, up to its broadcast. *)
Lemma to_pstate_become_leader id s pvs :
  to_pstate (become_leader id s <| nstate.prvals := pvs |>)
  = psend_msgs (pwin_state id (to_pstate s) (prvals_match pvs))
      [pself_ack id (pwin_state id (to_pstate s) (prvals_match pvs))].
Proof.
  assert (Hw : to_pstate (become_leader_log id s <| nstate.prvals := pvs |>)
               = pwin_state id (to_pstate s) (prvals_match pvs)).
  { rewrite /become_leader_log /become_leader_pre /reset_to /to_pstate /pwin_state
      /pappend /pbecome_leader /= decide_True // -app_assoc leader_entry_to_pstate //. }
  rewrite /become_leader -Hw /pself_ack plast_index_to_pstate /self_ack //.
Qed.

Lemma to_pstate_votes s v :
  to_pstate (s <| nstate.votes := v |>) = to_pstate s <| pstate.votes := v |>.
Proof. done. Qed.

Lemma to_pstate_vote s v :
  to_pstate (s <| nstate.vote := v |>) = to_pstate s <| pstate.vote := v |>.
Proof. done. Qed.

Lemma nstate_wf_become_follower s term lead :
  nstate_wf (become_follower s term lead).
Proof. done. Qed.

Lemma nstate_wf_become_candidate id s :
  nstate_wf (become_candidate id s).
Proof. done. Qed.

Lemma nstate_wf_become_leader id s :
  nstate_wf (become_leader id s).
Proof. done. Qed.

(** A state with new [Progress] values is as well-formed as before: [r.step]
    and the role are untouched. *)
Lemma nstate_wf_prvals s pvs : nstate_wf s → nstate_wf (s <| nstate.prvals := pvs |>).
Proof. done. Qed.

(** New [Progress] values are invisible to the protocol unless the node is
    leader and [Match] moved. *)
Lemma to_pstate_prvals s pvs :
  (s.(nstate.role) = role.Leader → prvals_match pvs = prvals_match s.(nstate.prvals)) →
  to_pstate (s <| nstate.prvals := pvs |>) = to_pstate s.
Proof.
  intros H. rewrite /to_pstate /=.
  destruct (decide (s.(nstate.role) = role.Leader)) as [Hr|Hr]; last done.
  rewrite H //.
Qed.

(** The common case: a non-leader. *)
Lemma to_pstate_prvals_nl s pvs :
  s.(nstate.role) ≠ role.Leader →
  to_pstate (s <| nstate.prvals := pvs |>) = to_pstate s.
Proof. intros Hr. apply to_pstate_prvals. intros; congruence. Qed.

Lemma nstate_wf_send_msgs s ms : nstate_wf s → nstate_wf (send_msgs s ms).
Proof. done. Qed.

(** [repl_ok] reads only the term, the log and the commit index. *)
Lemma repl_ok_proper id (ps ps' : pstate.t) m :
  ps'.(pstate.term) = ps.(pstate.term) →
  ps'.(pstate.base) = ps.(pstate.base) →
  ps'.(pstate.log) = ps.(pstate.log) →
  ps'.(pstate.commit) = ps.(pstate.commit) →
  repl_ok id ps m → repl_ok id ps' m.
Proof.
  intros Ht Hb Hl Hc. rewrite /repl_ok /app_ok /snap_ok Ht Hb Hl Hc. done.
Qed.

Lemma repl_sends_prvals id s pvs ms :
  repl_sends id (s <| nstate.prvals := pvs |>) ms ↔ repl_sends id s ms.
Proof.
  rewrite /repl_sends. split; apply Forall_impl; intros m;
    apply repl_ok_proper; done.
Qed.

Lemma repl_sends_app id s ms1 ms2 :
  repl_sends id s ms1 → repl_sends id s ms2 → repl_sends id s (ms1 ++ ms2).
Proof. rewrite /repl_sends. apply Forall_app_2. Qed.

(** Sending messages, or changing [Progress] values, does not change what
    [repl_ok] reads. *)
Lemma repl_sends_send_prvals id s ms0 pvs ms :
  repl_sends id (send_msgs s ms0 <| nstate.prvals := pvs |>) ms ↔ repl_sends id s ms.
Proof.
  rewrite /repl_sends. split; apply Forall_impl; intros m;
    apply repl_ok_proper; done.
Qed.

End phys_state.
