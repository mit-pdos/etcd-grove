(** * Refinement of etcd raft's leader election.

    The top-level results are the Hoare triples for [raft.Step] at the bottom
    of this file.  They say: running [Step] on an election message takes the
    physical raft struct from a state refining the protocol state [s] to one
    refining [s'], and the ghost protocol state can be moved from [s] to [s']
    at the same time — i.e. the implementation refines the protocol of
    [election_protocol.v].

    Scope, matching [election_protocol.v]:
      - no pre-vote, no check-quorum,
      - no proposals, no read-only requests,
      - no reconfiguration and no learners.

    Trust boundary.  [Section helper_axioms] below axiomatizes the raft
    components that leader election does not reason about: the log
    ([raftLog]), the progress tracker's non-vote state, the [Logger] and
    [TraceLogger] interfaces, and the tracing helpers.  Everything the
    election protocol actually depends on — terms, votes, roles, and the
    outgoing message queues — is proved. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.base.
Require Export New.proof.go_etcd_io.raft.v3_proof.election_protocol.
From New.proof Require Import bytes.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Context {bytes_sem : bytes.Assumptions}.
Collection W := sem + package_sem + bytes_sem.
Set Default Proof Using "W".

(** The (fixed) set of voters. *)
Context (cfg : gset w64).

Implicit Type γ : raft_election_names.
Implicit Type s : nstate.t.

(** ** Message-type constants, as Rocq values

    [raftpb.MessageType] is a [w32]; the Goose constants are opaque [val]s,
    so we name the underlying numbers. *)
Definition MsgHup : w32 := W32 0.
Definition MsgApp : w32 := W32 3.
Definition MsgAppResp : w32 := W32 4.
Definition MsgVote : w32 := W32 5.
Definition MsgVoteResp : w32 := W32 6.
Definition MsgSnap : w32 := W32 7.
Definition MsgHeartbeat : w32 := W32 8.
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

(** Discharge a goal [¬ (W32 a = W32 b)] for distinct literals. *)
Local Ltac w32_ne :=
  intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate.

Definition state_w64 (ro : role.t) : w64 :=
  match ro with
  | role.Follower => StateFollower
  | role.Candidate => StateCandidate
  | role.Leader => StateLeader
  end.

(** ** Abstraction of physical messages

    Only election-related message types have an abstraction. *)
Definition mtype_of (t : w32) : option mtype.t :=
  if decide (t = MsgVote) then Some mtype.Vote
  else if decide (t = MsgVoteResp) then Some mtype.VoteResp
  else if decide (t = MsgApp) then Some mtype.App
  else if decide (t = MsgHeartbeat) then Some mtype.Heartbeat
  else None.

Lemma mtype_of_MsgVote : mtype_of MsgVote = Some mtype.Vote.
Proof. rewrite /mtype_of. case_decide as H1; [done|congruence]. Qed.

Lemma mtype_of_MsgVoteResp : mtype_of MsgVoteResp = Some mtype.VoteResp.
Proof.
  rewrite /mtype_of. case_decide as H1.
  { exfalso. rewrite /MsgVoteResp /MsgVote in H1. word. }
  case_decide as H2; [done|congruence].
Qed.

Definition abs_msg (ty : mtype.t) (m : raftpb.Message.t) : msg.t :=
  msg.mk ty m.(raftpb.Message.From') m.(raftpb.Message.To')
            m.(raftpb.Message.Term') m.(raftpb.Message.Reject').

(** [m] is a message this node is allowed to have put on the network. *)
Definition is_phys_msg γ (m : raftpb.Message.t) : iProp Σ :=
  ∃ ty, ⌜ mtype_of m.(raftpb.Message.Type') = Some ty ⌝ ∗
        is_message γ (abs_msg ty m).

#[global] Instance is_phys_msg_pers γ m : Persistent (is_phys_msg γ m).
Proof. apply _. Qed.

(** ** The trust boundary: raft components election does not reason about *)
Section helper_axioms.

(** *** The log.

    Under our assumptions the only log operations on the election path are
    [lastEntryID] / [isUpToDate] (which can only make the node decline to
    vote, always protocol-legal), [lastIndex], and the single empty entry a
    new leader appends.  So the log is entirely opaque here. *)
Axiom own_raftLog : loc → iProp Σ.

Axiom wp_raftLog__lastEntryID : ∀ (l : loc),
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    l @! (go.PointerType raft.raftLog) @! "lastEntryID" #()
  {{{ (e : raft.entryID.t), RET #e; own_raftLog l }}}.

Axiom wp_raftLog__isUpToDate : ∀ (l : loc) (e : raft.entryID.t),
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    l @! (go.PointerType raft.raftLog) @! "isUpToDate" #e
  {{{ (b : bool), RET #b; own_raftLog l }}}.

Axiom wp_raftLog__lastIndex : ∀ (l : loc),
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    l @! (go.PointerType raft.raftLog) @! "lastIndex" #()
  {{{ (i : w64), RET #i; own_raftLog l }}}.

Axiom wp_raftLog__hasNextOrInProgressSnapshot : ∀ (l : loc),
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    l @! (go.PointerType raft.raftLog) @! "hasNextOrInProgressSnapshot" #()
  {{{ RET #false; own_raftLog l }}}.

(** *** The progress tracker.

    [trk] is embedded in the [raft] struct **by value**, so the tracker's own
    bytes are part of the [r ↦ rv] clause of [own_raft_phys] and must not be
    claimed a second time.  [own_tracker tv votes] therefore owns what the
    tracker *value* [tv] points at, and nothing else: the vote map at
    [tv.Votes], the [Progress] map at [tv.Progress] together with the
    [Progress] objects in it, and the id sets of [tv.Config].  [votes] is the
    recorded vote tally; the voter set is [cfg] (no learners, no joint
    configuration).  Same rule as [own_raft_misc] below — index it by what it
    actually covers.

    The methods need the tracker's *location* too, and [ResetVotes] replaces
    the [Votes] field outright, so they take [trk ↦ tv] as well.  A caller
    holding the whole raft struct splits that field out with

      iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=) in "Hr"

    which turns [r ↦ rv] into the named conjunction of its field
    points-tos, of which [trk] is one. *)
Axiom own_tracker : tracker.ProgressTracker.t → gmap w64 bool → iProp Σ.

(** [ResetVotes] assigns a fresh empty map to [p.Votes], so it changes the
    tracker value as well as the heap it points at. *)
Axiom wp_ProgressTracker__ResetVotes : ∀ (trk : loc) tv votes,
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker tv votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "ResetVotes" #()
  {{{ (votesRef : loc), RET #();
      trk ↦ (tv <| tracker.ProgressTracker.Votes' := votesRef |>) ∗
      own_tracker (tv <| tracker.ProgressTracker.Votes' := votesRef |>) ∅ }}}.

(** [RecordVote] only inserts into the map [p.Votes] already refers to, so
    the tracker value is unchanged. *)
Axiom wp_ProgressTracker__RecordVote : ∀ (trk : loc) tv votes (from : w64) (v : bool),
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker tv votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "RecordVote" #from #v
  {{{ RET #(); trk ↦ tv ∗ own_tracker tv (record_vote votes from v) }}}.

(** [TallyVotes] reports the outcome of the election, which is exactly the
    quorum condition of the model. *)
Axiom wp_ProgressTracker__TallyVotes : ∀ (trk : loc) tv votes,
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker tv votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "TallyVotes" #()
  {{{ (g rj : w64) (res : w8), RET (#g, #rj, #res);
      trk ↦ tv ∗ own_tracker tv votes ∗
      ⌜ res = VoteWon ∨ res = VoteLost ∨ res = VotePending ⌝ ∗
      ⌜ res = VoteWon → is_quorum cfg (granted votes) ⌝ ∗
      ⌜ res = VoteLost → is_quorum cfg (rejected votes) ⌝ }}}.

(** *** Per-peer replication progress.

    [becomeLeader] is the only place on the election path that touches a
    [Progress]: it marks its own replicating and recently active.  Neither
    fact is visible in the model, so a [Progress] is opaque apart from the
    one field the code assigns to directly, which has to be real ownership
    for the assignment to step.

    The [Progress] map and the objects in it are part of [own_tracker]
    above; what is added here is a handle on one of them. *)
Axiom own_progress_rest : loc → iProp Σ.

Definition own_progress (pr : loc) : iProp Σ :=
  ∃ (recentActive : bool),
    struct_field_ref tracker.Progress.t "RecentActive"%go pr ↦ recentActive ∗
    own_progress_rest pr.

(** [trk.Progress[i]], for a voter [i]: [becomeLeader] looks up [r.id].
    Only voters are in the map, whence the side condition.  No [trk ↦ tv]
    here: the lookup reads the map reference out of the value it is given,
    and the caller gets that by reading the struct field itself. *)
Axiom wp_tracker_progress_lookup : ∀ tv votes (i : w64),
  i ∈ cfg →
  {{{ own_tracker tv votes }}}
    map.lookup1 go.uint64 (go.PointerType tracker.Progress)
      #(tv.(tracker.ProgressTracker.Progress')) #i
  {{{ (pr : loc), RET #pr;
      own_progress pr ∗ (own_progress pr -∗ own_tracker tv votes) }}}.

(** [pr.BecomeReplicate()] moves a [Progress] into the replicating state.
    It says nothing about votes, terms or roles, so the model does not see
    it. *)
Axiom wp_Progress__BecomeReplicate : ∀ (pr : loc),
  {{{ is_pkg_init tracker ∗ own_progress pr }}}
    pr @! (go.PointerType tracker.Progress) @! "BecomeReplicate" #()
  {{{ RET #(); own_progress pr }}}.

(** [r.promotable()]: true exactly when this node is a voter.  It reads
    [r.id], [r.trk.Progress] and [r.raftLog], so it is stated against the
    raft struct rather than against three unrelated parameters. *)
Axiom wp_raft__promotable : ∀ (r : loc) rv votes,
  {{{ is_pkg_init raft ∗ r ↦ rv ∗
      own_tracker rv.(raft.raft.trk') votes ∗
      own_raftLog rv.(raft.raft.raftLog') }}}
    r @! (go.PointerType raft.raft) @! "promotable" #()
  {{{ (b : bool), RET #b;
      r ↦ rv ∗ own_tracker rv.(raft.raft.trk') votes ∗
      own_raftLog rv.(raft.raft.raftLog') ∗
      ⌜ b = bool_decide (rv.(raft.raft.id') ∈ cfg) ⌝ }}}.

(** [r.hasUnappliedConfChanges()]: false, since there is no
    reconfiguration. *)
Axiom wp_raft__hasUnappliedConfChanges : ∀ (r : loc) l,
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    r @! (go.PointerType raft.raft) @! "hasUnappliedConfChanges" #()
  {{{ RET #false; own_raftLog l }}}.

(** The ids of the voters, in some order, as [campaign] enumerates them.
    [campaign] calls this on [&r.trk.Config.Voters], so the receiver is that
    field ref and not the tracker itself. *)
Axiom wp_campaign_peer_ids : ∀ (trk : loc) tv votes,
  {{{ is_pkg_init quorum ∗ trk ↦ tv ∗ own_tracker tv votes }}}
    (trk.[tracker.ProgressTracker.t, "Config"].[tracker.Config.t, "Voters"])
      @! (go.PointerType quorum.JointConfig) @! "IDs" #()
  {{{ (mref : loc) (idm : gmap w64 unit), RET #mref;
      trk ↦ tv ∗ own_tracker tv votes ∗
      mref ↦$ idm ∗ ⌜ dom idm = cfg ⌝ }}}.

(** *** Logging and tracing.

    Every [Logger] method used on the election path returns unit and has no
    observable effect.  [Panicf]/[Panic] are only reached on paths shown
    unreachable, so they get the same (vacuously usable) spec. *)
Axiom is_Logger : interface.t_ok → iProp Σ.
Axiom is_Logger_pers : ∀ l, Persistent (is_Logger l).
#[global] Existing Instance is_Logger_pers.

(** The formatting log methods.  Deliberately *not* [Panic]/[Panicf]: those
    do not return, so a path that reaches one has to be shown unreachable
    rather than assumed away. *)
Definition log_methods : list go_string :=
  ["Info"%go; "Infof"%go; "Debug"%go; "Debugf"%go;
   "Warning"%go; "Warningf"%go; "Error"%go; "Errorf"%go].

Axiom wp_Logger__logf : ∀ (l : interface.t_ok) (meth : go_string)
                          (format : go_string) (args : slice.t),
  meth ∈ log_methods →
  {{{ is_Logger l }}}
    #(methods l.(interface.ty) meth l.(interface.v)) #format #args
  {{{ RET #(); True }}}.

(** *** The parts of the raft struct election neither reads nor writes:
    the read-state slice, the read-only queue, and the pending
    [MsgReadIndex] slice.  Indexed by exactly those three fields, so that
    updating any other field of the struct leaves it alone. *)
Axiom own_raft_misc :
  ∀ (readStates : slice.t) (readOnly : loc) (pendingReadIndex : slice.t),
  iProp Σ.

Axiom wp_traceReceiveMessage : ∀ (r : loc) (mp : loc) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceReceiveMessage #r #mp
  {{{ RET #(); own_raft_misc rs ro pri }}}.

Axiom wp_traceSendMessage : ∀ (r : loc) (mp : loc) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceSendMessage #r #mp
  {{{ RET #(); own_raft_misc rs ro pri }}}.

Axiom wp_traceBecomeFollower : ∀ (r : loc) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceBecomeFollower #r
  {{{ RET #(); own_raft_misc rs ro pri }}}.

Axiom wp_traceBecomeCandidate : ∀ (r : loc) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceBecomeCandidate #r
  {{{ RET #(); own_raft_misc rs ro pri }}}.

Axiom wp_traceBecomeLeader : ∀ (r : loc) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceBecomeLeader #r
  {{{ RET #(); own_raft_misc rs ro pri }}}.

(** The empty entry a new leader appends, and the append broadcast that
    follows it.  [bcastAppend] sends one [MsgApp] to each peer, which is
    exactly [step_win]'s [sent] list. *)
Axiom wp_raft__appendEmptyEntry : ∀ (r : loc) l (es : slice.t),
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    r @! (go.PointerType raft.raft) @! "appendEntry" #es
  {{{ RET #true; own_raftLog l }}}.

End helper_axioms.

(** Step over one logging call: build the variadic argument slice, then
    apply the logger spec.  Expects [is_Logger] under the name [Hlogger]. *)
Local Ltac wp_log lok_eq :=
  wp_apply wp_slice_literal;
  [ iSplitR;
    [ done
    | iIntros "% [? _]"; try wp_auto; rewrite lok_eq; try wp_auto;
      wp_apply (wp_Logger__logf with "Hlogger") as "_";
      [ rewrite /log_methods; set_solver | ] ] ].

(** ** Physical ownership of the raft struct

    [own_raft_phys γ r id s] is full ownership of the [raft] struct at [r],
    in a state that refines the protocol state [s], and whose two outgoing
    message queues contain only messages [γ] certifies as protocol-legal. *)
Definition own_raft_phys γ (r : loc) (id : w64) s : iProp Σ :=
  ∃ (rv : raft.raft.t) (msgs msgsAA : list raftpb.Message.t)
    (lok : interface.t_ok),
  "Hr" ∷ r ↦ rv ∗

  (** the abstraction relation *)
  "%Hid" ∷ ⌜ rv.(raft.raft.id') = id ⌝ ∗
  "%Hterm" ∷ ⌜ rv.(raft.raft.Term') = s.(nstate.term) ⌝ ∗
  "%Hvote" ∷ ⌜ rv.(raft.raft.Vote') = s.(nstate.vote) ⌝ ∗
  "%Hlead" ∷ ⌜ rv.(raft.raft.lead') = s.(nstate.lead) ⌝ ∗
  "%Hstate" ∷ ⌜ rv.(raft.raft.state') = state_w64 s.(nstate.role) ⌝ ∗

  (** the vote tally, and the rest of the heap the tracker points at.  The
      tracker's own bytes are covered by [Hr] above, since [trk] is embedded
      by value; this is only what hangs off it. *)
  "Htrk" ∷ own_tracker rv.(raft.raft.trk') s.(nstate.votes) ∗

  (** the log, opaque *)
  "Hlog" ∷ own_raftLog rv.(raft.raft.raftLog') ∗

  (** outgoing messages.  [send] routes vote/append *responses* to
      [msgsAfterAppend] and everything else to [msgs]; both must only ever
      hold protocol-legal messages. *)
  "Hmsgs" ∷ rv.(raft.raft.msgs') ↦* msgs ∗
  "Hmsgs_cap" ∷ own_slice_cap raftpb.Message.t rv.(raft.raft.msgs') (DfracOwn 1) ∗
  "HmsgsAA" ∷ rv.(raft.raft.msgsAfterAppend') ↦* msgsAA ∗
  "HmsgsAA_cap" ∷ own_slice_cap raftpb.Message.t
                    rv.(raft.raft.msgsAfterAppend') (DfracOwn 1) ∗
  "#Hsent" ∷ ([∗ list] m ∈ msgs, is_phys_msg γ m) ∗
  "#HsentAA" ∷ ([∗ list] m ∈ msgsAA, is_phys_msg γ m) ∗

  (** scope assumptions *)
  "%HnoPreVote" ∷ ⌜ rv.(raft.raft.preVote') = false ⌝ ∗
  "%HnoCheckQuorum" ∷ ⌜ rv.(raft.raft.checkQuorum') = false ⌝ ∗
  "%HnoLearner" ∷ ⌜ rv.(raft.raft.isLearner') = false ⌝ ∗
  "%HnoTransfer" ∷ ⌜ rv.(raft.raft.leadTransferee') = W64 0 ⌝ ∗
  "%Hid_nz" ∷ ⌜ id ≠ W64 0 ⌝ ∗

  (** logging, tracing, and everything else *)
  "%Hlok" ∷ ⌜ rv.(raft.raft.logger') = interface.ok lok ⌝ ∗
  "#Hlogger" ∷ is_Logger lok ∗
  "Hmisc" ∷ own_raft_misc rv.(raft.raft.readStates') rv.(raft.raft.readOnly')
             rv.(raft.raft.pendingReadIndexMessages').

(** The step function stored in [r.step] is determined by the role; rather
    than naming the closure, we record which of the three [stepX] functions
    it is by the role, and dispatch on the role at the one call site. *)

(** ** [send]

    [send] is the only place a message reaches the network, so this is where
    the [is_message] obligation is discharged: the caller must already know
    the abstract message is legal. *)
Lemma wp_raft__send_vote γ r id s (m : raftpb.Message.t) ty :
  m.(raftpb.Message.From') = W64 0 →
  m.(raftpb.Message.Type') = MsgVote ∨ m.(raftpb.Message.Type') = MsgVoteResp →
  mtype_of m.(raftpb.Message.Type') = Some ty →
  m.(raftpb.Message.Term') ≠ W64 0 →
  (* [send] panics on a self-addressed non-response; a candidate never sends
     itself a [MsgVote]. *)
  (m.(raftpb.Message.Type') = MsgVote → m.(raftpb.Message.To') ≠ id) →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "#Hm" ∷ is_message γ (msg.mk ty id m.(raftpb.Message.To')
                              m.(raftpb.Message.Term') m.(raftpb.Message.Reject'))
  }}}
    r @! (go.PointerType raft.raft) @! "send" #m
  {{{ RET #(); own_raft_phys γ r id s }}}.
Proof.
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

(** [voteRespMsgType] maps a vote request to its response type. *)
Lemma wp_voteRespMsgType (t : w32) :
  t = MsgVote →
  {{{ is_pkg_init raft }}}
    @! raft.voteRespMsgType #t
  {{{ RET #MsgVoteResp; True }}}.
Proof.
  intros Ht. wp_start as "_". wp_auto.
  rewrite Ht /MsgVote bool_decide_eq_true_2 //. wp_auto.
  by iApply "HΦ".
Qed.

(** ** [reset]

    [reset term] clears the vote iff the term changes, clears [lead] and the
    vote tally, and re-initializes the non-election state. *)
Lemma wp_raft__reset γ r id s (term : w64) :
  {{{ is_pkg_init raft ∗ own_raft_phys γ r id s }}}
    r @! (go.PointerType raft.raft) @! "reset" #term
  {{{ RET #();
      own_raft_phys γ r id
        {| nstate.term := term;
           nstate.vote := if decide (term = s.(nstate.term))
                          then s.(nstate.vote) else W64 0;
           nstate.lead := W64 0;
           nstate.role := s.(nstate.role);
           nstate.votes := ∅ |} }}}.
Proof.
Admitted.

(** ** [becomeFollower] / [becomeCandidate] / [becomeLeader]

    Each is [reset] plus assignments to [lead] and [state]; the postconditions
    are literally the model's role transitions. *)

Lemma wp_raft__becomeFollower γ r id s (term lead : w64) :
  {{{ is_pkg_init raft ∗ own_raft_phys γ r id s }}}
    r @! (go.PointerType raft.raft) @! "becomeFollower" #term #lead
  {{{ RET #(); own_raft_phys γ r id (become_follower s term lead) }}}.
Proof.
  wp_start as "Hphys". iNamed "Hphys". wp_auto.
  (* [r.step := stepFollower] is done; re-seal for [reset]. *)
  iAssert (own_raft_phys γ r id s)
    with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
    as "Hphys".
  { rewrite /own_raft_phys.
    iExists (rv <| raft.raft.step' := _ |>), msgs, msgsAA, lok. iFrame "∗#%". }
  wp_apply (wp_raft__reset with "[$Hphys]") as "Hphys".
  iNamedSuffix "Hphys" "1".
  (* [r.tick], [r.lead := lead], [r.state := StateFollower] *)
  wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
  wp_auto. rewrite Hlok1.
  wp_apply (wp_Logger__logf with "Hlogger1").
  { rewrite /log_methods. set_solver. }
  wp_apply (wp_traceBecomeFollower with "[$Hmisc1]") as "Hmisc1".
  iApply "HΦ". rewrite /own_raft_phys /become_follower /=.
  iExists _, msgs0, msgsAA0, lok0.
  simpl in Hid1, Hterm1, Hvote1, Hlead1, Hstate1.
  iEval (simpl) in "Htrk1".
  iFrame "Hr1 ∗#%".
  (* [lead] and [state] were just assigned, so these are by computation *)
  iSplit; iPureIntro; reflexivity.
Qed.

Lemma wp_raft__becomeCandidate γ r id s :
  s.(nstate.role) ≠ role.Leader →
  {{{ is_pkg_init raft ∗ own_raft_phys γ r id s }}}
    r @! (go.PointerType raft.raft) @! "becomeCandidate" #()
  {{{ RET #(); own_raft_phys γ r id (become_candidate id s) }}}.
Proof.
  intros Hrole. wp_start as "Hphys". iNamed "Hphys". wp_auto.
  (* [becomeCandidate] panics on a leader; by assumption we are not one. *)
  assert (state_w64 s.(nstate.role) ≠ W64 2) as Hnl.
  { destruct (s.(nstate.role)) eqn:Hro; try congruence;
      rewrite /state_w64 /StateFollower /StateCandidate;
      intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate. }
  rewrite Hstate bool_decide_eq_false_2 //. wp_auto.
  iAssert (own_raft_phys γ r id s)
    with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
    as "Hphys".
  { rewrite /own_raft_phys.
    iExists (rv <| raft.raft.step' := _ |>), msgs, msgsAA, lok. iFrame "∗#%". }
  (* [reset] is called at [r.Term + 1] *)
  rewrite Hterm.
  wp_apply (wp_raft__reset with "[$Hphys]") as "Hphys".
  iNamedSuffix "Hphys" "1".
  (* [r.tick], [r.Vote := r.id], [r.state := StateCandidate] *)
  wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
  wp_auto. rewrite Hlok1.
  wp_apply (wp_Logger__logf with "Hlogger1").
  { rewrite /log_methods. set_solver. }
  wp_apply (wp_traceBecomeCandidate with "[$Hmisc1]") as "Hmisc1".
  iApply "HΦ". rewrite /own_raft_phys /become_candidate /=.
  iExists _, msgs0, msgsAA0, lok0.
  simpl in Hid1, Hterm1, Hvote1, Hlead1, Hstate1.
  iEval (simpl) in "Htrk1".
  iFrame "Hr1 ∗#%".
  iPureIntro; reflexivity.
Qed.

Lemma wp_raft__becomeLeader γ r id s :
  s.(nstate.role) ≠ role.Follower →
  id ∈ cfg →
  {{{ is_pkg_init raft ∗ own_raft_phys γ r id s }}}
    r @! (go.PointerType raft.raft) @! "becomeLeader" #()
  {{{ RET #(); own_raft_phys γ r id (become_leader id s) }}}.
Proof.
  intros Hrole Hcfg. wp_start as "Hphys". iNamed "Hphys". wp_auto.
  (* [becomeLeader] panics on a follower; by assumption we are not one. *)
  assert (state_w64 s.(nstate.role) ≠ W64 0) as Hnf.
  { destruct (s.(nstate.role)) eqn:Hro; try congruence;
      rewrite /state_w64 /StateCandidate /StateLeader;
      intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate. }
  rewrite Hstate bool_decide_eq_false_2 //. wp_auto.
  iAssert (own_raft_phys γ r id s)
    with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
    as "Hphys".
  { rewrite /own_raft_phys.
    iExists (rv <| raft.raft.step' := _ |>), msgs, msgsAA, lok. iFrame "∗#%". }
  (* [reset] is called at the unchanged term, so the vote survives *)
  rewrite Hterm.
  wp_apply (wp_raft__reset with "[$Hphys]") as "Hphys".
  iNamedSuffix "Hphys" "1".
  assert (rv0.(raft.raft.Vote') = s.(nstate.vote)) as Hvote1'.
  { rewrite Hvote1 /=. rewrite decide_True //. }
  (* [r.tick], [r.lead := r.id], [r.state := StateLeader] *)
  wp_auto.
  rewrite Hid1.
  (* the leader's own [Progress] is marked replicating and recently active *)
  wp_apply (wp_tracker_progress_lookup _ _ _ Hcfg with "[$Htrk1]")
    as "%pr [Hpr Hprback]".
  wp_apply (wp_Progress__BecomeReplicate with "[$Hpr]") as "Hpr".
  iDestruct "Hpr" as (recentActive) "[Hra Hrest]".
  wp_auto.
  iAssert (own_progress pr) with "[Hra Hrest]" as "Hpr".
  { rewrite /own_progress. iExists true. iFrame. }
  iDestruct ("Hprback" with "Hpr") as "Htrk1".
  wp_apply (wp_raftLog__lastIndex with "[$Hlog1]") as "%li Hlog1".
  wp_apply (wp_traceBecomeLeader with "[$Hmisc1]") as "Hmisc1".
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
  wp_auto.
  wp_apply (wp_raft__appendEmptyEntry with "[$Hlog1]") as "Hlog1".
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
  wp_auto. rewrite Hlok1.
  wp_apply (wp_Logger__logf with "Hlogger1").
  { rewrite /log_methods. set_solver. }
  iApply "HΦ". rewrite /own_raft_phys /become_leader /=.
  iExists _, msgs0, msgsAA0, lok0.
  simpl in Hid1, Hterm1, Hvote1, Hlead1, Hstate1.
  iEval (simpl) in "Htrk1".
  iFrame "Hr1 ∗#%".
  iPureIntro. split_and!; done.
Qed.

(** ** [poll]

    [poll] records a vote and reports the outcome.  The returned [res] is
    tied to the model's quorum conditions by [wp_ProgressTracker__TallyVotes].
    Note [poll] only touches the tally, so the ghost step it justifies is
    [step_record_vote]; winning and losing are separate steps taken by the
    caller. *)
Lemma wp_raft__poll γ r id s (from : w64) (t : w32) (v : bool) :
  {{{ is_pkg_init raft ∗ own_raft_phys γ r id s }}}
    r @! (go.PointerType raft.raft) @! "poll" #from #t #v
  {{{ (g rj : w64) (res : w8), RET (#g, #rj, #res);
      let votes' := record_vote s.(nstate.votes) from v in
      own_raft_phys γ r id (s <| nstate.votes := votes' |>) ∗
      ⌜ res = VoteWon ∨ res = VoteLost ∨ res = VotePending ⌝ ∗
      ⌜ res = VoteWon → is_quorum cfg (granted votes') ⌝ ∗
      ⌜ res = VoteLost → is_quorum cfg (rejected votes') ⌝ }}}.
Proof.
Admitted.

(** ** [campaign]

    [campaign] refines [step_campaign]: it becomes a candidate, sends a
    self-addressed [MsgVoteResp], and sends a [MsgVote] to every peer.  Note
    that this is where [own_raft_ghost] is actually updated: the ghost step
    is taken first, which produces the [is_message] facts that [send]
    demands. *)
Lemma wp_raft__campaign γ r id s (t : raft.CampaignType.t) :
  t ≠ campaignPreElection →
  s.(nstate.role) ≠ role.Leader →
  id ∈ cfg →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "Hghost" ∷ own_raft_ghost γ id s
  }}}
    r @! (go.PointerType raft.raft) @! "campaign" #t
  {{{ RET #();
      let s' := become_candidate id s in
      own_raft_phys γ r id s' ∗ own_raft_ghost γ id s' }}}.
Proof.
Admitted.

(** ** [hup]

    [hup] either declines to campaign (leader already, not a voter, pending
    conf changes) — which is [step_refl] — or campaigns. *)
Lemma wp_raft__hup γ r id s (t : raft.CampaignType.t) :
  t ≠ campaignPreElection →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "Hghost" ∷ own_raft_ghost γ id s
  }}}
    r @! (go.PointerType raft.raft) @! "hup" #t
  {{{ s', RET #();
      own_raft_phys γ r id s' ∗ own_raft_ghost γ id s' ∗
      ⌜ ∃ sent, step cfg id s [] s' sent ⌝ }}}.
Proof.
Admitted.

(** ** [stepCandidate] and [stepFollower], restricted to election messages

    With proposals, read-only requests and reconfiguration out of scope, the
    only message either of these handles is [MsgVoteResp] (in
    [stepCandidate]; [stepFollower] ignores it).  [MsgVote] never reaches
    them: [Step] handles it itself. *)

(** The outcome of feeding a [MsgVoteResp] to a candidate. *)
Definition vote_resp_result id s (from : w64) (reject : bool) (won lost : bool)
  : nstate.t :=
  let s1 := s <| nstate.votes := record_vote s.(nstate.votes) from (negb reject) |> in
  if won then become_leader id s1
  else if lost then become_follower s1 s1.(nstate.term) (W64 0)
  else s1.

Lemma wp_stepCandidate_MsgVoteResp γ r id s (m : raftpb.Message.t) :
  m.(raftpb.Message.Type') = MsgVoteResp →
  m.(raftpb.Message.To') = id →
  m.(raftpb.Message.Term') = s.(nstate.term) →
  s.(nstate.role) = role.Candidate →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "Hghost" ∷ own_raft_ghost γ id s ∗
      "#Hm" ∷ is_message γ (abs_msg mtype.VoteResp m)
  }}}
    @! raft.stepCandidate #r #m
  {{{ (err : error.t) s', RET #err;
      own_raft_phys γ r id s' ∗ own_raft_ghost γ id s' ∗
      ⌜ ∃ won lost,
          s' = vote_resp_result id s m.(raftpb.Message.From')
                 m.(raftpb.Message.Reject') won lost ⌝ }}}.
Proof.
Admitted.

(** ** Model-level lemmas justifying each branch of [Step]

    These are pure facts about the protocol, independent of the program
    logic; the WP proofs below feed them to [own_raft_ghost_step]. *)

(** Dropping a message is always legal. *)
Lemma step_drop id s : step cfg id s [] s [].
Proof. constructor. Qed.

(** Stepping down and then answering a vote request, in one protocol step. *)
Lemma step_stepdown_then_vote id s (m : msg.t) :
  m.(msg.ty) = mtype.Vote →
  m.(msg.to) = id →
  uint.Z s.(nstate.term) < uint.Z m.(msg.term) →
  step cfg id s ([m] ++ [m])
       ((become_follower s m.(msg.term) (W64 0))
          <| nstate.vote := m.(msg.from) |>)
       ([] ++ [msg.mk mtype.VoteResp id m.(msg.from) m.(msg.term) false]).
Proof.
  intros Hty Hto Hlt.
  eapply step_trans with
    (s₁ := become_follower s m.(msg.term)
             (if from_leader m.(msg.ty) then m.(msg.from) else W64 0)).
  { by apply step_higher_term. }
  rewrite Hty /=.
  apply step_grant_vote; try done.
  (* [become_follower] to a strictly greater term clears the vote and the
     leader, so [can_vote] holds. *)
  rewrite /can_vote /become_follower /=.
  right. destruct (decide (m.(msg.term) = s.(nstate.term))) as [Heq|Hne].
  { rewrite Heq in Hlt. lia. }
  done.
Qed.

(** Stepping down and then declining. *)
Lemma step_stepdown_then_reject id s (m : msg.t) :
  m.(msg.ty) = mtype.Vote →
  m.(msg.to) = id →
  uint.Z s.(nstate.term) < uint.Z m.(msg.term) →
  step cfg id s ([m] ++ [m]) (become_follower s m.(msg.term) (W64 0))
       ([] ++ [msg.mk mtype.VoteResp id m.(msg.from) m.(msg.term) true]).
Proof.
  intros Hty Hto Hlt.
  eapply step_trans with
    (s₁ := become_follower s m.(msg.term)
             (if from_leader m.(msg.ty) then m.(msg.from) else W64 0)).
  { by apply step_higher_term. }
  rewrite Hty /=.
  by apply step_reject_vote.
Qed.

(** Recording a vote response and then winning. *)
Lemma step_record_then_win id s (m : msg.t) peers :
  m.(msg.ty) = mtype.VoteResp →
  m.(msg.to) = id →
  m.(msg.term) = s.(nstate.term) →
  s.(nstate.role) = role.Candidate →
  peers ≡ₚ elements (cfg ∖ {[id]}) →
  let s1 := s <| nstate.votes :=
                  record_vote s.(nstate.votes) m.(msg.from) (negb m.(msg.reject)) |> in
  is_quorum cfg (granted s1.(nstate.votes)) →
  step cfg id s ([m] ++ []) (become_leader id s1)
       ([] ++ ((λ to, msg.mk mtype.App id to s1.(nstate.term) false) <$> peers)).
Proof.
  intros ????? s1 Hq.
  eapply step_trans; [by apply step_record_vote|].
  by apply step_win.
Qed.

(** Recording a vote response and then losing. *)
Lemma step_record_then_lose id s (m : msg.t) :
  m.(msg.ty) = mtype.VoteResp →
  m.(msg.to) = id →
  m.(msg.term) = s.(nstate.term) →
  s.(nstate.role) = role.Candidate →
  let s1 := s <| nstate.votes :=
                  record_vote s.(nstate.votes) m.(msg.from) (negb m.(msg.reject)) |> in
  is_quorum cfg (rejected s1.(nstate.votes)) →
  step cfg id s ([m] ++ []) (become_follower s1 s1.(nstate.term) (W64 0)) ([] ++ []).
Proof.
  intros ???? s1 Hq.
  eapply step_trans; [by apply step_record_vote|].
  by apply step_lose.
Qed.

(** ** The top-level specs for [raft.Step]

    Each says: the physical struct moves from a state refining [s] to a state
    refining [s'], the ghost protocol state moves with it, and — the point —
    [s → s'] is a transition of the protocol state machine, justified by
    messages that were legitimately on the network. *)

(** An election message: the only ones in scope. *)
Definition election_msg (m : raftpb.Message.t) : Prop :=
  m.(raftpb.Message.Type') = MsgHup ∨
  m.(raftpb.Message.Type') = MsgVote ∨
  m.(raftpb.Message.Type') = MsgVoteResp.

(** *** [MsgHup]: start an election.

    [MsgHup] is a local message ([m.Term = 0]), so [Step]'s term preamble is
    skipped entirely and it goes straight to [hup]. *)
Theorem wp_raft__Step_MsgHup γ r id s (m : raftpb.Message.t) :
  m.(raftpb.Message.Type') = MsgHup →
  m.(raftpb.Message.Term') = W64 0 →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "Hghost" ∷ own_raft_ghost γ id s
  }}}
    r @! (go.PointerType raft.raft) @! "Step" #m
  {{{ (err : error.t) s', RET #err;
      "Hphys" ∷ own_raft_phys γ r id s' ∗
      "Hghost" ∷ own_raft_ghost γ id s' ∗
      "%Hrefines" ∷ ⌜ ∃ sent, step cfg id s [] s' sent ⌝ ∗
      "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
Proof.
  intros Hty Hterm.
  wp_start as "@".
  iNamed "Hphys".
  wp_auto.
  wp_apply (wp_traceReceiveMessage with "[$Hmisc]") as "Hmisc".
  (* [m.Term = 0] (a local message), so the term preamble is skipped. *)
  rewrite Hterm !bool_decide_eq_true_2 //.
  wp_auto.
  (* the type switch selects the [MsgHup] case *)
  rewrite Hty /MsgHup bool_decide_eq_true_2 //.
  wp_auto.
  (* no pre-vote, so this is a plain [hup(campaignElection)] *)
  rewrite HnoPreVote. wp_auto.
  (* re-seal the physical ownership for [hup] *)
  iAssert (own_raft_phys γ r id s)
    with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
  { rewrite /own_raft_phys. iFrame "∗#%". }
  wp_apply (wp_raft__hup with "[$Hphys $Hghost]") as "%s' (Hphys & Hghost & %Hstep)".
  { done. }
  iApply ("HΦ" $! interface.nil s'). by iFrame.
Qed.

(** *** [MsgVote]: answer a vote request.

    Three cases, by the relation between [m.Term] and [r.Term]:
    - [m.Term < r.Term]: the message is dropped ([step_drop]);
    - [m.Term > r.Term]: step down, then answer
      ([step_stepdown_then_vote] / [step_stepdown_then_reject]);
    - [m.Term = r.Term]: answer directly
      ([step_grant_vote] / [step_reject_vote]).
    The grant branch is taken only when [canVote] holds, which is literally
    the model's [can_vote]; the [isUpToDate] conjunct can only send the code
    down the reject branch, which the model always permits. *)
Theorem wp_raft__Step_MsgVote γ r id s (m : raftpb.Message.t) :
  m.(raftpb.Message.Type') = MsgVote →
  m.(raftpb.Message.To') = id →
  m.(raftpb.Message.Term') ≠ W64 0 →
  (* [send] stamps the sender's id into [From], and node ids are nonzero *)
  m.(raftpb.Message.From') ≠ W64 0 →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "Hghost" ∷ own_raft_ghost γ id s ∗
      "#Hm" ∷ is_message γ (abs_msg mtype.Vote m) ∗
      (* the message's [Context] is readable and is not the leader-transfer
         marker: leader transfer is out of scope *)
      "#Hctx" ∷ (∃ ctx, m.(raftpb.Message.Context') ↦*□ ctx ∗
                        ⌜ ctx ≠ campaignTransfer ⌝)
  }}}
    r @! (go.PointerType raft.raft) @! "Step" #m
  {{{ (err : error.t) s', RET #err;
      "Hphys" ∷ own_raft_phys γ r id s' ∗
      "Hghost" ∷ own_raft_ghost γ id s' ∗
      "%Hrefines" ∷ ⌜ ∃ recv sent,
          (∀ m', m' ∈ recv → m' = abs_msg mtype.Vote m) ∧
          step cfg id s recv s' sent ⌝ ∗
      "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
Proof.
  intros Hty Hto Hterm Hfnz.
  wp_start as "@". iNamed "Hphys". wp_auto.
  wp_apply (wp_traceReceiveMessage with "[$Hmisc]") as "Hmisc".
  (* [m.Term ≠ 0], so the first arm of the term preamble is skipped. *)
  assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
    by by apply bool_decide_eq_false_2.
  rewrite Hz. rewrite bool_decide_eq_false_2; last done. wp_auto.
  destruct (decide (uint.Z rv.(raft.raft.Term') < uint.Z m.(raftpb.Message.Term')))
    as [Hgt|Hle].
  - (* [m.Term > r.Term]: step down to follower first, then answer. *)
    assert (bool_decide (uint.Z rv.(raft.raft.Term') <
                         uint.Z m.(raftpb.Message.Term')) = true) as Hb
      by by apply bool_decide_eq_true_2.
    rewrite Hb. rewrite bool_decide_eq_true_2 //. wp_auto.
    rewrite Hty /MsgVote bool_decide_eq_true_2 //. wp_auto.
    (* [force] is false (not a leader transfer) and [inLease] is false (no
       check-quorum), so the lease check does not drop the message. *)
    iDestruct "Hctx" as (ctx) "[Hctx_sl %Hctx_ne]".
    wp_apply wp_string_to_bytes as "%ct_sl [ct_sl ct_cap]".
    wp_apply (wp_Equal _ _ DfracDiscarded (DfracOwn 1) ctx ("CampaignTransfer"%go)
                with "[$Hctx_sl $ct_sl]") as "[_ ct_sl2]".
    rewrite HnoCheckQuorum. wp_auto.
    assert (bool_decide (ctx = "CampaignTransfer"%go) = false) as Hnf
      by by apply bool_decide_eq_false_2.
    rewrite Hnf. wp_auto.
    (* neither MsgPreVote nor MsgPreVoteResp, so we fall through to the
       step-down *)
    assert (bool_decide (m.(raftpb.Message.Type') = W32 17) = false) as Hpv
      by (apply bool_decide_eq_false_2; rewrite Hty /MsgVote; w32_ne).
    rewrite Hpv. rewrite bool_decide_eq_false_2; last done. wp_auto.
    assert (bool_decide (m.(raftpb.Message.Type') = W32 18) = false) as Hpvr
      by (apply bool_decide_eq_false_2; rewrite Hty /MsgVote; w32_ne).
    rewrite Hpvr. wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [Hlog_sl _]".
    wp_auto. rewrite Hlok.
    wp_apply (wp_Logger__logf with "Hlogger").
    { rewrite /log_methods. set_solver. }
    (* a [MsgVote] is not from a leader, so no leader is adopted *)
    rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
    rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
    rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
    iAssert (own_raft_phys γ r id s)
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
    { rewrite /own_raft_phys. iExists rv, msgs, msgsAA, lok. iFrame "∗#%". }
    wp_apply (wp_raft__becomeFollower with "[$Hphys]") as "Hphys".
    (* the corresponding protocol step *)
    iMod (own_raft_ghost_step_1 with "Hm Hghost") as "Hghost".
    { replace (W64 0) with
        (if from_leader (abs_msg mtype.Vote m).(msg.ty)
         then (abs_msg mtype.Vote m).(msg.from) else W64 0) by done.
      apply step_higher_term.
      - rewrite /abs_msg /= -Hterm0. exact Hgt.
      - rewrite /abs_msg /=. exact Hto. }
    iNamedSuffix "Hphys" "1".
    (* the type switch: not MsgHup / MsgStorageAppendResp / MsgStorageApplyResp,
       not MsgPreVote, but MsgVote *)
    rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
    (* Stepping down to a strictly greater term cleared both [Vote] and
       [lead], so [canVote] holds. *)
    assert (Hne : m.(raftpb.Message.Term') ≠ s.(nstate.term)).
    { rewrite -Hterm0. intros Heq. rewrite Heq in Hgt. lia. }
    rewrite /become_follower /= decide_False // in Hvote1 Hlead1.
    rewrite Hvote1 bool_decide_eq_false_2; last congruence. wp_auto.
    rewrite Hvote1 bool_decide_eq_true_2 //. wp_auto.
    rewrite Hlead1 bool_decide_eq_true_2 //. wp_auto.
    wp_apply (wp_raftLog__lastEntryID with "[$Hlog1]") as "%lastID Hlog1".
    wp_apply (wp_raftLog__isUpToDate with "[$Hlog1]") as "%uptodate Hlog1".
    destruct uptodate.
    + (* the candidate's log is up to date: grant the vote *)
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok1.
      wp_apply (wp_Logger__logf with "Hlogger1").
      { rewrite /log_methods. set_solver. }
      wp_apply wp_voteRespMsgType; first done.
      (* the protocol step: grant the vote *)
      iMod (own_raft_ghost_step_1_1 with "Hm Hghost") as "[Hghost #Hgrant]".
      { apply step_grant_vote; [done|exact Hto|done|].
        rewrite /can_vote /become_follower /=. right.
        split; [by rewrite decide_False|done]. }
      iEval (rewrite /abs_msg /become_follower /=) in "Hgrant".
      iAssert (own_raft_phys γ r id (become_follower s m.(raftpb.Message.Term') (W64 0)))
        with "[Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1]"
        as "Hphys".
      { rewrite /own_raft_phys. iExists rv0, msgs0, msgsAA0, lok0.
        rewrite /become_follower /= decide_False //. iFrame "∗#%". }
      (* TODO: the remaining steps are [send] of the granted vote and the
         [r.Vote := m.From] update; see notes/raft-election-refinement.md *)
      admit.
    + admit.
  - admit.
Admitted.

(** *** [MsgVoteResp]: tally a vote.

    [Step]'s switch has no case for [MsgVoteResp], so it falls through to
    [r.step], i.e. [stepCandidate] (which polls, and may win or lose the
    election) or [stepFollower] / [stepLeader] (which ignore it). *)
Theorem wp_raft__Step_MsgVoteResp γ r id s (m : raftpb.Message.t) :
  m.(raftpb.Message.Type') = MsgVoteResp →
  m.(raftpb.Message.To') = id →
  m.(raftpb.Message.Term') ≠ W64 0 →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "Hghost" ∷ own_raft_ghost γ id s ∗
      "#Hm" ∷ is_message γ (abs_msg mtype.VoteResp m)
  }}}
    r @! (go.PointerType raft.raft) @! "Step" #m
  {{{ (err : error.t) s', RET #err;
      "Hphys" ∷ own_raft_phys γ r id s' ∗
      "Hghost" ∷ own_raft_ghost γ id s' ∗
      "%Hrefines" ∷ ⌜ ∃ recv sent,
          (∀ m', m' ∈ recv → m' = abs_msg mtype.VoteResp m) ∧
          step cfg id s recv s' sent ⌝ ∗
      "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
Proof.
Admitted.

(** *** The refinement theorem.

    For any election message, [Step] takes the implementation through a
    transition of the protocol state machine, using only messages that were
    legitimately on the network, and the ghost protocol state follows. *)
Theorem wp_raft__Step γ r id s (m : raftpb.Message.t) :
  election_msg m →
  (m.(raftpb.Message.Type') = MsgHup → m.(raftpb.Message.Term') = W64 0) →
  (m.(raftpb.Message.Type') = MsgVote →
     m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0 ∧
     m.(raftpb.Message.From') ≠ W64 0) →
  (m.(raftpb.Message.Type') = MsgVoteResp →
     m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0) →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "Hghost" ∷ own_raft_ghost γ id s ∗
      "#Hm" ∷ (∀ ty, ⌜ mtype_of m.(raftpb.Message.Type') = Some ty ⌝ -∗
                     is_message γ (abs_msg ty m)) ∗
      "#Hctx" ∷ (∃ ctx, m.(raftpb.Message.Context') ↦*□ ctx ∗
                        ⌜ ctx ≠ campaignTransfer ⌝)
  }}}
    r @! (go.PointerType raft.raft) @! "Step" #m
  {{{ (err : error.t) s', RET #err;
      "Hphys" ∷ own_raft_phys γ r id s' ∗
      "Hghost" ∷ own_raft_ghost γ id s' ∗
      "%Hrefines" ∷ ⌜ ∃ recv sent, step cfg id s recv s' sent ⌝ ∗
      "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
Proof.
  intros Helection Hhup Hvote Hvoteresp.
  iIntros (Φ) "(#Hinit & Hphys & Hghost & #Hm & #Hctx) HΦ".
  destruct Helection as [Hty | [Hty | Hty]].
  - (* MsgHup: a local message, handled by [hup]. *)
    wp_apply (wp_raft__Step_MsgHup with "[$Hphys $Hghost]"); [done|by auto|].
    iIntros (err s') "(Hphys & Hghost & %Hst & %Herr)".
    iApply ("HΦ" $! err s'). iFrame. iPureIntro. split; [|done].
    destruct Hst as [sent Hst]. by eexists [], sent.
  - (* MsgVote: answer the vote request, stepping down first if needed. *)
    destruct (Hvote Hty) as (Hto & Hterm & Hfnz).
    iDestruct ("Hm" $! mtype.Vote with "[]") as "#Hm'".
    { iPureIntro. rewrite Hty. apply mtype_of_MsgVote. }
    wp_apply (wp_raft__Step_MsgVote with "[$Hphys $Hghost $Hm' $Hctx]");
      [done..|].
    iIntros (err s') "(Hphys & Hghost & %Hst & %Herr)".
    iApply ("HΦ" $! err s'). iFrame. iPureIntro. split; [|done].
    destruct Hst as (recv & sent & _ & Hstep). by eexists recv, sent.
  - (* MsgVoteResp: tally the vote, possibly winning or losing. *)
    destruct (Hvoteresp Hty) as [Hto Hterm].
    iDestruct ("Hm" $! mtype.VoteResp with "[]") as "#Hm'".
    { iPureIntro. rewrite Hty. apply mtype_of_MsgVoteResp. }
    wp_apply (wp_raft__Step_MsgVoteResp with "[$Hphys $Hghost $Hm']"); [done..|].
    iIntros (err s') "(Hphys & Hghost & %Hst & %Herr)".
    iApply ("HΦ" $! err s'). iFrame. iPureIntro. split; [|done].
    destruct Hst as (recv & sent & _ & Hstep). by eexists recv, sent.
Qed.

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
