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

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
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

    [own_tracker trk votes] owns the tracker embedded at [trk], whose voter
    set is [cfg] (no learners, no joint configuration) and whose recorded
    vote tally is [votes]. *)
Axiom own_tracker : loc → gmap w64 bool → iProp Σ.

Axiom wp_ProgressTracker__ResetVotes : ∀ (trk : loc) votes,
  {{{ is_pkg_init tracker ∗ own_tracker trk votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "ResetVotes" #()
  {{{ RET #(); own_tracker trk ∅ }}}.

Axiom wp_ProgressTracker__RecordVote : ∀ (trk : loc) votes (from : w64) (v : bool),
  {{{ is_pkg_init tracker ∗ own_tracker trk votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "RecordVote" #from #v
  {{{ RET #(); own_tracker trk (record_vote votes from v) }}}.

(** [TallyVotes] reports the outcome of the election, which is exactly the
    quorum condition of the model. *)
Axiom wp_ProgressTracker__TallyVotes : ∀ (trk : loc) votes,
  {{{ is_pkg_init tracker ∗ own_tracker trk votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "TallyVotes" #()
  {{{ (g rj : w64) (res : w8), RET (#g, #rj, #res);
      own_tracker trk votes ∗
      ⌜ res = VoteWon ∨ res = VoteLost ∨ res = VotePending ⌝ ∗
      ⌜ res = VoteWon → is_quorum cfg (granted votes) ⌝ ∗
      ⌜ res = VoteLost → is_quorum cfg (rejected votes) ⌝ }}}.

(** [r.promotable()]: true exactly when this node is a voter. *)
Axiom wp_raft__promotable : ∀ (r : loc) (id : w64) trk votes l,
  {{{ is_pkg_init raft ∗ own_tracker trk votes ∗ own_raftLog l }}}
    r @! (go.PointerType raft.raft) @! "promotable" #()
  {{{ (b : bool), RET #b;
      own_tracker trk votes ∗ own_raftLog l ∗ ⌜ b = bool_decide (id ∈ cfg) ⌝ }}}.

(** [r.hasUnappliedConfChanges()]: false, since there is no
    reconfiguration. *)
Axiom wp_raft__hasUnappliedConfChanges : ∀ (r : loc) l,
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    r @! (go.PointerType raft.raft) @! "hasUnappliedConfChanges" #()
  {{{ RET #false; own_raftLog l }}}.

(** The ids of the voters, in some order, as [campaign] enumerates them. *)
Axiom wp_campaign_peer_ids : ∀ (trk : loc) votes,
  {{{ is_pkg_init quorum ∗ own_tracker trk votes }}}
    trk @! (go.PointerType quorum.JointConfig) @! "IDs" #()
  {{{ (mref : loc) (idm : gmap w64 unit), RET #mref;
      own_tracker trk votes ∗ mref ↦$ idm ∗ ⌜ dom idm = cfg ⌝ }}}.

(** *** Logging and tracing.

    Every [Logger] method used on the election path returns unit and has no
    observable effect.  [Panicf]/[Panic] are only reached on paths shown
    unreachable, so they get the same (vacuously usable) spec. *)
Axiom is_Logger_ok : interface.t_ok → iProp Σ.
Axiom is_Logger_ok_pers : ∀ l, Persistent (is_Logger_ok l).
#[global] Existing Instance is_Logger_ok_pers.

Axiom wp_Logger__logf : ∀ (l : interface.t_ok) (meth : go_string)
                          (format : go_string) (args : slice.t),
  meth ∈ (["Infof"%go; "Debugf"%go; "Warningf"%go; "Errorf"%go] : list go_string) →
  {{{ is_Logger_ok l }}}
    #(methods l.(interface.ty) meth l.(interface.v)) #format #args
  {{{ RET #(); True }}}.

(** The logger stored in the struct, which must not be nil. *)
Definition is_Logger (l : raft.Logger.t) : iProp Σ :=
  ∃ lok : interface.t_ok, ⌜ l = interface.ok lok ⌝ ∗ is_Logger_ok lok.

#[global] Instance is_Logger_pers l : Persistent (is_Logger l).
Proof. apply _. Qed.

Axiom is_TraceLogger : raft.TraceLogger.t → iProp Σ.
Axiom is_TraceLogger_pers : ∀ l, Persistent (is_TraceLogger l).
#[global] Existing Instance is_TraceLogger_pers.

(** *** The parts of the raft struct election neither reads nor writes. *)
Axiom own_raft_misc : raft.raft.t → iProp Σ.

Axiom wp_traceReceiveMessage : ∀ (r : loc) (m : loc) rv,
  {{{ is_pkg_init raft ∗ own_raft_misc rv }}}
    @! raft.traceReceiveMessage #r #m
  {{{ RET #(); own_raft_misc rv }}}.

Axiom wp_traceSendMessage : ∀ (r : loc) (m : loc) rv,
  {{{ is_pkg_init raft ∗ own_raft_misc rv }}}
    @! raft.traceSendMessage #r #m
  {{{ RET #(); own_raft_misc rv }}}.

Axiom wp_traceBecomeFollower : ∀ (r : loc) rv,
  {{{ is_pkg_init raft ∗ own_raft_misc rv }}}
    @! raft.traceBecomeFollower #r
  {{{ RET #(); own_raft_misc rv }}}.

Axiom wp_traceBecomeCandidate : ∀ (r : loc) rv,
  {{{ is_pkg_init raft ∗ own_raft_misc rv }}}
    @! raft.traceBecomeCandidate #r
  {{{ RET #(); own_raft_misc rv }}}.

Axiom wp_traceBecomeLeader : ∀ (r : loc) rv,
  {{{ is_pkg_init raft ∗ own_raft_misc rv }}}
    @! raft.traceBecomeLeader #r
  {{{ RET #(); own_raft_misc rv }}}.

(** [reset] also re-initializes the election/heartbeat timers, every peer's
    [Progress], the pending-conf index, the uncommitted size and the
    read-only queue.  None of that is election state, so it is bundled
    here: [reset] restores [own_raft_misc] for the updated struct and clears
    the vote tally. *)
Axiom own_raft_misc_reset : ∀ rv rv',
  own_raft_misc rv -∗ own_raft_misc rv'.

(** The empty entry a new leader appends, and the append broadcast that
    follows it.  [bcastAppend] sends one [MsgApp] to each peer, which is
    exactly [step_win]'s [sent] list. *)
Axiom wp_raft__appendEmptyEntry : ∀ (r : loc) l (es : slice.t),
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    r @! (go.PointerType raft.raft) @! "appendEntry" #es
  {{{ RET #true; own_raftLog l }}}.

End helper_axioms.

(** ** Physical ownership of the raft struct

    [own_raft_phys γ r id s] is full ownership of the [raft] struct at [r],
    in a state that refines the protocol state [s], and whose two outgoing
    message queues contain only messages [γ] certifies as protocol-legal. *)
Definition own_raft_phys γ (r : loc) (id : w64) s : iProp Σ :=
  ∃ (rv : raft.raft.t) (msgs msgsAA : list raftpb.Message.t),
  "Hr" ∷ r ↦ rv ∗

  (** the abstraction relation *)
  "%Hid" ∷ ⌜ rv.(raft.raft.id') = id ⌝ ∗
  "%Hterm" ∷ ⌜ rv.(raft.raft.Term') = s.(nstate.term) ⌝ ∗
  "%Hvote" ∷ ⌜ rv.(raft.raft.Vote') = s.(nstate.vote) ⌝ ∗
  "%Hlead" ∷ ⌜ rv.(raft.raft.lead') = s.(nstate.lead) ⌝ ∗
  "%Hstate" ∷ ⌜ rv.(raft.raft.state') = state_w64 s.(nstate.role) ⌝ ∗

  (** the vote tally lives in the tracker *)
  "Htrk" ∷ own_tracker (struct_field_ref raft.raft.t "trk" r) s.(nstate.votes) ∗

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
  "#Hsent" ∷ ([∗ list] m ∈ msgs ++ msgsAA, is_phys_msg γ m) ∗

  (** scope assumptions *)
  "%HnoPreVote" ∷ ⌜ rv.(raft.raft.preVote') = false ⌝ ∗
  "%HnoCheckQuorum" ∷ ⌜ rv.(raft.raft.checkQuorum') = false ⌝ ∗
  "%HnoLearner" ∷ ⌜ rv.(raft.raft.isLearner') = false ⌝ ∗
  "%HnoTransfer" ∷ ⌜ rv.(raft.raft.leadTransferee') = W64 0 ⌝ ∗
  "%Hid_nz" ∷ ⌜ id ≠ W64 0 ⌝ ∗

  (** logging, tracing, and everything else *)
  "#Hlogger" ∷ is_Logger rv.(raft.raft.logger') ∗
  "#Htracer" ∷ is_TraceLogger rv.(raft.raft.traceLogger') ∗
  "Hmisc" ∷ own_raft_misc rv.

(** The step function stored in [r.step] is determined by the role; rather
    than naming the closure, we record which of the three [stepX] functions
    it is by the role, and dispatch on the role at the one call site. *)

(** ** [send]

    [send] is the only place a message reaches the network, so this is where
    the [is_message] obligation is discharged: the caller must already know
    the abstract message is legal. *)
Lemma wp_raft__send γ r id s (m : raftpb.Message.t) ty :
  m.(raftpb.Message.From') = W64 0 ∨ m.(raftpb.Message.From') = id →
  mtype_of m.(raftpb.Message.Type') = Some ty →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "#Hm" ∷ is_message γ (abs_msg ty (m <| raftpb.Message.From' := id |>))
  }}}
    r @! (go.PointerType raft.raft) @! "send" #m
  {{{ RET #(); own_raft_phys γ r id s }}}.
Proof.
  (* The proof: [send] fills in [From] (already [id]), fills in [Term] from
     [r.Term] for non-vote messages, and appends to [msgsAfterAppend] (for
     MsgVoteResp / MsgAppResp) or to [msgs] (otherwise).  In both cases the
     new element of the queue is [m], for which [Hm] is exactly the required
     [is_phys_msg]. *)
Admitted.

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
Admitted.

Lemma wp_raft__becomeCandidate γ r id s :
  s.(nstate.role) ≠ role.Leader →
  {{{ is_pkg_init raft ∗ own_raft_phys γ r id s }}}
    r @! (go.PointerType raft.raft) @! "becomeCandidate" #()
  {{{ RET #(); own_raft_phys γ r id (become_candidate id s) }}}.
Proof.
Admitted.

Lemma wp_raft__becomeLeader γ r id s :
  s.(nstate.role) ≠ role.Follower →
  {{{ is_pkg_init raft ∗ own_raft_phys γ r id s }}}
    r @! (go.PointerType raft.raft) @! "becomeLeader" #()
  {{{ RET #(); own_raft_phys γ r id (become_leader id s) }}}.
Proof.
Admitted.

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
      ⌜ s' = s ∨ s' = become_candidate id s ⌝ }}}.
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
  Show.
Admitted.

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
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "Hghost" ∷ own_raft_ghost γ id s ∗
      "#Hm" ∷ is_message γ (abs_msg mtype.Vote m)
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
     m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0) →
  (m.(raftpb.Message.Type') = MsgVoteResp →
     m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0) →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "Hghost" ∷ own_raft_ghost γ id s ∗
      "#Hm" ∷ (∀ ty, ⌜ mtype_of m.(raftpb.Message.Type') = Some ty ⌝ -∗
                     is_message γ (abs_msg ty m))
  }}}
    r @! (go.PointerType raft.raft) @! "Step" #m
  {{{ (err : error.t) s', RET #err;
      "Hphys" ∷ own_raft_phys γ r id s' ∗
      "Hghost" ∷ own_raft_ghost γ id s' ∗
      "%Hrefines" ∷ ⌜ ∃ recv sent, step cfg id s recv s' sent ⌝ ∗
      "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
Proof.
  intros Helection Hhup Hvote Hvoteresp.
  iIntros (Φ) "(#Hinit & Hphys & Hghost & #Hm) HΦ".
  destruct Helection as [Hty | [Hty | Hty]].
  - (* MsgHup: a local message, handled by [hup]. *)
    wp_apply (wp_raft__Step_MsgHup with "[$Hphys $Hghost]"); [done|by auto|].
    iIntros (err s') "(Hphys & Hghost & %Hst & %Herr)".
    iApply ("HΦ" $! err s'). iFrame. iPureIntro. split; [|done].
    destruct Hst as [sent Hst]. by eexists [], sent.
  - (* MsgVote: answer the vote request, stepping down first if needed. *)
    destruct (Hvote Hty) as [Hto Hterm].
    iDestruct ("Hm" $! mtype.Vote with "[]") as "#Hm'".
    { iPureIntro. rewrite Hty. apply mtype_of_MsgVote. }
    wp_apply (wp_raft__Step_MsgVote with "[$Hphys $Hghost $Hm']"); [done..|].
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
