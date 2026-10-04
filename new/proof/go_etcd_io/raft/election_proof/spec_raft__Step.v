Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
(* [snap_scope], for [MsgSnap]; before [step_lemmas], whose [step] must win *)
Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__restore.
Require Export New.proof.go_etcd_io.raft.election_proof.step_lemmas.
(* [MsgBeat] *)
Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__handleHeartbeat.
(* [wp_Equal], for the MsgVote branch's Context comparison. *)
Require Export New.proof.bytes.

(** The top-level dispatch, and **one spec like every other function**.  The
    per-message-type branches are proof structure, not specification: since
    2026-09-17 they live in [proof_raft__Step_MsgHup.v], [_MsgVote.v],
    [_MsgVoteResp.v] and (2026-10-02) [_MsgProp.v] (and below those,
    [_MsgVote_gt.v], [_MsgVote_le.v], [_MsgVote_lt.v],
    [_MsgVote_eq_novote.v], [_MsgVote_eq_voted.v]), each a
    functor over [STEP_POSTULATES] with no [Module Type] and no [Parameter],
    so that [make -j] checks them in parallel.  Only [proof_raft__Step.v] and
    the combining files may [Require] one.  (An earlier version of this note
    said [Step] "is the one function with more than one spec"; that was
    written before the first cut's three per-message-type [Module Type]s were
    removed on 2026-09-14, and it is no longer true of anything here.)

    This is **the only spec in this development that mentions ghost state**.
    Every function below it is specified against [own_raft_phys] alone, saying
    which state the struct ends up refining and how the outbox grew; [Step]
    assembles those pure facts into one [step] witness and takes one
    [own_raft_ghost_step].  A caller that needs to know a pending outgoing
    message is protocol-legal gets that from [own_raft_ghost_outbox], not from
    [own_raft_phys]. *)
(** The message types [Step] is specified for: every type its branches
    cover (2026-10-02; until then only [MsgHup]/[MsgVote]/[MsgVoteResp],
    [election_msg]; [MsgPreVote]/[MsgPreVoteResp] since 2026-10-04). *)
Definition step_msg_types : list w32 :=
  [MsgHup; MsgVote; MsgVoteResp; MsgApp; MsgAppResp; MsgHeartbeat;
   MsgHeartbeatResp; MsgBeat; MsgProp; MsgSnap; MsgPreVote; MsgPreVoteResp].

Definition step_msg (m : raftpb.Message.t) : Prop :=
  m.(raftpb.Message.Type') ∈ step_msg_types.

Definition wp_raft__Step_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (γ : raft_election_names) (r : loc) (id : w64) (s : nstate.t) (ps : pstate.t)
    (m : raftpb.Message.t),
  (* The ghost state is about one configuration, and it is this one.  Without
     this the caller could hand [own_raft_ghost_step] a [cfg] of its own
     choosing -- a singleton one, say, in which the node is its own quorum --
     and election safety would not hold.  See [raft_election_names]. *)
  γ.(re_cfg) = cfg →
  step_msg m →
  (* The node is a voter.  [stepCandidate] needs this outright (its [poll]
     and [becomeLeader] both do) and [spec_stepCandidate_MsgVoteResp.v] says
     to thread it in "from the caller" -- but [Step] *is* the outermost
     caller, so it has to enter the development here.  Under the no-learner,
     no-reconfiguration scope this is a property of the node, not of a
     particular call.  Added 2026-09-16 for the [MsgVoteResp] branch. *)
  id ∈ cfg →
  (* A [MsgHup] is local ([Term = 0]) and may start an election, which
     increments the term; [send] panics if that wraps to zero. *)
  (m.(raftpb.Message.Type') = MsgHup →
     m.(raftpb.Message.Term') = W64 0 ∧
     uint.Z s.(nstate.term) + 1 < 2 ^ 64) →
  (m.(raftpb.Message.Type') = MsgVote →
     m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0 ∧
     m.(raftpb.Message.From') ≠ W64 0) →
  (m.(raftpb.Message.Type') = MsgVoteResp →
     m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0) →
  (* Pre-vote (2026-10-04), by what the transport and the peers guarantee,
     like [MsgVote]; [Go] checks none of it.  Two more:
     - a [MsgPreVote] of a higher term is answered at the node's own term
       when the candidate's log is behind ([Term: r.Term, Reject: true];
       the term is not raised for a pre-vote), and [send] panics on a vote
       message with [Term = 0].  So a node at term [0] must find every
       pre-vote candidate up to date -- true of a node whose log holds
       nothing past term [0], i.e. of every node etcd builds (a fresh node
       has an empty log; [Bootstrap] and [RestartNode] start at a term of
       at least the log's), but not implied by [own_raft_phys], which
       admits a persisted log ahead of the persisted term;
     - a [MsgPreVoteResp] at a pre-candidate may win, which runs the real
       [campaign] and increments the term: it must not wrap (as for
       [MsgHup]). *)
  (m.(raftpb.Message.Type') = MsgPreVote →
     m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0 ∧
     m.(raftpb.Message.From') ≠ W64 0 ∧ m.(raftpb.Message.From') ≠ id ∧
     (s.(nstate.term) = W64 0 →
      plog_up_to_date s.(nstate.logst).(logstate.prev)
        (s.(nstate.logst).(logstate.sents) ++ s.(nstate.logst).(logstate.uents))
        (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) = true)) →
  (m.(raftpb.Message.Type') = MsgPreVoteResp →
     m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0 ∧
     m.(raftpb.Message.From') ≠ W64 0 ∧
     uint.Z s.(nstate.term) + 1 < 2 ^ 64) →
  (* The replication types, by what the transport and the peers guarantee
     (Go checks none of it).  A leader's [MsgApp]/[MsgHeartbeat], and a
     [MsgHeartbeatResp], come from another node: [send] never queues them
     to oneself.  An accepting [MsgAppResp] may be the node's own
     ([appendEntry]'s self-acknowledgement); a rejecting one is not. *)
  (m.(raftpb.Message.Type') = MsgApp →
     m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0 ∧
     m.(raftpb.Message.From') ≠ W64 0 ∧ m.(raftpb.Message.From') ≠ id) →
  (m.(raftpb.Message.Type') = MsgHeartbeat →
     m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0 ∧
     m.(raftpb.Message.From') ≠ W64 0 ∧ m.(raftpb.Message.From') ≠ id) →
  (m.(raftpb.Message.Type') = MsgAppResp →
     m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0 ∧
     m.(raftpb.Message.From') ≠ W64 0 ∧
     (m.(raftpb.Message.Reject') = true → m.(raftpb.Message.From') ≠ id)) →
  (m.(raftpb.Message.Type') = MsgHeartbeatResp →
     m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0 ∧
     m.(raftpb.Message.From') ≠ W64 0 ∧ m.(raftpb.Message.From') ≠ id) →
  (* A leader's [MsgSnap], likewise (2026-10-02). *)
  (m.(raftpb.Message.Type') = MsgSnap →
     m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0 ∧
     m.(raftpb.Message.From') ≠ W64 0 ∧ m.(raftpb.Message.From') ≠ id) →
  (* [MsgBeat] and [MsgProp] are local ([Term = 0]); a proposal is not yet
     stamped with a sender ([From = 0]).  The proposal's batch is
     constrained in [Hm] below, where its list is named. *)
  (m.(raftpb.Message.Type') = MsgBeat → m.(raftpb.Message.Term') = W64 0) →
  (m.(raftpb.Message.Type') = MsgProp →
     m.(raftpb.Message.Term') = W64 0 ∧ m.(raftpb.Message.From') = W64 0) →
  (* The one place the two layers meet.  [s] is the physical abstract state
     [own_raft_phys] is indexed by, [ps] the protocol state the ghost state
     is about, and [nstate_rel] ([defs.v]) connects them: [ps] is [s]'s
     protocol fields, [r.step] agrees with the role, nothing is on loan. *)
  nstate_rel s ps →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys cfg r id s ∗
      "Hghost" ∷ own_raft_ghost γ id ps ∗
      (* The message's [Entries] slice, holding [ents] ([[]] for a message
         without entries, [Entries = nil]):
         - a proposal is a local message whose batch the caller owns
           outright -- [appendEntry] writes [Term]/[Index] into the
           entries -- while every network message's entries are read-only;
         - the slice's capacity, owned: [raftLog.maybeAppend] can adopt
           the caller's slice ([unstable.truncateAndAppend]'s replace arm,
           v3.v:1650), so a received [MsgApp] needs it;
         - a proposal's batch is non-empty ([stepLeader]'s [Panicf]),
           [EntryNormal] only (no conf change in scope) and short enough
           for [appendEntry]'s indices not to wrap;
         - what the message carries as a protocol message: its abstraction
           ([abs_msg], which needs the entries) was legitimately sent --
           for every type but [MsgSnap], whose abstraction is [abs_snap]
           (["Hsnap"] below). *)
      "Hm" ∷ (∃ ents,
         "Hents" ∷ (if decide (m.(raftpb.Message.Type') = MsgProp)
                    then m.(raftpb.Message.Entries') ↦* ents
                    else m.(raftpb.Message.Entries') ↦*□ ents) ∗
         "Hents_cap" ∷ own_slice_cap raftpb.Entry.t m.(raftpb.Message.Entries') (DfracOwn 1) ∗
         "%Hprop" ∷ ⌜ m.(raftpb.Message.Type') = MsgProp →
                      ents ≠ [] ∧
                      Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents ∧
                      (Z.of_nat (length ents) < 2^61)%Z ⌝ ∗
         "#Hmsg" ∷ □ (∀ ty, ⌜ mtype_of m.(raftpb.Message.Type') = Some ty ⌝ -∗
                            ⌜ ty ≠ mtype.Snap ⌝ -∗
                            is_message γ (abs_msg ty m ents))) ∗
      (* the [Context]: not the leader-transfer marker (out of scope), and
         empty on a heartbeat response (no read-index requests in scope:
         [bcastHeartbeat] sends [nil] and [handleHeartbeat] echoes it) *)
      "#Hctx" ∷ (∃ ctx, m.(raftpb.Message.Context') ↦*□ ctx ∗
                        ⌜ ctx ≠ campaignTransfer ⌝ ∗
                        ⌜ m.(raftpb.Message.Type') = MsgHeartbeatResp → ctx = [] ⌝) ∗
      (* A [MsgSnap]'s snapshot (2026-10-02): what [m.Snapshot] points to,
         read-only, and the list behind its [ConfState.Voters]; under the
         fixed-voter-set scope [snap_scope] ([spec_raft__restore.v]): the
         voters are [cfg]'s, [cfg] is zero-free, the other three sets are
         empty and [AutoLeave] is off (what [confchange.Restore]'s and
         [assertConfStatesEquivalent]'s specs cover), and the index is
         below [2^61] (a pending snapshot becomes the [Storage]'s boundary,
         which [is_Storage]'s [Hbounded] bounds the same way).  And the
         abstraction [abs_snap] ([defs.v]) -- the snapshot's metadata, not
         [m]'s own [Index]/[LogTerm] -- was legitimately sent.  The two
         added on 2026-10-02 with the branch ([W64 0 ∉ cfg], [AutoLeave],
         the index bound) are transport/client assumptions like the
         rest. *)
      "#Hsnap" ∷ □ (⌜ m.(raftpb.Message.Type') = MsgSnap ⌝ -∗
         ∃ (sv : raftpb.Snapshot.t) (voters : list w64),
           m.(raftpb.Message.Snapshot') ↦□ sv ∗
           sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
             .(raftpb.ConfState.Voters') ↦*□ voters ∗
           ⌜ snap_scope cfg sv voters ⌝ ∗
           is_message γ (abs_snap m sv voters))
  }}}
    r @! (go.PointerType raft.raft) @! "Step" #m
  {{{ (err : error.t) s' ps', RET #err;
      "Hphys" ∷ own_raft_phys cfg r id s' ∗
      "Hghost" ∷ own_raft_ghost γ id ps' ∗
      "%Hrel" ∷ ⌜ nstate_rel s' ps' ⌝ ∗
      "%Hrefines" ∷ ⌜ ∃ recv, step cfg id ps recv ps' ⌝ ∗
      (* only a proposal can be dropped, with [ErrProposalDropped] *)
      "Herr" ∷ (⌜ err = interface.nil ⌝ ∨
                (⌜ m.(raftpb.Message.Type') = MsgProp ⌝ ∗
                 (global_addr raft.ErrProposalDropped) ↦□ err)) }}}.

Module Type STEP.
  Parameter wp_raft__Step : wp_raft__Step_body.
  Arguments wp_raft__Step {_ _ _ _ _ _ _ _}.
End STEP.
