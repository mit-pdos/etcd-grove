(** * Physical ownership of the raft struct *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raftlog.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_tracker.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_logger.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_misc.

(** Step over one logging call: build the variadic argument slice, then
    apply the logger spec.  Expects [is_Logger] under the name [Hlogger]. *)
Ltac wp_log lok_eq :=
  wp_apply wp_slice_literal;
  [ iSplitR;
    [ done
    | iIntros "% [? _]"; try wp_auto; rewrite lok_eq; try wp_auto;
      wp_apply (wp_Logger__logf with "Hlogger") as "_";
      [ rewrite /log_methods; set_solver | ] ] ].

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** The (fixed) set of voters.  [own_raft_phys] mentions it because
    [own_tracker] does: now that the tracker is a real definition rather than
    an opaque axiom, it pins the progress map's domain and the configuration's
    voter set to [cfg]. *)
Context (cfg : gset w64).

Implicit Type γ : raft_election_names.
Implicit Type s : nstate.t.

(** ** Physical ownership of the raft struct

    [own_raft_phys r id s] is full ownership of the [raft] struct at [r], in a
    state that refines the protocol state [s] — [s.(nstate.outbox)] included.

    Note there is no [γ]: this predicate says nothing about ghost state, and
    in particular does not certify the outgoing queues.  That certification
    now follows from [own_raft_ghost] instead, via [own_raft_ghost_outbox],
    which is what lets every spec below [Step] be ghost-free. *)
(** Which of the three [stepX] functions [r.step] holds, as a function of the
    role.  The [becomeX] functions assign these ([r.step := stepFollower] and
    so on), and [Step] dispatches a message it does not handle inline through
    [r.step(m)] -- so without tying the field to the role, that call cannot be
    stepped at all: [wp_auto] reaches [#rv.(step') #r #m] with nothing to
    apply.

    Until 2026-09-16 a comment here *claimed* [own_raft_phys] recorded this,
    and it did not: [step'] appeared in no conjunct, which is why
    [proof_raft__becomeFollower.v] could re-seal with
    [iExists (rv <| step' := _ |>)]. Discovered while trying to prove
    [Step]'s [MsgVoteResp] branch, which is the first thing that needs it. *)
Definition step_func_of (ro : role.t) : func.t :=
  match ro with
  | role.Follower => functions raft.stepFollower []
  | role.Candidate => functions raft.stepCandidate []
  | role.Leader => functions raft.stepLeader []
  end.

(** Ownership of the struct, with [r.step] pinned to an explicit [f] rather
    than to the role.

    The parameterized form is needed because [becomeFollower] assigns
    [r.step := stepFollower] **before** [r.state := StateFollower], and
    [reset] runs in between -- so at that point the field and the role
    genuinely disagree and [own_raft_phys] below does not hold. [reset]'s
    spec is therefore stated on this variant, carrying [f] through unchanged,
    and the [becomeX] proofs fold back to [own_raft_phys] once the role
    assignment catches up. *)
Definition own_raft_phys_at (r : loc) (id : w64) s (f : func.t) : iProp Σ :=
  ∃ (rv : raft.raft.t) (msgs msgsAA : list raftpb.Message.t)
    (lok : interface.t_ok),
  "Hr" ∷ r ↦ rv ∗

  (** the abstraction relation *)
  "%Hid" ∷ ⌜ rv.(raft.raft.id') = id ⌝ ∗
  "%Hterm" ∷ ⌜ rv.(raft.raft.Term') = s.(nstate.term) ⌝ ∗
  "%Hvote" ∷ ⌜ rv.(raft.raft.Vote') = s.(nstate.vote) ⌝ ∗
  "%Hlead" ∷ ⌜ rv.(raft.raft.lead') = s.(nstate.lead) ⌝ ∗
  "%Hstate" ∷ ⌜ rv.(raft.raft.state') = state_w64 s.(nstate.role) ⌝ ∗
  (** [r.step] is the given function.  See [step_func_of] above. *)
  "%Hstepfn" ∷ ⌜ rv.(raft.raft.step') = f ⌝ ∗

  (** the vote tally, and the rest of the heap the tracker points at.  The
      tracker's own bytes are covered by [Hr] above, since [trk] is embedded
      by value; this is only what hangs off it. *)
  "Htrk" ∷ own_tracker cfg rv.(raft.raft.trk') s.(nstate.votes) ∗

  (** the log, opaque *)
  "Hlog" ∷ own_raftLog rv.(raft.raft.raftLog') ∗

  (** outgoing messages.  [send] routes vote/append *responses* to
      [msgsAfterAppend] and everything else to [msgs]; the model has a single
      outbox, so the abstraction is of the two together.

      Two deliberate choices here.  [omap]: a message type the model does not
      describe (notably the [MsgAppResp] that [appendEntry] queues) simply
      drops out, rather than making the abstract outbox undefined.  [≡ₚ]:
      appending to [msgs] does not append to the concatenation when [msgsAA]
      is non-empty, so equality would not survive a [send]; permutation is
      also all the model needs, since it cares which messages are out and not
      in what order. *)
  "Hmsgs" ∷ rv.(raft.raft.msgs') ↦* msgs ∗
  "Hmsgs_cap" ∷ own_slice_cap raftpb.Message.t rv.(raft.raft.msgs') (DfracOwn 1) ∗
  "HmsgsAA" ∷ rv.(raft.raft.msgsAfterAppend') ↦* msgsAA ∗
  "HmsgsAA_cap" ∷ own_slice_cap raftpb.Message.t
                    rv.(raft.raft.msgsAfterAppend') (DfracOwn 1) ∗
  "%Houtbox" ∷ ⌜ s.(nstate.outbox) ≡ₚ abs_outbox msgs msgsAA ⌝ ∗

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

(** The usual form: [r.step] is whichever [stepX] the role calls for. *)
Definition own_raft_phys (r : loc) (id : w64) s : iProp Σ :=
  own_raft_phys_at r id s (step_func_of s.(nstate.role)).

(** Out of scope: the empty entry a new leader appends.  [appendEntry]
    updates the log and then queues a self-addressed [MsgAppResp]
    ([new/code/go_etcd_io/raft/v3.v], the [send] at the end of
    [raft__appendEntryⁱᵐᵖˡ]).  [mtype_of MsgAppResp = None], so [abs_msg_opt]
    drops it and the abstract state — outbox included — is unchanged.

    This axiom lives here rather than in [inv_misc.v] because it has to
    mention [own_raft_phys].  Its previous form owned only [own_raftLog] while
    the code it describes writes [r.msgsAfterAppend], which made it false; it
    could not be stated honestly before the outbox was abstracted, because
    the old [is_phys_msg] clause was unprovable for a [MsgAppResp]. *)
Axiom wp_raft__appendEmptyEntry : ∀ (r : loc) id s (es : slice.t),
  {{{ is_pkg_init raft ∗ own_raft_phys r id s }}}
    r @! (go.PointerType raft.raft) @! "appendEntry" #es
  {{{ RET #true; own_raft_phys r id s }}}.

(** The broadcast a new leader sends.  [bcastAppend] visits every peer's
    [Progress] and calls [sendAppend], which reaches [maybeSendAppend] -- and
    that sends a [MsgApp] only when the log and the peer's [Progress] permit
    it, otherwise a [MsgSnap] or nothing at all (the peer is paused, or there
    is nothing to send and [sendIfEmpty] is false).

    So this says **not** one [MsgApp] per peer, only that the outbox grew by
    some list of [App]s from [id] at the current term.  That is exactly what
    the weakened [step_win] asks for, and all the election model ever uses: a
    receiver reads an [App] through [step_higher_term], which cares about its
    term and that a leader sent it.  An earlier version of the model demanded
    one per peer, which would have made this claim false -- the same trap
    [wp_raft__appendEmptyEntry] fell into before 2026-09-15. *)
Lemma wp_raft__bcastAppend (r : loc) id s :
  {{{ is_pkg_init raft ∗ own_raft_phys r id s }}}
    r @! (go.PointerType raft.raft) @! "bcastAppend" #()
  {{{ (ms : list msg.t), RET #();
      own_raft_phys r id (send_msgs s ms) ∗
      ⌜ app_sends id s.(nstate.term) ms ⌝ }}}.
Proof. Admitted.

End proof.
