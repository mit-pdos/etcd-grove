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
  (** [Config.validate] requires [ElectionTick > HeartbeatTick > 0] and
      [newRaft] copies it, so this is an invariant of every struct raft
      builds.  It is needed because [resetRandomizedElectionTimeout] passes
      the field to [crypto/rand.Int], which panics on a non-positive bound
      -- see [spec_raft__resetRandomizedElectionTimeout.v].  Never written
      on the election path.  Added 2026-09-20. *)
  "%HelectionTimeout" ∷ ⌜ 0 < sint.Z rv.(raft.raft.electionTimeout') ⌝ ∗

  (** logging, tracing, and everything else *)
  "%Hlok" ∷ ⌜ rv.(raft.raft.logger') = interface.ok lok ⌝ ∗
  "#Hlogger" ∷ is_Logger lok ∗
  "Hmisc" ∷ own_raft_misc rv.(raft.raft.readStates') rv.(raft.raft.readOnly')
             rv.(raft.raft.pendingReadIndexMessages').

(** The usual form: [r.step] is whichever [stepX] the role calls for. *)
Definition own_raft_phys (r : loc) (id : w64) s : iProp Σ :=
  own_raft_phys_at r id s (step_func_of s.(nstate.role)).

(** Re-sealing [own_raft_phys] after a proof has taken it apart.

    [iFrame "∗#%"] against the unfolded predicate costs ~17s per use (2026-09-17
    measurement): [iFrame "%"] alone tries every pure fact in the Coq context
    against every one of the 25 conjuncts. These lemmas make a re-seal a
    single [iApply] with named hypotheses and pure side goals:

      iApply (own_raft_phys_intro with
        "Hlogger Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done.

    The pure premises are in the order the conjuncts appear in the predicate.
    [is_Logger] comes first among the spatial arguments because it is the one
    persistent one. *)
Lemma own_raft_phys_at_intro r id s f (rv : raft.raft.t)
    (msgs msgsAA : list raftpb.Message.t) (lok : interface.t_ok) :
  rv.(raft.raft.id') = id →
  rv.(raft.raft.Term') = s.(nstate.term) →
  rv.(raft.raft.Vote') = s.(nstate.vote) →
  rv.(raft.raft.lead') = s.(nstate.lead) →
  rv.(raft.raft.state') = state_w64 s.(nstate.role) →
  rv.(raft.raft.step') = f →
  s.(nstate.outbox) ≡ₚ abs_outbox msgs msgsAA →
  rv.(raft.raft.preVote') = false →
  rv.(raft.raft.checkQuorum') = false →
  rv.(raft.raft.isLearner') = false →
  rv.(raft.raft.leadTransferee') = W64 0 →
  id ≠ W64 0 →
  0 < sint.Z rv.(raft.raft.electionTimeout') →
  rv.(raft.raft.logger') = interface.ok lok →
  is_Logger lok -∗
  r ↦ rv -∗
  own_tracker cfg rv.(raft.raft.trk') s.(nstate.votes) -∗
  own_raftLog rv.(raft.raft.raftLog') -∗
  rv.(raft.raft.msgs') ↦* msgs -∗
  own_slice_cap raftpb.Message.t rv.(raft.raft.msgs') (DfracOwn 1) -∗
  rv.(raft.raft.msgsAfterAppend') ↦* msgsAA -∗
  own_slice_cap raftpb.Message.t rv.(raft.raft.msgsAfterAppend') (DfracOwn 1) -∗
  own_raft_misc rv.(raft.raft.readStates') rv.(raft.raft.readOnly')
    rv.(raft.raft.pendingReadIndexMessages') -∗
  own_raft_phys_at r id s f.
Proof.
  intros Hid Hterm Hvote Hlead Hstate Hstepfn Houtbox HnoPreVote HnoCheckQuorum
    HnoLearner HnoTransfer Hid_nz HelectionTimeout Hlok.
  iIntros "#Hlogger Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc".
  rewrite /own_raft_phys_at. iExists rv, msgs, msgsAA, lok. iFrame "∗#%".
Qed.

Lemma own_raft_phys_intro r id s (rv : raft.raft.t)
    (msgs msgsAA : list raftpb.Message.t) (lok : interface.t_ok) :
  rv.(raft.raft.id') = id →
  rv.(raft.raft.Term') = s.(nstate.term) →
  rv.(raft.raft.Vote') = s.(nstate.vote) →
  rv.(raft.raft.lead') = s.(nstate.lead) →
  rv.(raft.raft.state') = state_w64 s.(nstate.role) →
  rv.(raft.raft.step') = step_func_of s.(nstate.role) →
  s.(nstate.outbox) ≡ₚ abs_outbox msgs msgsAA →
  rv.(raft.raft.preVote') = false →
  rv.(raft.raft.checkQuorum') = false →
  rv.(raft.raft.isLearner') = false →
  rv.(raft.raft.leadTransferee') = W64 0 →
  id ≠ W64 0 →
  0 < sint.Z rv.(raft.raft.electionTimeout') →
  rv.(raft.raft.logger') = interface.ok lok →
  is_Logger lok -∗
  r ↦ rv -∗
  own_tracker cfg rv.(raft.raft.trk') s.(nstate.votes) -∗
  own_raftLog rv.(raft.raft.raftLog') -∗
  rv.(raft.raft.msgs') ↦* msgs -∗
  own_slice_cap raftpb.Message.t rv.(raft.raft.msgs') (DfracOwn 1) -∗
  rv.(raft.raft.msgsAfterAppend') ↦* msgsAA -∗
  own_slice_cap raftpb.Message.t rv.(raft.raft.msgsAfterAppend') (DfracOwn 1) -∗
  own_raft_misc rv.(raft.raft.readStates') rv.(raft.raft.readOnly')
    rv.(raft.raft.pendingReadIndexMessages') -∗
  own_raft_phys r id s.
Proof. apply own_raft_phys_at_intro. Qed.

(** ** The struct with its two lent-out heaps removed

    [own_raft_phys_at] hides the struct value under [∃ rv], which is the
    right thing for a caller that only wants "the struct is well-formed",
    and the wrong thing for a caller that read a pointer *out* of the
    struct before a call and must come back to it afterwards.  Two of
    [own_raft_phys_at]'s conjuncts describe heap that hangs off a field
    rather than the struct's own bytes:

      [Htrk] ∷ own_tracker cfg rv.(trk') s.(votes)
      [Hlog] ∷ own_raftLog rv.(raftLog')

    and both get *lent out* on the append path: [maybeSendAppend] borrows
    one voter's [Progress] out of the tracker and one page of entries out
    of the log, and holds both across [r.send(...)].  With the struct
    sealed, [send]'s postcondition re-existentialises [rv], so nothing
    relates the rebuilt [rv'.(trk')] to the tracker the [Progress] came
    from -- and the page cannot be held at all, because [own_raft_phys]
    demands the whole log back before the call.  (See
    [proof_raft__maybeSendAppend.v]'s header and notes/false-statements.md,
    2026-09-21.)

    [own_raft_bare r id s f tv lg] is [own_raft_phys_at r id s f] with
    those two conjuncts deleted and the two field values they were indexed
    by promoted to *parameters*: [⌜ rv.(trk') = tv ⌝] and
    [⌜ rv.(raftLog') = lg ⌝].  A triple stated on it therefore says, as
    part of its postcondition, "the tracker field and the log field still
    point where they did" -- which is what [send] and [maybeSendSnapshot]
    (through [send]) do in fact guarantee: neither touches either field.

    The conjuncts are spelled out again rather than factored out of
    [own_raft_phys_at], deliberately.  Twenty-odd other specs are stated on
    [own_raft_phys]/[own_raft_phys_at] and open them with [iNamed]; defining
    [own_raft_phys_at] as [∃ tv lg, own_raft_bare … ∗ …] would put two extra
    existentials in front of every one of those [iNamed]s.  **Keep the two
    lists in step**: a conjunct added to [own_raft_phys_at] belongs here too,
    or [own_raft_phys_at_split] below stops compiling -- which is the point
    of stating that lemma as an [⊣⊢]. *)
Definition own_raft_bare (r : loc) (id : w64) s (f : func.t)
    (tv : tracker.ProgressTracker.t) (lg : loc) : iProp Σ :=
  ∃ (rv : raft.raft.t) (msgs msgsAA : list raftpb.Message.t)
    (lok : interface.t_ok),
  "Hr" ∷ r ↦ rv ∗

  "%Hid" ∷ ⌜ rv.(raft.raft.id') = id ⌝ ∗
  "%Hterm" ∷ ⌜ rv.(raft.raft.Term') = s.(nstate.term) ⌝ ∗
  "%Hvote" ∷ ⌜ rv.(raft.raft.Vote') = s.(nstate.vote) ⌝ ∗
  "%Hlead" ∷ ⌜ rv.(raft.raft.lead') = s.(nstate.lead) ⌝ ∗
  "%Hstate" ∷ ⌜ rv.(raft.raft.state') = state_w64 s.(nstate.role) ⌝ ∗
  "%Hstepfn" ∷ ⌜ rv.(raft.raft.step') = f ⌝ ∗

  (** the two lent-out heaps, replaced by the field values they hang off *)
  "%Htv" ∷ ⌜ rv.(raft.raft.trk') = tv ⌝ ∗
  "%Hlg" ∷ ⌜ rv.(raft.raft.raftLog') = lg ⌝ ∗

  "Hmsgs" ∷ rv.(raft.raft.msgs') ↦* msgs ∗
  "Hmsgs_cap" ∷ own_slice_cap raftpb.Message.t rv.(raft.raft.msgs') (DfracOwn 1) ∗
  "HmsgsAA" ∷ rv.(raft.raft.msgsAfterAppend') ↦* msgsAA ∗
  "HmsgsAA_cap" ∷ own_slice_cap raftpb.Message.t
                    rv.(raft.raft.msgsAfterAppend') (DfracOwn 1) ∗
  "%Houtbox" ∷ ⌜ s.(nstate.outbox) ≡ₚ abs_outbox msgs msgsAA ⌝ ∗

  "%HnoPreVote" ∷ ⌜ rv.(raft.raft.preVote') = false ⌝ ∗
  "%HnoCheckQuorum" ∷ ⌜ rv.(raft.raft.checkQuorum') = false ⌝ ∗
  "%HnoLearner" ∷ ⌜ rv.(raft.raft.isLearner') = false ⌝ ∗
  "%HnoTransfer" ∷ ⌜ rv.(raft.raft.leadTransferee') = W64 0 ⌝ ∗
  "%Hid_nz" ∷ ⌜ id ≠ W64 0 ⌝ ∗
  "%HelectionTimeout" ∷ ⌜ 0 < sint.Z rv.(raft.raft.electionTimeout') ⌝ ∗

  "%Hlok" ∷ ⌜ rv.(raft.raft.logger') = interface.ok lok ⌝ ∗
  "#Hlogger" ∷ is_Logger lok ∗
  "Hmisc" ∷ own_raft_misc rv.(raft.raft.readStates') rv.(raft.raft.readOnly')
             rv.(raft.raft.pendingReadIndexMessages').

(** The tracker alone, for a caller that keeps the log: this is the
    predicate STATUS item 18 asks for, and [maybeSendSnapshot] is stated on
    it (it calls [raftLog.snapshot] and [raftLog.firstIndex], so it needs
    the log; it borrows no [Progress], so it must not be given the
    tracker). *)
Definition own_raft_notrk (r : loc) (id : w64) s (f : func.t)
    (tv : tracker.ProgressTracker.t) : iProp Σ :=
  ∃ (lg : loc), own_raft_bare r id s f tv lg ∗ own_raftLog lg.

Lemma own_raft_bare_split r id s f :
  own_raft_phys_at r id s f -∗
  ∃ tv lg, own_raft_bare r id s f tv lg ∗
           own_tracker cfg tv s.(nstate.votes) ∗ own_raftLog lg.
Proof.
  iIntros "H". iNamed "H".
  iExists rv.(raft.raft.trk'), rv.(raft.raft.raftLog').
  iFrame "Htrk Hlog". rewrite /own_raft_bare.
  iExists rv, msgs, msgsAA, lok. iFrame "∗#%". all: done.
Qed.

Lemma own_raft_bare_join r id s f tv lg :
  own_raft_bare r id s f tv lg -∗
  own_tracker cfg tv s.(nstate.votes) -∗
  own_raftLog lg -∗
  own_raft_phys_at r id s f.
Proof.
  iIntros "H Htrk0 Hlog0". iNamed "H".
  rewrite /own_raft_phys_at. iExists rv, msgs, msgsAA, lok.
  rewrite Htv Hlg. iFrame "∗#%". all: done.
Qed.

(** The [⊣⊢] the two directions above are the halves of.  Stated as an
    equivalence on purpose: it is what keeps [own_raft_bare]'s copy of the
    conjunct list honest. *)
Lemma own_raft_phys_at_split r id s f :
  own_raft_phys_at r id s f ⊣⊢
  ∃ tv, own_raft_notrk r id s f tv ∗ own_tracker cfg tv s.(nstate.votes).
Proof.
  iSplit.
  - iIntros "H". iDestruct (own_raft_bare_split with "H") as (tv lg) "(H & Htrk0 & Hlog0)".
    iExists tv. iFrame "Htrk0". iExists lg. iFrame.
  - iIntros "H". iDestruct "H" as (tv) "[H Htrk0]".
    iDestruct "H" as (lg) "[H Hlog0]".
    iApply (own_raft_bare_join with "H Htrk0 Hlog0").
Qed.

Lemma own_raft_notrk_join r id s f tv :
  own_raft_notrk r id s f tv -∗
  own_tracker cfg tv s.(nstate.votes) -∗
  own_raft_phys_at r id s f.
Proof.
  iIntros "H Htrk0". iDestruct "H" as (lg) "[H Hlog0]".
  iApply (own_raft_bare_join with "H Htrk0 Hlog0").
Qed.

Lemma own_raft_phys_split r id s :
  own_raft_phys r id s ⊣⊢
  ∃ tv, own_raft_notrk r id s (step_func_of s.(nstate.role)) tv ∗
        own_tracker cfg tv s.(nstate.votes).
Proof. apply own_raft_phys_at_split. Qed.

(** Re-sealing [own_raft_bare], in the shape of [own_raft_phys_at_intro]:
    the two [own_tracker]/[own_raftLog] arguments are gone and the two
    field equations join the pure premises. *)
Lemma own_raft_bare_intro r id s f tv lg (rv : raft.raft.t)
    (msgs msgsAA : list raftpb.Message.t) (lok : interface.t_ok) :
  rv.(raft.raft.id') = id →
  rv.(raft.raft.Term') = s.(nstate.term) →
  rv.(raft.raft.Vote') = s.(nstate.vote) →
  rv.(raft.raft.lead') = s.(nstate.lead) →
  rv.(raft.raft.state') = state_w64 s.(nstate.role) →
  rv.(raft.raft.step') = f →
  rv.(raft.raft.trk') = tv →
  rv.(raft.raft.raftLog') = lg →
  s.(nstate.outbox) ≡ₚ abs_outbox msgs msgsAA →
  rv.(raft.raft.preVote') = false →
  rv.(raft.raft.checkQuorum') = false →
  rv.(raft.raft.isLearner') = false →
  rv.(raft.raft.leadTransferee') = W64 0 →
  id ≠ W64 0 →
  0 < sint.Z rv.(raft.raft.electionTimeout') →
  rv.(raft.raft.logger') = interface.ok lok →
  is_Logger lok -∗
  r ↦ rv -∗
  rv.(raft.raft.msgs') ↦* msgs -∗
  own_slice_cap raftpb.Message.t rv.(raft.raft.msgs') (DfracOwn 1) -∗
  rv.(raft.raft.msgsAfterAppend') ↦* msgsAA -∗
  own_slice_cap raftpb.Message.t rv.(raft.raft.msgsAfterAppend') (DfracOwn 1) -∗
  own_raft_misc rv.(raft.raft.readStates') rv.(raft.raft.readOnly')
    rv.(raft.raft.pendingReadIndexMessages') -∗
  own_raft_bare r id s f tv lg.
Proof.
  intros Hid Hterm Hvote Hlead Hstate Hstepfn Htv Hlg Houtbox HnoPreVote
    HnoCheckQuorum HnoLearner HnoTransfer Hid_nz HelectionTimeout Hlok.
  iIntros "#Hlogger Hr Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc".
  rewrite /own_raft_bare. iExists rv, msgs, msgsAA, lok. iFrame "∗#%". all: done.
Qed.

(** The same for [own_raft_notrk]: the log is an argument again, the tracker
    is not.  [maybeSendSnapshot] re-seals with this, exactly where it used to
    use [own_raft_phys_intro]. *)
Lemma own_raft_notrk_intro r id s f tv (rv : raft.raft.t)
    (msgs msgsAA : list raftpb.Message.t) (lok : interface.t_ok) :
  rv.(raft.raft.id') = id →
  rv.(raft.raft.Term') = s.(nstate.term) →
  rv.(raft.raft.Vote') = s.(nstate.vote) →
  rv.(raft.raft.lead') = s.(nstate.lead) →
  rv.(raft.raft.state') = state_w64 s.(nstate.role) →
  rv.(raft.raft.step') = f →
  rv.(raft.raft.trk') = tv →
  s.(nstate.outbox) ≡ₚ abs_outbox msgs msgsAA →
  rv.(raft.raft.preVote') = false →
  rv.(raft.raft.checkQuorum') = false →
  rv.(raft.raft.isLearner') = false →
  rv.(raft.raft.leadTransferee') = W64 0 →
  id ≠ W64 0 →
  0 < sint.Z rv.(raft.raft.electionTimeout') →
  rv.(raft.raft.logger') = interface.ok lok →
  is_Logger lok -∗
  r ↦ rv -∗
  own_raftLog rv.(raft.raft.raftLog') -∗
  rv.(raft.raft.msgs') ↦* msgs -∗
  own_slice_cap raftpb.Message.t rv.(raft.raft.msgs') (DfracOwn 1) -∗
  rv.(raft.raft.msgsAfterAppend') ↦* msgsAA -∗
  own_slice_cap raftpb.Message.t rv.(raft.raft.msgsAfterAppend') (DfracOwn 1) -∗
  own_raft_misc rv.(raft.raft.readStates') rv.(raft.raft.readOnly')
    rv.(raft.raft.pendingReadIndexMessages') -∗
  own_raft_notrk r id s f tv.
Proof.
  intros Hid Hterm Hvote Hlead Hstate Hstepfn Htv Houtbox HnoPreVote
    HnoCheckQuorum HnoLearner HnoTransfer Hid_nz HelectionTimeout Hlok.
  iIntros "#Hlogger Hr Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc".
  rewrite /own_raft_notrk. iExists rv.(raft.raft.raftLog'). iFrame "Hlog".
  iApply (own_raft_bare_intro with
    "Hlogger Hr Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done.
Qed.


End proof.
