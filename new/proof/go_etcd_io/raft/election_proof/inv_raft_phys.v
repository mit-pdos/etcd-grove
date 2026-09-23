(** * Physical ownership of the raft struct *)

Require Export New.proof.go_etcd_io.raft.election_proof.inv_raftlog.
Require Export New.proof.go_etcd_io.raft.election_proof.inv_tracker.
Require Export New.proof.go_etcd_io.raft.election_proof.inv_logger.
Require Export New.proof.go_etcd_io.raft.election_proof.inv_misc.

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

Implicit Type s : nstate.t.

(** The tracker and log conjuncts of [own_raft_phys], at loan state
    [lent] ([nstate.lent], [defs.v]): the heap itself when nothing is on
    loan; when the caller holds it, nothing but the tracker value it was
    lent at.  A proof that opens [own_raft_phys] under
    [s.(nstate.lent) = None] turns [Htrk]/[Hlog] into [own_tracker] /
    [own_raftLog] with the [_open] lemmas and back with [_close]; none of
    them needs a [simpl] of the goal. *)
Definition own_tracker_unless (lent : option tracker.ProgressTracker.t)
    (tv : tracker.ProgressTracker.t) (votes : gmap w64 bool) : iProp Σ :=
  match lent with
  | None => own_tracker cfg tv votes
  | Some tv0 => ⌜ tv = tv0 ⌝
  end.

Definition own_raftLog_unless (lent : option tracker.ProgressTracker.t)
    (l : loc) : iProp Σ :=
  match lent with None => own_raftLog l | Some _ => True end.

Lemma own_tracker_unless_open lent tv votes :
  lent = None → own_tracker_unless lent tv votes -∗ own_tracker cfg tv votes.
Proof. intros ->. auto. Qed.

Lemma own_tracker_unless_close lent tv votes :
  lent = None → own_tracker cfg tv votes -∗ own_tracker_unless lent tv votes.
Proof. intros ->. auto. Qed.

Lemma own_raftLog_unless_open lent l :
  lent = None → own_raftLog_unless lent l -∗ own_raftLog l.
Proof. intros ->. auto. Qed.

Lemma own_raftLog_unless_close lent l :
  lent = None → own_raftLog l -∗ own_raftLog_unless lent l.
Proof. intros ->. auto. Qed.

(** The two conjuncts while on loan: nothing to own. *)
Lemma own_tracker_unless_lent tv votes :
  ⊢ own_tracker_unless (Some tv) tv votes.
Proof. by iPureIntro. Qed.

Lemma own_raftLog_unless_lent tv l : ⊢ own_raftLog_unless (Some tv) l.
Proof. auto. Qed.

(** While on loan, the tracker field is the value it was lent at. *)
Lemma own_tracker_unless_lent_eq tv0 tv votes :
  own_tracker_unless (Some tv0) tv votes -∗ ⌜ tv = tv0 ⌝.
Proof. auto. Qed.

(** ** Physical ownership of the raft struct

    [own_raft_phys r id s] is full ownership of the [raft] struct at [r] and
    of everything hanging off it, in a state described by the physical
    abstract state [s : nstate.t] ([defs.v]).

    **This is the only ownership predicate for the raft struct, and every
    Go-level spec is stated on it.**  If a function cannot be specified this
    way, the fix is to make [nstate.t] more precise and this predicate with
    it -- not to add a variant.  See [nstate.t] for the three variants this
    replaced on 2026-09-22 and notes/decisions.md, "Three layers", for why.

    There is no [γ]: this predicate says nothing about ghost state.  The
    connection to the protocol is [nstate_rel] ([defs.v]), and [Step]'s spec
    is the only one that mentions both. *)
Definition own_raft_phys (r : loc) (id : w64) s : iProp Σ :=
  ∃ (rv : raft.raft.t) (msgs msgsAA : list raftpb.Message.t)
    (lok : interface.t_ok),
  "Hr" ∷ r ↦ rv ∗

  (** the abstraction relation *)
  "%Hid" ∷ ⌜ rv.(raft.raft.id') = id ⌝ ∗
  "%Hterm" ∷ ⌜ rv.(raft.raft.Term') = s.(nstate.term) ⌝ ∗
  "%Hvote" ∷ ⌜ rv.(raft.raft.Vote') = s.(nstate.vote) ⌝ ∗
  "%Hlead" ∷ ⌜ rv.(raft.raft.lead') = s.(nstate.lead) ⌝ ∗
  "%Hstate" ∷ ⌜ rv.(raft.raft.state') = state_w64 s.(nstate.role) ⌝ ∗
  (** [r.step].  Not a function of the role: [becomeFollower] assigns it
      before [reset] runs, and [newRaft] starts with it nil.  That the two
      agree is [nstate_wf], which [Step] carries. *)
  "%Hstepfn" ∷ ⌜ rv.(raft.raft.step') = s.(nstate.stepfn) ⌝ ∗

  (** the vote tally, and the rest of the heap the tracker points at.  The
      tracker's own bytes are covered by [Hr] above, since [trk] is embedded
      by value; this is only what hangs off it. *)
  "Htrk" ∷ own_tracker_unless s.(nstate.lent) rv.(raft.raft.trk') s.(nstate.votes) ∗
  (** The progress map, pinned to [s.(nstate.progress)].  [own_tracker] holds
      the same (read-only, hence duplicable) points-to; this copy is what
      lets a proof know *which* [Progress] a peer has after a call it made
      with the tracker sealed -- [maybeSendAppend] borrows [pr] before
      [r.send] and must come back to the same pointer after. *)
  "#Hprs" ∷ rv.(raft.raft.trk').(tracker.ProgressTracker.Progress')
              ↦$□ s.(nstate.progress) ∗

  (** the log, unless it is on loan to the caller ([nstate.lent]) *)
  "%Hlogp" ∷ ⌜ rv.(raft.raft.raftLog') = s.(nstate.log) ⌝ ∗
  "Hlog" ∷ own_raftLog_unless s.(nstate.lent) rv.(raft.raft.raftLog') ∗

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

(** Re-sealing [own_raft_phys] after a proof has taken it apart.

    [iFrame "∗#%"] against the unfolded predicate costs ~17s per use (2026-09-17
    measurement): [iFrame "%"] alone tries every pure fact in the Coq context
    against every one of the conjuncts. This lemma makes a re-seal a single
    [iApply] with named hypotheses and pure side goals:

      iApply (own_raft_phys_intro with
        "Hr Hlogger Hprs Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done.

    The pure premises are in the order the conjuncts appear in the predicate.
    [r ↦ rv] is the first spatial argument **on purpose**: it is what fixes
    [rv], at the struct value the heap holds *now*.  If a persistent
    argument came first, [rv] would be fixed from it -- at whatever struct
    value that hypothesis was stated -- and after any field write the heap's
    [r ↦ (rv <| … |>)] would then fail to match. *)
Lemma own_raft_phys_intro r id s (rv : raft.raft.t)
    (msgs msgsAA : list raftpb.Message.t) (lok : interface.t_ok) :
  rv.(raft.raft.id') = id →
  rv.(raft.raft.Term') = s.(nstate.term) →
  rv.(raft.raft.Vote') = s.(nstate.vote) →
  rv.(raft.raft.lead') = s.(nstate.lead) →
  rv.(raft.raft.state') = state_w64 s.(nstate.role) →
  rv.(raft.raft.step') = s.(nstate.stepfn) →
  s.(nstate.outbox) ≡ₚ abs_outbox msgs msgsAA →
  rv.(raft.raft.preVote') = false →
  rv.(raft.raft.checkQuorum') = false →
  rv.(raft.raft.isLearner') = false →
  rv.(raft.raft.leadTransferee') = W64 0 →
  id ≠ W64 0 →
  0 < sint.Z rv.(raft.raft.electionTimeout') →
  rv.(raft.raft.logger') = interface.ok lok →
  rv.(raft.raft.raftLog') = s.(nstate.log) →
  r ↦ rv -∗
  is_Logger lok -∗
  rv.(raft.raft.trk').(tracker.ProgressTracker.Progress') ↦$□ s.(nstate.progress) -∗
  own_tracker_unless s.(nstate.lent) rv.(raft.raft.trk') s.(nstate.votes) -∗
  own_raftLog_unless s.(nstate.lent) rv.(raft.raft.raftLog') -∗
  rv.(raft.raft.msgs') ↦* msgs -∗
  own_slice_cap raftpb.Message.t rv.(raft.raft.msgs') (DfracOwn 1) -∗
  rv.(raft.raft.msgsAfterAppend') ↦* msgsAA -∗
  own_slice_cap raftpb.Message.t rv.(raft.raft.msgsAfterAppend') (DfracOwn 1) -∗
  own_raft_misc rv.(raft.raft.readStates') rv.(raft.raft.readOnly')
    rv.(raft.raft.pendingReadIndexMessages') -∗
  own_raft_phys r id s.
Proof.
  intros Hid Hterm Hvote Hlead Hstate Hstepfn Houtbox HnoPreVote HnoCheckQuorum
    HnoLearner HnoTransfer Hid_nz HelectionTimeout Hlok Hlogp.
  iIntros "Hr #Hlogger #Hprs Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc".
  rewrite /own_raft_phys. iExists rv, msgs, msgsAA, lok. iFrame "∗#%".
Qed.

(** The progress map in [s] is the tracker's, and so has domain [cfg].  Read
    out without consuming anything. *)
Lemma own_raft_phys_progress_dom r id s :
  s.(nstate.lent) = None →
  own_raft_phys r id s -∗ ⌜ dom s.(nstate.progress) = cfg ⌝ ∗ own_raft_phys r id s.
Proof.
  iIntros (Hlent) "H". iNamed "H".
  iDestruct (own_tracker_unless_open _ _ _ Hlent with "Htrk") as "Htrk".
  iDestruct (own_tracker_progress_map with "Htrk") as (prs) "(#Hprs' & %Hdom & Htrk)".
  iDestruct (progress_map_agree with "Hprs Hprs'") as %<-.
  iDestruct (own_tracker_unless_close _ _ _ Hlent with "Htrk") as "Htrk".
  iSplitR; first done.
  rewrite /own_raft_phys. iExists rv, msgs, msgsAA, lok. iFrame "∗#%".
Qed.

(** Changing only the outbox, up to permutation. *)
Lemma own_raft_phys_outbox r id s (o : list msg.t) :
  o ≡ₚ s.(nstate.outbox) →
  own_raft_phys r id s -∗ own_raft_phys r id (s <| nstate.outbox := o |>).
Proof.
  iIntros (Ho) "H". iNamed "H".
  rewrite /own_raft_phys. iExists rv, msgs, msgsAA, lok. simpl. iFrame "∗#%".
  iPureIntro. by rewrite Ho.
Qed.

(** Sending nothing, in both directions: an exit that sends nothing proves
    a postcondition stated at [send_msgs s ms] with [ms = []], and a [send]
    of a message the model does not see comes back at [send_msgs s []]. *)
Lemma own_raft_phys_send_nil r id s :
  own_raft_phys r id s -∗ own_raft_phys r id (send_msgs s []).
Proof.
  rewrite /send_msgs app_nil_r. destruct s. auto.
Qed.

Lemma own_raft_phys_unsend r id s :
  own_raft_phys r id (send_msgs s []) -∗ own_raft_phys r id s.
Proof.
  rewrite /send_msgs app_nil_r. destruct s. auto.
Qed.

End proof.
