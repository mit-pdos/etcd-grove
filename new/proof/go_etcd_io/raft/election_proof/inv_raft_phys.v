(** * Physical ownership of the raft struct *)

Require Export New.proof.go_etcd_io.raft.election_proof.inv_raftlog.
Require Export New.proof.go_etcd_io.raft.election_proof.inv_tracker.
Require Export New.proof.go_etcd_io.raft.election_proof.inv_logger.
Require Export New.proof.go_etcd_io.raft.election_proof.inv_misc.

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
    (tv : tracker.ProgressTracker.t) (votes : gmap w64 bool)
    (prs : gmap w64 loc) : iProp Σ :=
  match lent with
  | None => own_tracker cfg tv votes prs
  | Some tv0 => ⌜ tv = tv0 ⌝
  end.

(** The log's state is quantified here rather than kept in [nstate.t]: no
    spec on the election path needs to relate it across a call, and every
    function that reads the log re-opens it (notes/decisions.md, "One
    predicate per object").  Only at no page: a page loan never outlives
    the function that took it. *)
Definition own_raftLog_unless (lent : option tracker.ProgressTracker.t)
    (l : loc) : iProp Σ :=
  match lent with
  | None => ∃ ls, ⌜ ls.(logstate.page) = None ⌝ ∗ own_raftLog l ls
  | Some _ => True
  end.

Lemma own_tracker_unless_open lent tv votes prs :
  lent = None → own_tracker_unless lent tv votes prs -∗ own_tracker cfg tv votes prs.
Proof. intros ->. auto. Qed.

Lemma own_tracker_unless_close lent tv votes prs :
  lent = None → own_tracker cfg tv votes prs -∗ own_tracker_unless lent tv votes prs.
Proof. intros ->. auto. Qed.

Lemma own_raftLog_unless_open lent l :
  lent = None → own_raftLog_unless lent l -∗
  ∃ ls, ⌜ ls.(logstate.page) = None ⌝ ∗ own_raftLog l ls.
Proof. intros ->. auto. Qed.

(** The page premise is a wand premise rather than a Coq one so that the
    log fixes [ls] first: callers write [with "Hlog [//]"]. *)
Lemma own_raftLog_unless_close lent l ls :
  lent = None →
  own_raftLog l ls -∗ ⌜ ls.(logstate.page) = None ⌝ -∗ own_raftLog_unless lent l.
Proof. intros ->. iIntros "H %Hpg". iExists ls. iFrame "H". done. Qed.

(** The two conjuncts while on loan: nothing to own. *)
Lemma own_tracker_unless_lent tv votes prs :
  ⊢ own_tracker_unless (Some tv) tv votes prs.
Proof. by iPureIntro. Qed.

Lemma own_raftLog_unless_lent tv l : ⊢ own_raftLog_unless (Some tv) l.
Proof. auto. Qed.

(** While on loan, the tracker field is the value it was lent at. *)
Lemma own_tracker_unless_lent_eq tv0 tv votes prs :
  own_tracker_unless (Some tv0) tv votes prs -∗ ⌜ tv = tv0 ⌝.
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
Definition own_raft_phys_def (r : loc) (id : w64) s : iProp Σ :=
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

  (** the vote tally, the progress map and the rest of the heap the tracker
      points at.  The tracker's own bytes are covered by [Hr] above, since
      [trk] is embedded by value; this is only what hangs off it.  Indexed
      by [s.(nstate.progress)]: that is what lets a proof know *which*
      [Progress] a peer has after a call it made with the struct sealed.
      (From 2026-09-22 to 2026-09-23 a second, persistent copy of the
      progress map's points-to sat here, beside the one inside
      [own_tracker]; indexing [own_tracker] by the map made it redundant.) *)
  "Htrk" ∷ own_tracker_unless s.(nstate.lent) rv.(raft.raft.trk')
             s.(nstate.votes) s.(nstate.progress) ∗

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

(** Sealed: outside this file [own_raft_phys] cannot be unfolded, so a
    program proof that reaches into the representation does not compile.
    Every access goes through the interface at the end of this section. *)
Local Definition own_raft_phys_aux : seal (@own_raft_phys_def). Proof. by eexists. Qed.
Definition own_raft_phys := own_raft_phys_aux.(unseal).
Local Definition own_raft_phys_unseal :
  @own_raft_phys = @own_raft_phys_def := own_raft_phys_aux.(seal_eq).

(** Open the predicate, in this file only. *)
Local Tactic Notation "iNamed_phys" constr(H) :=
  iEval (rewrite own_raft_phys_unseal) in H; iNamed H.

(** Re-sealing [own_raft_phys] after a proof has taken it apart.

    [iFrame "∗#%"] against the unfolded predicate costs ~17s per use (2026-09-17
    measurement): [iFrame "%"] alone tries every pure fact in the Coq context
    against every one of the conjuncts. This lemma makes a re-seal a single
    [iApply] with named hypotheses and pure side goals:

      iApply (own_raft_phys_intro with
        "Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done.

    The pure premises are in the order the conjuncts appear in the predicate.
    [r ↦ rv] is the first spatial argument **on purpose**: it is what fixes
    [rv], at the struct value the heap holds *now*.  If another argument
    came first, [rv] would be fixed from it -- at whatever struct value that
    hypothesis was stated -- and after any field write the heap's
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
  own_tracker_unless s.(nstate.lent) rv.(raft.raft.trk') s.(nstate.votes)
    s.(nstate.progress) -∗
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
  iIntros "Hr #Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc".
  rewrite own_raft_phys_unseal /own_raft_phys_def. iExists rv, msgs, msgsAA, lok. iFrame "∗#%".
Qed.

(** The progress map in [s] is the tracker's, and so has domain [cfg].  Read
    out without consuming anything. *)
Lemma own_raft_phys_progress_dom r id s :
  s.(nstate.lent) = None →
  own_raft_phys r id s -∗ ⌜ dom s.(nstate.progress) = cfg ⌝ ∗ own_raft_phys r id s.
Proof.
  iIntros (Hlent) "H". iNamed_phys "H".
  iDestruct (own_tracker_unless_open _ _ _ _ Hlent with "Htrk") as "Htrk".
  iDestruct (own_tracker_progress_map with "Htrk") as "(#Hprs & %Hdom & Htrk)".
  iDestruct (own_tracker_unless_close _ _ _ _ Hlent with "Htrk") as "Htrk".
  iSplitR; first done.
  rewrite own_raft_phys_unseal /own_raft_phys_def. iExists rv, msgs, msgsAA, lok. iFrame "∗#%".
Qed.

(** Changing only the outbox, up to permutation. *)
Lemma own_raft_phys_outbox r id s (o : list msg.t) :
  o ≡ₚ s.(nstate.outbox) →
  own_raft_phys r id s -∗ own_raft_phys r id (s <| nstate.outbox := o |>).
Proof.
  iIntros (Ho) "H". iNamed_phys "H".
  rewrite own_raft_phys_unseal /own_raft_phys_def. iExists rv, msgs, msgsAA, lok. simpl. iFrame "∗#%".
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


(** ** The interface: field lemmas and accessors

    **Program proofs do not unfold [own_raft_phys].**  Every access to the
    raft struct goes through one of the lemmas below, so that the struct's
    representation -- [r ↦ rv], the abstraction relation, the scope
    assumptions -- is written down, and relied on, in this file alone.
    Changing the representation then means re-proving this section, not the
    program proofs.  (Decided 2026-09-24; notes/decisions.md, "Program proofs
    do not unfold [own_raft_phys]".)

    [wp_auto] is *not* used for these accesses.  Its field automation
    builds on full ownership of the struct, [r ↦ rv], which is exactly the
    representation this predicate hides: with [own_raft_phys] sealed,
    [wp_auto] stops in front of a load or store of a raft field, and the
    proof continues with the lemma for that field.  [wp_raft_field] (after
    the section) picks it for the accesses with no outputs to name.

    There are three kinds.

    - **Scalar fields**, one Hoare triple per load and per store, stated at
      the expression [wp_auto] leaves behind: [![t] #(r.[raft.raft.t, f])]
      and [GoStore t (#(r.[raft.raft.t, f]), #v)%V].  A field [nstate.t]
      tracks is loaded at its abstract value and a store updates [s]; a
      field pinned by a scope assumption is loaded at the pinned value and
      has no store (or only a store of that value); a field the abstraction
      does not track is loaded at an unknown value and stored freely.  If a
      proof needs to know more about one of the latter -- that two loads
      agree, say -- the rule is the usual one: add it to [nstate.t].
    - **Heap hanging off a field**: the tracker, the log, the two message
      queues, the [readOnly] object.  An *accessor* hands out the field's
      points-to and the object's own predicate, together with a wand that
      takes them back -- possibly changed -- and gives [own_raft_phys] at
      the correspondingly changed state.  What the object is then used for
      (a map lookup in [trk.Progress], [raftLog] methods, [append] on a
      queue) is the object's business, specified by its own predicate, so
      no operation on it is duplicated here.
    - **Loans**: [own_raft_phys_lend] / [own_raft_phys_unlend] move the
      tracker's heap and the log out of the predicate and back
      ([nstate.lent]), and [own_raft_phys_trk_lent] reaches the tracker
      field while they are out. *)

Local Lemma wp_load_access {V t} `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}
    (l : loc) (v : V) (P : iProp Σ) `{!AccessStrict (l ↦ v) (l ↦ v) P P} Φ :
  P -∗ ▷ (P -∗ Φ #v) -∗ WP ![t] #l {{ Φ }}.
Proof.
  iIntros "HP HΦ".
  iDestruct (access_strict (A:=l ↦ v) (A':=l ↦ v) with "HP") as "[Hl Hback]".
  wp_apply (wp_load with "Hl") as "Hl".
  iApply "HΦ". iApply "Hback". iFrame.
Qed.

Local Lemma wp_store_access {V t} `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}
    (l : loc) (v w : V) (P P' : iProp Σ) `{!AccessStrict (l ↦ v) (l ↦ w) P P'} Φ :
  P -∗ ▷ (P' -∗ Φ #()) -∗ WP GoStore t (#l, #w)%V {{ Φ }}.
Proof.
  iIntros "HP HΦ".
  iDestruct (access_strict (A:=l ↦ v) (A':=l ↦ w) with "HP") as "[Hl Hback]".
  wp_apply (wp_store with "Hl") as "Hl".
  iApply "HΦ". iApply "Hback". iFrame.
Qed.

(** Re-seal at the state the goal names.  Given explicitly because
    otherwise [own_raft_phys_intro]'s [s] is fixed by [Htrk] -- at the state
    *before* the access -- and the conclusion no longer matches. *)
Local Ltac reseal :=
  lazymatch goal with
  | |- environments.envs_entails _ (own_raft_phys _ _ ?s') =>
      iApply (own_raft_phys_intro _ _ s' with
        "Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
      try done
  end.

Local Ltac load_proof :=
  iIntros (Φ) "H HΦ"; iNamed_phys "H";
  wp_apply (wp_load_access with "Hr") as "Hr".

Local Ltac store_proof :=
  iIntros (Φ) "H HΦ"; iNamed_phys "H";
  wp_apply (wp_store_access with "Hr") as "Hr";
  iApply "HΦ"; reseal.

(** *** Loads of fields [nstate.t] tracks, and of the pinned ones *)

Lemma wp_raft_load_id r id s :
  {{{ own_raft_phys r id s }}}
    ![go.uint64] #(r.[raft.raft.t, "id"])
  {{{ RET #id; own_raft_phys r id s }}}.
Proof. load_proof. rewrite Hid. iApply "HΦ". reseal. Qed.

Lemma wp_raft_load_Term r id s :
  {{{ own_raft_phys r id s }}}
    ![go.uint64] #(r.[raft.raft.t, "Term"])
  {{{ RET #s.(nstate.term); own_raft_phys r id s }}}.
Proof. load_proof. rewrite Hterm. iApply "HΦ". reseal. Qed.

Lemma wp_raft_load_Vote r id s :
  {{{ own_raft_phys r id s }}}
    ![go.uint64] #(r.[raft.raft.t, "Vote"])
  {{{ RET #s.(nstate.vote); own_raft_phys r id s }}}.
Proof. load_proof. rewrite Hvote. iApply "HΦ". reseal. Qed.

Lemma wp_raft_load_lead r id s :
  {{{ own_raft_phys r id s }}}
    ![go.uint64] #(r.[raft.raft.t, "lead"])
  {{{ RET #s.(nstate.lead); own_raft_phys r id s }}}.
Proof. load_proof. rewrite Hlead. iApply "HΦ". reseal. Qed.

Lemma wp_raft_load_state r id s :
  {{{ own_raft_phys r id s }}}
    ![raft.StateType] #(r.[raft.raft.t, "state"])
  {{{ RET #(state_w64 s.(nstate.role)); own_raft_phys r id s }}}.
Proof. load_proof. rewrite Hstate. iApply "HΦ". reseal. Qed.

Lemma wp_raft_load_step r id s :
  {{{ own_raft_phys r id s }}}
    ![raft.stepFunc] #(r.[raft.raft.t, "step"])
  {{{ RET #s.(nstate.stepfn); own_raft_phys r id s }}}.
Proof. load_proof. rewrite Hstepfn. iApply "HΦ". reseal. Qed.

(** The log's *location*.  Its contents are [own_raft_phys_log]'s. *)
Lemma wp_raft_load_raftLog r id s :
  {{{ own_raft_phys r id s }}}
    ![go.PointerType raft.raftLog] #(r.[raft.raft.t, "raftLog"])
  {{{ RET #s.(nstate.log); own_raft_phys r id s }}}.
Proof. load_proof. rewrite -Hlogp. iApply "HΦ". reseal. Qed.

Lemma wp_raft_load_logger r id s :
  {{{ own_raft_phys r id s }}}
    ![raft.Logger] #(r.[raft.raft.t, "logger"])
  {{{ (lok : interface.t_ok), RET #(interface.ok lok);
      own_raft_phys r id s ∗ is_Logger lok }}}.
Proof. load_proof. rewrite Hlok. iApply "HΦ". iSplitL; [reseal | done]. Qed.

Lemma wp_raft_load_checkQuorum r id s :
  {{{ own_raft_phys r id s }}}
    ![go.bool] #(r.[raft.raft.t, "checkQuorum"])
  {{{ RET #false; own_raft_phys r id s }}}.
Proof. load_proof. rewrite HnoCheckQuorum. iApply "HΦ". reseal. Qed.

Lemma wp_raft_load_preVote r id s :
  {{{ own_raft_phys r id s }}}
    ![go.bool] #(r.[raft.raft.t, "preVote"])
  {{{ RET #false; own_raft_phys r id s }}}.
Proof. load_proof. rewrite HnoPreVote. iApply "HΦ". reseal. Qed.

Lemma wp_raft_load_isLearner r id s :
  {{{ own_raft_phys r id s }}}
    ![go.bool] #(r.[raft.raft.t, "isLearner"])
  {{{ RET #false; own_raft_phys r id s }}}.
Proof. load_proof. rewrite HnoLearner. iApply "HΦ". reseal. Qed.

Lemma wp_raft_load_leadTransferee r id s :
  {{{ own_raft_phys r id s }}}
    ![go.uint64] #(r.[raft.raft.t, "leadTransferee"])
  {{{ RET #(W64 0); own_raft_phys r id s }}}.
Proof. load_proof. rewrite HnoTransfer. iApply "HΦ". reseal. Qed.

(** *** Loads of fields the abstraction does not track *)

Lemma wp_raft_load_electionTimeout r id s :
  {{{ own_raft_phys r id s }}}
    ![go.int] #(r.[raft.raft.t, "electionTimeout"])
  {{{ (v : w64), RET #v; own_raft_phys r id s ∗ ⌜ 0 < sint.Z v ⌝ }}}.
Proof. load_proof. iApply "HΦ". iSplitL; [reseal | done]. Qed.

Lemma wp_raft_load_electionElapsed r id s :
  {{{ own_raft_phys r id s }}}
    ![go.int] #(r.[raft.raft.t, "electionElapsed"])
  {{{ (v : w64), RET #v; own_raft_phys r id s }}}.
Proof. load_proof. iApply "HΦ". reseal. Qed.

Lemma wp_raft_load_heartbeatTimeout r id s :
  {{{ own_raft_phys r id s }}}
    ![go.int] #(r.[raft.raft.t, "heartbeatTimeout"])
  {{{ (v : w64), RET #v; own_raft_phys r id s }}}.
Proof. load_proof. iApply "HΦ". reseal. Qed.

Lemma wp_raft_load_randomizedElectionTimeout r id s :
  {{{ own_raft_phys r id s }}}
    ![go.int] #(r.[raft.raft.t, "randomizedElectionTimeout"])
  {{{ (v : w64), RET #v; own_raft_phys r id s }}}.
Proof. load_proof. iApply "HΦ". reseal. Qed.

Lemma wp_raft_load_pendingConfIndex r id s :
  {{{ own_raft_phys r id s }}}
    ![go.uint64] #(r.[raft.raft.t, "pendingConfIndex"])
  {{{ (v : w64), RET #v; own_raft_phys r id s }}}.
Proof. load_proof. iApply "HΦ". reseal. Qed.

Lemma wp_raft_load_uncommittedSize r id s :
  {{{ own_raft_phys r id s }}}
    ![raft.entryPayloadSize] #(r.[raft.raft.t, "uncommittedSize"])
  {{{ (v : raft.entryPayloadSize.t), RET #v; own_raft_phys r id s }}}.
Proof. load_proof. iApply "HΦ". reseal. Qed.

Lemma wp_raft_load_maxUncommittedSize r id s :
  {{{ own_raft_phys r id s }}}
    ![raft.entryPayloadSize] #(r.[raft.raft.t, "maxUncommittedSize"])
  {{{ (v : raft.entryPayloadSize.t), RET #v; own_raft_phys r id s }}}.
Proof. load_proof. iApply "HΦ". reseal. Qed.

Lemma wp_raft_load_maxMsgSize r id s :
  {{{ own_raft_phys r id s }}}
    ![raft.entryEncodingSize] #(r.[raft.raft.t, "maxMsgSize"])
  {{{ (v : raft.entryEncodingSize.t), RET #v; own_raft_phys r id s }}}.
Proof. load_proof. iApply "HΦ". reseal. Qed.

(** *** Stores to fields [nstate.t] tracks *)

Lemma wp_raft_store_Term r id s (v : w64) :
  {{{ own_raft_phys r id s }}}
    GoStore go.uint64 (#(r.[raft.raft.t, "Term"]), #v)%V
  {{{ RET #(); own_raft_phys r id (s <| nstate.term := v |>) }}}.
Proof. store_proof. Qed.

Lemma wp_raft_store_Vote r id s (v : w64) :
  {{{ own_raft_phys r id s }}}
    GoStore go.uint64 (#(r.[raft.raft.t, "Vote"]), #v)%V
  {{{ RET #(); own_raft_phys r id (s <| nstate.vote := v |>) }}}.
Proof. store_proof. Qed.

Lemma wp_raft_store_lead r id s (v : w64) :
  {{{ own_raft_phys r id s }}}
    GoStore go.uint64 (#(r.[raft.raft.t, "lead"]), #v)%V
  {{{ RET #(); own_raft_phys r id (s <| nstate.lead := v |>) }}}.
Proof. store_proof. Qed.

(** Stated at [state_w64 ro], so the caller names the role; the Go code
    stores the constant ([StateFollower] = [W64 0]), which unifies with
    [state_w64 role.Follower] by computation. *)
Lemma wp_raft_store_state r id s (ro : role.t) :
  {{{ own_raft_phys r id s }}}
    GoStore raft.StateType (#(r.[raft.raft.t, "state"]), #(state_w64 ro))%V
  {{{ RET #(); own_raft_phys r id (s <| nstate.role := ro |>) }}}.
Proof. store_proof. Qed.

Lemma wp_raft_store_step r id s (f : func.t) :
  {{{ own_raft_phys r id s }}}
    GoStore raft.stepFunc (#(r.[raft.raft.t, "step"]), #f)%V
  {{{ RET #(); own_raft_phys r id (s <| nstate.stepfn := f |>) }}}.
Proof. store_proof. Qed.

(** *** Stores to fields the abstraction does not track, and the pinned one *)

Lemma wp_raft_store_tick r id s (f : func.t) :
  {{{ own_raft_phys r id s }}}
    GoStore (go.FunctionType (go.Signature [] false []))
      (#(r.[raft.raft.t, "tick"]), #f)%V
  {{{ RET #(); own_raft_phys r id s }}}.
Proof. store_proof. Qed.

Lemma wp_raft_store_electionElapsed r id s (v : w64) :
  {{{ own_raft_phys r id s }}}
    GoStore go.int (#(r.[raft.raft.t, "electionElapsed"]), #v)%V
  {{{ RET #(); own_raft_phys r id s }}}.
Proof. store_proof. Qed.

Lemma wp_raft_store_heartbeatElapsed r id s (v : w64) :
  {{{ own_raft_phys r id s }}}
    GoStore go.int (#(r.[raft.raft.t, "heartbeatElapsed"]), #v)%V
  {{{ RET #(); own_raft_phys r id s }}}.
Proof. store_proof. Qed.

Lemma wp_raft_store_randomizedElectionTimeout r id s (v : w64) :
  {{{ own_raft_phys r id s }}}
    GoStore go.int (#(r.[raft.raft.t, "randomizedElectionTimeout"]), #v)%V
  {{{ RET #(); own_raft_phys r id s }}}.
Proof. store_proof. Qed.

Lemma wp_raft_store_pendingConfIndex r id s (v : w64) :
  {{{ own_raft_phys r id s }}}
    GoStore go.uint64 (#(r.[raft.raft.t, "pendingConfIndex"]), #v)%V
  {{{ RET #(); own_raft_phys r id s }}}.
Proof. store_proof. Qed.

Lemma wp_raft_store_uncommittedSize r id s (v : raft.entryPayloadSize.t) :
  {{{ own_raft_phys r id s }}}
    GoStore raft.entryPayloadSize (#(r.[raft.raft.t, "uncommittedSize"]), #v)%V
  {{{ RET #(); own_raft_phys r id s }}}.
Proof. store_proof. Qed.

(** Only [None]: no leader transfer is in scope. *)
Lemma wp_raft_store_leadTransferee r id s :
  {{{ own_raft_phys r id s }}}
    GoStore go.uint64 (#(r.[raft.raft.t, "leadTransferee"]), #(W64 0))%V
  {{{ RET #(); own_raft_phys r id s }}}.
Proof. store_proof. Qed.

(** Two states that are equal: for a state reached by a run of field
    stores and the name a spec gives it ([become_follower s t l], say).
    Proving the [=] with [reflexivity] is cheap; leaving it to unification
    inside [iFrame] can run for minutes (notes/gotchas.md). *)
Lemma own_raft_phys_eq r id s1 s2 :
  s1 = s2 → own_raft_phys r id s1 -∗ own_raft_phys r id s2.
Proof. intros ->. iIntros "$". Qed.

(** *** Accessors *)

(** One field of the struct points-to, with a wand taking back *any* value.
    The generated [AccessStrict] store instance fixes the new value when it
    is applied, which is too early for a value a later call produces (see
    notes/gotchas.md); these unseal [l ↦ rv] instead.  The pattern names the
    field by position and keeps every other field in one hypothesis: framing
    the 33 field points-tos one by one ([iNamed], then [iFrame "∗%"]) cost
    ~40s per lemma, this ~6s (2026-09-24). *)
Local Ltac split_field_proof pat :=
  iIntros "Hr";
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=) in "Hr";
  iDestruct "Hr" as "[Hf %Hnn]";
  iDestruct "Hf" as pat;
  iFrame "Hx"; iIntros (x) "Hx";
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=);
  iFrame; done.

Local Lemma raft_split_trk (l : loc) (rv : raft.raft.t) :
  l ↦ rv -∗
  l.[raft.raft.t, "trk"] ↦ rv.(raft.raft.trk') ∗
  (∀ x, l.[raft.raft.t, "trk"] ↦ x -∗ l ↦ (rv <| raft.raft.trk' := x |>)).
Proof. split_field_proof "(? & ? & ? & ? & ? & ? & ? & Hx & Hrest)". Qed.

Local Lemma raft_split_msgs (l : loc) (rv : raft.raft.t) :
  l ↦ rv -∗
  l.[raft.raft.t, "msgs"] ↦ rv.(raft.raft.msgs') ∗
  (∀ x, l.[raft.raft.t, "msgs"] ↦ x -∗ l ↦ (rv <| raft.raft.msgs' := x |>)).
Proof. split_field_proof "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hx & Hrest)". Qed.

Local Lemma raft_split_msgsAA (l : loc) (rv : raft.raft.t) :
  l ↦ rv -∗
  l.[raft.raft.t, "msgsAfterAppend"] ↦ rv.(raft.raft.msgsAfterAppend') ∗
  (∀ x, l.[raft.raft.t, "msgsAfterAppend"] ↦ x -∗
        l ↦ (rv <| raft.raft.msgsAfterAppend' := x |>)).
Proof. split_field_proof "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hx & Hrest)". Qed.

Local Lemma raft_split_readOnly (l : loc) (rv : raft.raft.t) :
  l ↦ rv -∗
  l.[raft.raft.t, "readOnly"] ↦ rv.(raft.raft.readOnly') ∗
  (∀ x, l.[raft.raft.t, "readOnly"] ↦ x -∗ l ↦ (rv <| raft.raft.readOnly' := x |>)).
Proof. split_field_proof "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hx & Hrest)". Qed.

(** The tracker, as the tracker's own specs take it: the embedded struct's
    points-to and [own_tracker].  The wand takes it back at any tracker
    value and vote tally, and at the same progress map ([nstate.progress]
    is stable: nothing on the election path inserts into the map).  A map
    lookup [r.trk.Progress[i]] is done on what this hands out, with
    [own_tracker_progress_map] / [wp_tracker_progress_lookup]. *)
Lemma own_raft_phys_tracker r id s :
  s.(nstate.lent) = None →
  own_raft_phys r id s -∗
  ∃ tv, r.[raft.raft.t, "trk"] ↦ tv ∗
        own_tracker cfg tv s.(nstate.votes) s.(nstate.progress) ∗
        (∀ tv' votes', r.[raft.raft.t, "trk"] ↦ tv' -∗
           own_tracker cfg tv' votes' s.(nstate.progress) -∗
           own_raft_phys r id (s <| nstate.votes := votes' |>)).
Proof.
  iIntros (Hlent) "H". iNamed_phys "H".
  iDestruct (own_tracker_unless_open _ _ _ _ Hlent with "Htrk") as "Htrk".
  iDestruct (raft_split_trk with "Hr") as "[Hf Hback]".
  iExists _. iFrame "Hf Htrk".
  iIntros (tv' votes') "Hf Htrk".
  iDestruct ("Hback" $! tv' with "Hf") as "Hr".
  iDestruct (own_tracker_unless_close _ _ _ _ Hlent with "Htrk") as "Htrk".
  reseal.
Qed.

(** The same, put back at the same tally: the wand gives [own_raft_phys] at
    [s] itself rather than at [s <| votes := s.votes |>], so a read-only use
    (a map lookup, [JointConfig.IDs]), or a split and re-seal repeated
    inside a [Visit] closure, does not pile up setters. *)
Lemma own_raft_phys_tracker_same r id s :
  s.(nstate.lent) = None →
  own_raft_phys r id s -∗
  ∃ tv, r.[raft.raft.t, "trk"] ↦ tv ∗
        own_tracker cfg tv s.(nstate.votes) s.(nstate.progress) ∗
        (∀ tvx, r.[raft.raft.t, "trk"] ↦ tvx -∗
           own_tracker cfg tvx s.(nstate.votes) s.(nstate.progress) -∗
           own_raft_phys r id s).
Proof.
  iIntros (Hlent) "Hphys".
  iDestruct (own_raft_phys_tracker _ _ _ Hlent with "Hphys")
    as (tv) "(Htrkf & Htrk & Hback)".
  iExists tv. iFrame "Htrkf Htrk".
  iIntros (tvx) "Htrkf Htrk".
  iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
  iApply (own_raft_phys_eq with "Hphys"). by destruct s.
Qed.

(** The log, at no page. *)
Lemma own_raft_phys_log r id s :
  s.(nstate.lent) = None →
  own_raft_phys r id s -∗
  ∃ ls, ⌜ ls.(logstate.page) = None ⌝ ∗ own_raftLog s.(nstate.log) ls ∗
        (∀ ls', own_raftLog s.(nstate.log) ls' -∗ ⌜ ls'.(logstate.page) = None ⌝ -∗
                own_raft_phys r id s).
Proof.
  iIntros (Hlent) "H". iNamed_phys "H".
  iDestruct (own_raftLog_unless_open _ _ Hlent with "Hlog") as (ls Hls) "Hlog".
  iExists ls. iSplitR; first done. rewrite -Hlogp. iFrame "Hlog".
  iIntros (ls') "Hlog %Hls'".
  iDestruct (own_raftLog_unless_close _ _ _ Hlent with "Hlog [//]") as "Hlog".
  reseal.
Qed.

(** Lend the tracker's heap and the log to the caller ([nstate.lent]).
    The tracker is lent at the value the field holds, which
    [own_raft_phys_trk_lent] reaches while the loan lasts. *)
Lemma own_raft_phys_lend r id s :
  s.(nstate.lent) = None →
  own_raft_phys r id s -∗
  ∃ tv ls, ⌜ ls.(logstate.page) = None ⌝ ∗
           own_tracker cfg tv s.(nstate.votes) s.(nstate.progress) ∗
           own_raftLog s.(nstate.log) ls ∗
           own_raft_phys r id (s <| nstate.lent := Some tv |>).
Proof.
  iIntros (Hlent) "H". iNamed_phys "H".
  iDestruct (own_tracker_unless_open _ _ _ _ Hlent with "Htrk") as "Htrk0".
  iDestruct (own_raftLog_unless_open _ _ Hlent with "Hlog") as (ls Hls) "Hlog0".
  iExists rv.(raft.raft.trk'), ls. iSplitR; first done.
  iFrame "Htrk0". rewrite -Hlogp. iFrame "Hlog0".
  iPoseProof (own_tracker_unless_lent rv.(raft.raft.trk') s.(nstate.votes)
                s.(nstate.progress)) as "Htrk".
  iPoseProof (own_raftLog_unless_lent rv.(raft.raft.trk') rv.(raft.raft.raftLog'))
    as "Hlog".
  reseal.
Qed.

(** End a loan: the tracker comes back at any tally and progress map, the
    log at any state with no page out.  Stated, like
    [own_raft_phys_trk_lent], at the state [own_raft_phys_lend] produces:
    [(s <| lent := x |>).(lent)] does not reduce to [x] for a variable [s]
    (the setter destructures the record), so a premise [s.(lent) = Some tv]
    would need a [destruct s] at every use.  A caller whose state has been
    through a call since the loan began gets it into this form with
    [own_raft_phys_eq] and [by destruct s]. *)
Lemma own_raft_phys_unlend r id s tv votes prs ls :
  ls.(logstate.page) = None →
  own_raft_phys r id (s <| nstate.lent := Some tv |>) -∗
  own_tracker cfg tv votes prs -∗
  own_raftLog s.(nstate.log) ls -∗
  own_raft_phys r id (s <| nstate.lent := None |> <| nstate.votes := votes |>
                        <| nstate.progress := prs |>).
Proof.
  iIntros (Hpg) "H Htrk0 Hlog0". iNamed_phys "H".
  iDestruct (own_tracker_unless_lent_eq with "Htrk") as %Htv.
  iClear "Htrk Hlog".
  rewrite -Htv.
  iDestruct (own_tracker_unless_close None _ _ _ eq_refl with "Htrk0") as "Htrk".
  iAssert (own_raftLog rv.(raft.raft.raftLog') ls) with "[Hlog0]" as "Hlog0".
  { rewrite Hlogp. destruct s. iExact "Hlog0". }
  iDestruct (own_raftLog_unless_close None _ _ eq_refl with "Hlog0 [//]") as "Hlog".
  reseal.
Qed.

(** The tracker field while the tracker is on loan: the loan follows the
    field to whatever value it is given.  Stated at the state
    [own_raft_phys_lend] produces, [s <| lent := Some tv |>], so that
    re-splitting the field after putting it back matches the same [s]
    again instead of stacking setters. *)
Lemma own_raft_phys_trk_lent r id s tv :
  own_raft_phys r id (s <| nstate.lent := Some tv |>) -∗
  r.[raft.raft.t, "trk"] ↦ tv ∗
  (∀ tv', r.[raft.raft.t, "trk"] ↦ tv' -∗
          own_raft_phys r id (s <| nstate.lent := Some tv' |>)).
Proof.
  iIntros "H". iNamed_phys "H".
  iDestruct (own_tracker_unless_lent_eq with "Htrk") as %Htv.
  iDestruct (raft_split_trk with "Hr") as "[Hf Hback]".
  rewrite Htv. iFrame "Hf".
  iIntros (tv') "Hf".
  iDestruct ("Hback" $! tv' with "Hf") as "Hr".
  iClear "Htrk Hlog".
  iPoseProof (own_tracker_unless_lent tv' s.(nstate.votes) s.(nstate.progress))
    as "Htrk".
  iPoseProof (own_raftLog_unless_lent tv' rv.(raft.raft.raftLog')) as "Hlog".
  reseal.
Qed.

(** [r.msgs], append-only: whatever is appended joins the abstract outbox
    (at the end, up to permutation -- see [Houtbox]); a message type the
    model does not describe drops out through [abs_msg_opt]. *)
Lemma own_raft_phys_msgs r id s :
  own_raft_phys r id s -∗
  ∃ sl ms, r.[raft.raft.t, "msgs"] ↦ sl ∗ sl ↦* ms ∗
           own_slice_cap raftpb.Message.t sl (DfracOwn 1) ∗
           (∀ sl' ms', r.[raft.raft.t, "msgs"] ↦ sl' -∗ sl' ↦* (ms ++ ms') -∗
              own_slice_cap raftpb.Message.t sl' (DfracOwn 1) -∗
              own_raft_phys r id
                (s <| nstate.outbox := s.(nstate.outbox) ++ omap abs_msg_opt ms' |>)).
Proof.
  iIntros "H". iNamed_phys "H".
  iDestruct (raft_split_msgs with "Hr") as "[Hf Hback]".
  iExists _, msgs. iFrame "Hf Hmsgs Hmsgs_cap".
  iIntros (sl' ms') "Hf Hmsgs Hmsgs_cap".
  iDestruct ("Hback" $! sl' with "Hf") as "Hr".
  reseal.
  change (s.(nstate.outbox) ++ omap abs_msg_opt ms' ≡ₚ abs_outbox (msgs ++ ms') msgsAA).
  rewrite Houtbox /abs_outbox omap_app -!assoc.
  apply Permutation_app_head, Permutation_app_comm.
Qed.

(** [r.msgsAfterAppend], likewise. *)
Lemma own_raft_phys_msgsAA r id s :
  own_raft_phys r id s -∗
  ∃ sl ms, r.[raft.raft.t, "msgsAfterAppend"] ↦ sl ∗ sl ↦* ms ∗
           own_slice_cap raftpb.Message.t sl (DfracOwn 1) ∗
           (∀ sl' ms', r.[raft.raft.t, "msgsAfterAppend"] ↦ sl' -∗
              sl' ↦* (ms ++ ms') -∗
              own_slice_cap raftpb.Message.t sl' (DfracOwn 1) -∗
              own_raft_phys r id
                (s <| nstate.outbox := s.(nstate.outbox) ++ omap abs_msg_opt ms' |>)).
Proof.
  iIntros "H". iNamed_phys "H".
  iDestruct (raft_split_msgsAA with "Hr") as "[Hf Hback]".
  iExists _, msgsAA. iFrame "Hf HmsgsAA HmsgsAA_cap".
  iIntros (sl' ms') "Hf HmsgsAA HmsgsAA_cap".
  iDestruct ("Hback" $! sl' with "Hf") as "Hr".
  reseal.
  change (s.(nstate.outbox) ++ omap abs_msg_opt ms' ≡ₚ abs_outbox msgs (msgsAA ++ ms')).
  rewrite Houtbox /abs_outbox omap_app -!assoc //.
Qed.

(** The [readOnly] object.  Election never reads it; [reset] replaces it. *)
Lemma own_raft_phys_readOnly r id s :
  own_raft_phys r id s -∗
  ∃ ro, r.[raft.raft.t, "readOnly"] ↦ ro ∗ own_read_only ro ∗
        (∀ ro', r.[raft.raft.t, "readOnly"] ↦ ro' -∗ own_read_only ro' -∗
                own_raft_phys r id s).
Proof.
  iIntros "H". iNamed_phys "H". iNamed "Hmisc".
  iDestruct (raft_split_readOnly with "Hr") as "[Hf Hback]".
  iExists _. iFrame "Hf Hro_obj".
  iIntros (ro') "Hf Hro_obj".
  iDestruct ("Hback" $! ro' with "Hf") as "Hr".
  iAssert (own_raft_misc _ ro' _)
    with "[HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap]" as "Hmisc".
  { rewrite /own_raft_misc. iFrame. }
  reseal.
Qed.


End proof.

(** One raft-field access with nothing to name: a load of a field whose
    value the state determines, or a store.  Works on the hypothesis
    ["Hphys"] and gives it back under the same name.  The accesses with
    outputs -- [logger], the untracked loads -- and the accessors are
    applied by hand. *)
Ltac wp_raft_field :=
  first
  [ wp_apply (wp_raft_load_id with "Hphys") as "Hphys"
  | wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"
  | wp_apply (wp_raft_load_Vote with "Hphys") as "Hphys"
  | wp_apply (wp_raft_load_lead with "Hphys") as "Hphys"
  | wp_apply (wp_raft_load_state with "Hphys") as "Hphys"
  | wp_apply (wp_raft_load_step with "Hphys") as "Hphys"
  | wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys"
  | wp_apply (wp_raft_load_checkQuorum with "Hphys") as "Hphys"
  | wp_apply (wp_raft_load_preVote with "Hphys") as "Hphys"
  | wp_apply (wp_raft_load_isLearner with "Hphys") as "Hphys"
  | wp_apply (wp_raft_load_leadTransferee with "Hphys") as "Hphys"
  | wp_apply (wp_raft_store_Term with "Hphys") as "Hphys"
  | wp_apply (wp_raft_store_Vote with "Hphys") as "Hphys"
  | wp_apply (wp_raft_store_lead with "Hphys") as "Hphys"
  | wp_apply (wp_raft_store_state _ _ _ _ role.Follower with "Hphys") as "Hphys"
  | wp_apply (wp_raft_store_state _ _ _ _ role.Candidate with "Hphys") as "Hphys"
  | wp_apply (wp_raft_store_state _ _ _ _ role.Leader with "Hphys") as "Hphys"
  | wp_apply (wp_raft_store_step with "Hphys") as "Hphys"
  | wp_apply (wp_raft_store_tick with "Hphys") as "Hphys"
  | wp_apply (wp_raft_store_electionElapsed with "Hphys") as "Hphys"
  | wp_apply (wp_raft_store_heartbeatElapsed with "Hphys") as "Hphys"
  | wp_apply (wp_raft_store_randomizedElectionTimeout with "Hphys") as "Hphys"
  | wp_apply (wp_raft_store_pendingConfIndex with "Hphys") as "Hphys"
  | wp_apply (wp_raft_store_uncommittedSize with "Hphys") as "Hphys"
  | wp_apply (wp_raft_store_leadTransferee with "Hphys") as "Hphys" ].

(** A logging call through [r.logger]: the raft fields its arguments read,
    the variadic argument slice, the load of [r.logger], and the logger
    spec.  Works on ["Hphys"], like [wp_raft_field]. *)
Ltac wp_raft_log :=
  repeat wp_raft_field;
  wp_apply wp_slice_literal;
  (* depending on the arguments, [wp_apply] may already have discharged the
     precondition and introduced the slice *)
  try (iSplitR; [ done | ]); try iIntros "% [? _]"; try wp_auto;
  let lk := fresh "lok" in
  wp_apply (wp_raft_load_logger with "Hphys") as (lk) "[Hphys #Hlg]";
  wp_apply (wp_Logger__logf with "Hlg");
  [ solve_log_method | try iIntros "_"; iClear "Hlg"; try wp_auto ].
