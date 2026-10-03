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

(** ** The abstract outbox of the two queues

    [msg_abs m a]: the queued physical message [m] contributes [a] to the
    abstract outbox -- [None] for a type the model does not describe
    ([mtype_of = None]: [MsgHup], [MsgCheckQuorum], ...), else
    [abs_msg ty m ents] where [ents] is what [m.Entries] points to, held
    read-only.  The points-to is what makes the abstraction a function of
    the heap rather than of [m] alone: [m.Entries] is a slice
    ([notes/raft-replication-model.md], "Abstract messages").

    A [MsgSnap] is abstracted by [abs_snap m sv voters] instead (since
    2026-10-02), the snapshot's metadata.  **Not yet tied to the heap**:
    [sv]/[voters] should be what [m.Snapshot ↦□ sv] and [sv]'s
    [ConfState.Voters ↦*□ voters] say, but [send] -- the only producer of
    a [msg_abs] -- has no such precondition (adding one changes every
    caller's proof), and [maybeSendSnapshot] could not supply the voters'
    points-to anyway ([raftLog.snapshot]/[is_Storage]'s [HSnapshot] give no
    ownership of them).  So today a queued [MsgSnap]'s metadata is whatever
    its sender's spec says it is ([maybeSendSnapshot]: the [Storage]'s
    snapshot), and nothing in [own_raft_phys] re-reads it.  The receiving
    side, [Step]'s ["Hsnap"], does hold the points-tos.

    [outbox_rel o msgs msgsAA]: the abstract outbox [o] is, up to
    permutation, what the two queues contribute.  Persistent. *)
Definition msg_abs (m : raftpb.Message.t) (a : option msg.t) : iProp Σ :=
  (⌜ mtype_of m.(raftpb.Message.Type') = None ∧ a = None ⌝) ∨
  (∃ ty ents, ⌜ mtype_of m.(raftpb.Message.Type') = Some ty ∧ ty ≠ mtype.Snap ∧
                a = Some (abs_msg ty m ents) ⌝ ∗
              m.(raftpb.Message.Entries') ↦*□ ents) ∨
  (⌜ mtype_of m.(raftpb.Message.Type') = Some mtype.Snap ∧
     ∃ (sv : raftpb.Snapshot.t) (voters : list w64),
       a = Some (abs_snap m sv voters) ⌝).

Definition abs_list (as_ : list (option msg.t)) : list msg.t := omap (λ a, a) as_.

Definition outbox_rel (o : list msg.t) (msgs msgsAA : list raftpb.Message.t) : iProp Σ :=
  ∃ (as1 as2 : list (option msg.t)),
    ⌜ o ≡ₚ abs_list as1 ++ abs_list as2 ⌝ ∗
    ([∗ list] m; a ∈ msgs; as1, msg_abs m a) ∗
    ([∗ list] m; a ∈ msgsAA; as2, msg_abs m a).

Global Instance msg_abs_pers m a : Persistent (msg_abs m a).
Proof. apply _. Qed.
Global Instance outbox_rel_pers o msgs msgsAA : Persistent (outbox_rel o msgs msgsAA).
Proof. apply _. Qed.

Lemma outbox_rel_nil : ⊢ outbox_rel [] [] [].
Proof. iExists [], []. rewrite !big_sepL2_nil. done. Qed.

Lemma outbox_rel_perm o o' msgs msgsAA :
  o' ≡ₚ o → outbox_rel o msgs msgsAA -∗ outbox_rel o' msgs msgsAA.
Proof.
  iIntros (Hp) "(%as1 & %as2 & %Ho & H1 & H2)". iExists as1, as2. iFrame.
  iPureIntro. by rewrite Hp.
Qed.

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
      by [s.(nstate.progress)] and [s.(nstate.prvals)]: that is what lets
      a proof know *which* [Progress] a peer has, and what it holds, after
      a call it made with the struct sealed.  (Until 2026-09-29 the
      values were existential, and a proof that needed one across a call
      took the tracker out of the predicate on loan, [nstate.lent].)
      (From 2026-09-22 to 2026-09-23 a second, persistent copy of the
      progress map's points-to sat here, beside the one inside
      [own_tracker]; indexing [own_tracker] by the map made it redundant.) *)
  "Htrk" ∷ own_tracker cfg rv.(raft.raft.trk')
             {| trk.votes := s.(nstate.votes); trk.prs := s.(nstate.progress);
                trk.peers := s.(nstate.prvals) |} ∗

  (** the log, at the state [s] records ([nstate.logst]).  Never on loan:
      what [raftLog.slice] returns is read-only and the caller's for good.
      (Until 2026-09-28 the log's state was quantified here, and the log
      went on loan with the tracker; until 2026-09-29 a slice [raftLog.slice]
      lent out was recorded in [logst.page].) *)
  "%Hlogp" ∷ ⌜ rv.(raft.raft.raftLog') = s.(nstate.log) ⌝ ∗
  "Hlog" ∷ own_raftLog rv.(raft.raft.raftLog') s.(nstate.logst) ∗

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
  "#Houtbox" ∷ outbox_rel s.(nstate.outbox) msgs msgsAA ∗

  (** scope assumptions *)
  "%HnoPreVote" ∷ ⌜ rv.(raft.raft.preVote') = false ⌝ ∗
  (** [Config.DisableProposalForwarding] is [false] ([newRaft]'s premise):
      a follower forwards a proposal to the leader it knows.  Never
      written after [newRaft].  Added 2026-10-02. *)
  "%HpropForward" ∷ ⌜ rv.(raft.raft.disableProposalForwarding') = false ⌝ ∗
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
        "Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox"); done.

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
  rv.(raft.raft.preVote') = false →
  rv.(raft.raft.disableProposalForwarding') = false →
  rv.(raft.raft.checkQuorum') = false →
  rv.(raft.raft.isLearner') = false →
  rv.(raft.raft.leadTransferee') = W64 0 →
  id ≠ W64 0 →
  0 < sint.Z rv.(raft.raft.electionTimeout') →
  rv.(raft.raft.logger') = interface.ok lok →
  rv.(raft.raft.raftLog') = s.(nstate.log) →
  r ↦ rv -∗
  is_Logger lok -∗
  own_tracker cfg rv.(raft.raft.trk')
    {| trk.votes := s.(nstate.votes); trk.prs := s.(nstate.progress);
       trk.peers := s.(nstate.prvals) |} -∗
  own_raftLog rv.(raft.raft.raftLog') s.(nstate.logst) -∗
  rv.(raft.raft.msgs') ↦* msgs -∗
  own_slice_cap raftpb.Message.t rv.(raft.raft.msgs') (DfracOwn 1) -∗
  rv.(raft.raft.msgsAfterAppend') ↦* msgsAA -∗
  own_slice_cap raftpb.Message.t rv.(raft.raft.msgsAfterAppend') (DfracOwn 1) -∗
  own_raft_misc rv.(raft.raft.readStates') rv.(raft.raft.readOnly')
    rv.(raft.raft.pendingReadIndexMessages') -∗
  outbox_rel s.(nstate.outbox) msgs msgsAA -∗
  own_raft_phys r id s.
Proof.
  intros Hid Hterm Hvote Hlead Hstate Hstepfn HnoPreVote HpropForward HnoCheckQuorum
    HnoLearner HnoTransfer Hid_nz HelectionTimeout Hlok Hlogp.
  iIntros "Hr #Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc #Houtbox".
  rewrite own_raft_phys_unseal /own_raft_phys_def. iExists rv, msgs, msgsAA, lok.
  (* [Hlog] before [Hlogger]: framing [Hlogger] first would also frame it
     inside the unfolded [own_raftLog]'s logger conjuncts *)
  iFrame "Hr Hlog Htrk Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox Hlogger".
  iPureIntro. split_and!; done.
Qed.

(** The progress map in [s] is the tracker's, and so has domain [cfg].  Read
    out without consuming anything. *)
Lemma own_raft_phys_progress_dom r id s :
  own_raft_phys r id s -∗ ⌜ dom s.(nstate.progress) = cfg ⌝ ∗ own_raft_phys r id s.
Proof.
  iIntros "H". iNamed_phys "H".
  iDestruct (own_tracker_progress_map with "Htrk") as "(#Hprs & %Hdom & Htrk)".
  iSplitR; first done.
  iApply (own_raft_phys_intro _ _ s with
    "Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox"); done.
Qed.

(** Changing only the outbox, up to permutation. *)
Lemma own_raft_phys_outbox r id s (o : list msg.t) :
  o ≡ₚ s.(nstate.outbox) →
  own_raft_phys r id s -∗ own_raft_phys r id (s <| nstate.outbox := o |>).
Proof.
  iIntros (Ho) "H". iNamed_phys "H".
  iDestruct (outbox_rel_perm _ o with "Houtbox") as "#Houtbox'"; first done.
  iApply (own_raft_phys_intro _ _ (s <| nstate.outbox := o |>) with
    "Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox'"); done.
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
    proof continues with the lemma for that field, named explicitly:
    [wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"].  There is
    deliberately no tactic that searches the lemmas for the one that
    applies: each failed [wp_apply] walks the whole program, and a proof
    that names its lemma says which field it touches.

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
    Nothing is ever lent out of the predicate: an accessor's wand is the
    only way to hold part of the struct across a step, and a call on the
    struct needs the predicate whole.  (Until 2026-09-29 there were loans,
    [own_raft_phys_lend] / [own_raft_phys_unlend], which moved the
    tracker's heap out of the predicate for the length of a function body;
    [nstate.lent].) *)

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
        "Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox");
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

Lemma wp_raft_load_disableProposalForwarding r id s :
  {{{ own_raft_phys r id s }}}
    ![go.bool] #(r.[raft.raft.t, "disableProposalForwarding"])
  {{{ RET #false; own_raft_phys r id s }}}.
Proof. load_proof. rewrite HpropForward. iApply "HΦ". reseal. Qed.

(** [r.pendingReadIndexMessages], at a slice of length [0] ([own_raft_misc]
    holds it at the empty list).  Moved here from
    [proof_releasePendingReadIndexMessages.v] on 2026-10-02. *)
Lemma wp_raft_load_pendingReadIndexMessages r id s :
  {{{ own_raft_phys r id s }}}
    ![go.SliceType raftpb.Message] #(r.[raft.raft.t, "pendingReadIndexMessages"])
  {{{ (sl : slice.t), RET #sl; own_raft_phys r id s ∗ ⌜ sl.(slice.len) = W64 0 ⌝ }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed_phys "H".
  iNamed "Hmisc".
  iDestruct (own_slice_len with "Hpri") as %[Hl Hl0].
  wp_apply (wp_load_access with "Hr") as "Hr".
  iApply "HΦ". iSplitL; last (iPureIntro; simpl in Hl; word).
  iAssert (own_raft_misc rv.(raft.raft.readStates') rv.(raft.raft.readOnly')
             rv.(raft.raft.pendingReadIndexMessages'))
    with "[HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap]" as "Hmisc".
  { rewrite /own_raft_misc. iFrame. }
  reseal.
Qed.

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

(** Only [false]: no learners are in scope.  [switchToConfig] stores
    [ok && pr.IsLearner], which is [false] for every voter's [Progress]. *)
Lemma wp_raft_store_isLearner r id s :
  {{{ own_raft_phys r id s }}}
    GoStore go.bool (#(r.[raft.raft.t, "isLearner"]), #false)%V
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

(** Two fields at once, [raftLog] (read-only here) and [trk]: for
    [own_raft_phys_retrack]. *)
Local Lemma raft_split_raftLog_trk (l : loc) (rv : raft.raft.t) :
  l ↦ rv -∗
  l.[raft.raft.t, "raftLog"] ↦ rv.(raft.raft.raftLog') ∗
  l.[raft.raft.t, "trk"] ↦ rv.(raft.raft.trk') ∗
  (∀ x, l.[raft.raft.t, "raftLog"] ↦ rv.(raft.raft.raftLog') -∗
        l.[raft.raft.t, "trk"] ↦ x -∗ l ↦ (rv <| raft.raft.trk' := x |>)).
Proof.
  iIntros "Hr".
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=) in "Hr".
  iDestruct "Hr" as "[Hf %Hnn]".
  iDestruct "Hf" as "(? & ? & ? & ? & Hy & ? & ? & Hx & Hrest)".
  iFrame "Hx Hy". iIntros (x) "Hy Hx".
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=).
  iFrame. done.
Qed.

(** The tracker, as the tracker's own specs take it: the embedded struct's
    points-to and [own_tracker].  The wand takes it back at any tracker
    value and vote tally, and at the same progress map and [Progress]
    values ([nstate.progress] is stable: nothing on the election path
    inserts into the map).  A map lookup [r.trk.Progress[i]] is done on
    what this hands out, with [own_tracker_progress_map] /
    [wp_tracker_progress_lookup]; a function that changes a [Progress]
    uses [own_raft_phys_tracker_prvals]. *)
Lemma own_raft_phys_tracker r id s :
  own_raft_phys r id s -∗
  ∃ tv, r.[raft.raft.t, "trk"] ↦ tv ∗
        own_tracker cfg tv (trk.mk s.(nstate.votes) s.(nstate.progress) s.(nstate.prvals)) ∗
        (∀ tv' votes', r.[raft.raft.t, "trk"] ↦ tv' -∗
           own_tracker cfg tv' (trk.mk votes' s.(nstate.progress) s.(nstate.prvals)) -∗
           own_raft_phys r id (s <| nstate.votes := votes' |>)).
Proof.
  iIntros "H". iNamed_phys "H".
  iDestruct (raft_split_trk with "Hr") as "[Hf Hback]".
  iExists _. iFrame "Hf Htrk".
  iIntros (tv' votes') "Hf Htrk".
  iDestruct ("Hback" $! tv' with "Hf") as "Hr".
  reseal.
Qed.

(** The same, put back at the same tally: the wand gives [own_raft_phys] at
    [s] itself rather than at [s <| votes := s.votes |>], so a read-only use
    (a map lookup, [JointConfig.IDs]), or a split and re-seal repeated
    inside a [Visit] closure, does not pile up setters. *)
Lemma own_raft_phys_tracker_same r id s :
  own_raft_phys r id s -∗
  ∃ tv, r.[raft.raft.t, "trk"] ↦ tv ∗
        own_tracker cfg tv (trk.mk s.(nstate.votes) s.(nstate.progress) s.(nstate.prvals)) ∗
        (∀ tvx, r.[raft.raft.t, "trk"] ↦ tvx -∗
           own_tracker cfg tvx (trk.mk s.(nstate.votes) s.(nstate.progress) s.(nstate.prvals)) -∗
           own_raft_phys r id s).
Proof.
  iIntros "Hphys".
  iDestruct (own_raft_phys_tracker with "Hphys")
    as (tv) "(Htrkf & Htrk & Hback)".
  iExists tv. iFrame "Htrkf Htrk".
  iIntros (tvx) "Htrkf Htrk".
  iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
  iApply (own_raft_phys_eq with "Hphys"). by destruct s.
Qed.

(** The tracker, put back with new [Progress] values (at the same tally):
    for a function that writes a [Progress] -- [reset]'s [Visit] closure,
    [becomeLeader]'s [RecentActive] and [BecomeReplicate], [SentEntries]. *)
Lemma own_raft_phys_tracker_prvals r id s :
  own_raft_phys r id s -∗
  ∃ tv, r.[raft.raft.t, "trk"] ↦ tv ∗
        own_tracker cfg tv (trk.mk s.(nstate.votes) s.(nstate.progress) s.(nstate.prvals)) ∗
        (∀ tv' pvs', r.[raft.raft.t, "trk"] ↦ tv' -∗
           own_tracker cfg tv' (trk.mk s.(nstate.votes) s.(nstate.progress) pvs') -∗
           own_raft_phys r id (s <| nstate.prvals := pvs' |>)).
Proof.
  iIntros "H". iNamed_phys "H".
  iDestruct (raft_split_trk with "Hr") as "[Hf Hback]".
  iExists _. iFrame "Hf Htrk".
  iIntros (tv' pvs') "Hf Htrk".
  iDestruct ("Hback" $! tv' with "Hf") as "Hr".
  reseal.
Qed.

(** One peer's [Progress], borrowed out of the struct by its key at the
    value [nstate.prvals] records, and given back at that value -- for a
    read ([IsPaused], field loads, [Inflights.Full]).  The lookup of
    [r.trk.Progress[to]] itself goes through [own_raft_phys_tracker_same]:
    it reads the tracker field.  The two
    lookups are premises inside the logic, so that [s] is fixed by the
    struct hypothesis the lemma is applied to, not by the lookups' types:
    [iDestruct (own_raft_phys_pr with "Hphys [//] [//]")]. *)
Lemma own_raft_phys_pr r id s to pr p :
  own_raft_phys r id s -∗
  ⌜ s.(nstate.progress) !! to = Some pr ⌝ -∗
  ⌜ s.(nstate.prvals) !! to = Some p ⌝ -∗
  own_Progress pr p ∗ (own_Progress pr p -∗ own_raft_phys r id s).
Proof.
  iIntros "Hphys %Hlk %Hv".
  iDestruct (own_raft_phys_tracker_same with "Hphys") as (tv) "(Htrkf & Htrk & Hback)".
  iDestruct (own_tracker_lookup_same _ _ (trk.mk _ _ _) _ _ Hlk with "Htrk")
    as (p' Hv') "[Hp Hpb]".
  simpl in Hv'. rewrite Hv in Hv'. simplify_eq.
  iFrame "Hp". iIntros "Hp". iApply ("Hback" with "Htrkf"). iApply ("Hpb" with "Hp").
Qed.

(** The same, given back at new values, which the state then records --
    for a write ([SentEntries]). *)
Lemma own_raft_phys_pr_upd r id s to pr p :
  own_raft_phys r id s -∗
  ⌜ s.(nstate.progress) !! to = Some pr ⌝ -∗
  ⌜ s.(nstate.prvals) !! to = Some p ⌝ -∗
  own_Progress pr p ∗
  (∀ p', own_Progress pr p' -∗
     own_raft_phys r id (s <| nstate.prvals := <[to := p']> s.(nstate.prvals) |>)).
Proof.
  iIntros "Hphys %Hlk %Hv".
  iDestruct (own_raft_phys_tracker_prvals with "Hphys") as (tv) "(Htrkf & Htrk & Hback)".
  iDestruct (own_tracker_lookup _ _ (trk.mk _ _ _) _ _ Hlk with "Htrk")
    as (p' Hv') "[Hp Hpb]".
  simpl in Hv'. rewrite Hv in Hv'. simplify_eq.
  iFrame "Hp". iIntros (p'') "Hp". iApply ("Hback" with "Htrkf"). iApply ("Hpb" with "Hp").
Qed.

(** A write that does not need to know the value it overwrites
    ([SentCommit]). *)
Lemma own_raft_phys_pr_any r id s to pr :
  own_raft_phys r id s -∗
  ⌜ s.(nstate.progress) !! to = Some pr ⌝ -∗
  ∃ p, own_Progress pr p ∗
  (∀ p', own_Progress pr p' -∗
     own_raft_phys r id (s <| nstate.prvals := <[to := p']> s.(nstate.prvals) |>)).
Proof.
  iIntros "Hphys %Hlk".
  iDestruct (own_raft_phys_tracker_prvals with "Hphys") as (tv) "(Htrkf & Htrk & Hback)".
  iDestruct (own_tracker_lookup _ _ (trk.mk _ _ _) _ _ Hlk with "Htrk")
    as (p' Hv') "[Hp Hpb]".
  iExists p'. iFrame "Hp". iIntros (p'') "Hp".
  iApply ("Hback" with "Htrkf"). iApply ("Hpb" with "Hp").
Qed.

(** The log, at the state [s] records, put back at any state.  This is the
    accessor for a function that changes the log ([appendEntry]'s [append],
    [loadState]'s [committed], [newRaft]'s [appliedTo]). *)
Lemma own_raft_phys_log_at r id s :
  own_raft_phys r id s -∗
  own_raftLog s.(nstate.log) s.(nstate.logst) ∗
  (∀ ls', own_raftLog s.(nstate.log) ls' -∗
          own_raft_phys r id (s <| nstate.logst := ls' |>)).
Proof.
  iIntros "H". iNamed_phys "H".
  rewrite -Hlogp. iFrame "Hlog".
  iIntros (ls') "Hlog".
  reseal.
Qed.

(** The log at the state [s] records, put back at that same state: for a
    read through [own_raftLog] (a [raftLog] method that keeps its state, a
    field load through [own_raftLog_struct]).
    The wand gives [own_raft_phys] at [s] itself, so no [own_raft_phys_eq]
    is needed afterwards. *)
Lemma own_raft_phys_log_same r id s :
  own_raft_phys r id s -∗
  own_raftLog s.(nstate.log) s.(nstate.logst) ∗
  (own_raftLog s.(nstate.log) s.(nstate.logst) -∗ own_raft_phys r id s).
Proof.
  iIntros "H".
  iDestruct (own_raft_phys_log_at with "H") as "[Hlog Hback]".
  iFrame "Hlog". iIntros "Hlog".
  iDestruct ("Hback" with "Hlog") as "H".
  iApply (own_raft_phys_eq with "H"). by destruct s.
Qed.

(** [r.msgs], append-only: a message [m'] appended joins the abstract
    outbox (at the end, up to permutation -- see [Houtbox]) as whatever
    [msg_abs] says it contributes: nothing for a type the model does not
    describe, else its abstraction, given [m'.Entries ↦*□ ents]. *)
Lemma own_raft_phys_msgs r id s :
  own_raft_phys r id s -∗
  ∃ sl ms, r.[raft.raft.t, "msgs"] ↦ sl ∗ sl ↦* ms ∗
           own_slice_cap raftpb.Message.t sl (DfracOwn 1) ∗
           (∀ sl' m' a, r.[raft.raft.t, "msgs"] ↦ sl' -∗ sl' ↦* (ms ++ [m']) -∗
              own_slice_cap raftpb.Message.t sl' (DfracOwn 1) -∗
              msg_abs m' a -∗
              own_raft_phys r id
                (s <| nstate.outbox := s.(nstate.outbox) ++ abs_list [a] |>)).
Proof.
  iIntros "H". iNamed_phys "H".
  iDestruct (raft_split_msgs with "Hr") as "[Hf Hback]".
  iExists _, msgs. iFrame "Hf Hmsgs Hmsgs_cap".
  iIntros (sl' m' a) "Hf Hmsgs Hmsgs_cap #Ha".
  iDestruct ("Hback" $! sl' with "Hf") as "Hr".
  iDestruct "Houtbox" as (as1 as2 Ho) "[#H1 #H2]".
  iAssert (outbox_rel (s.(nstate.outbox) ++ abs_list [a]) (msgs ++ [m']) msgsAA)
    as "#Houtbox".
  { iExists (as1 ++ [a]), as2. iSplit.
    - iPureIntro. rewrite Ho /abs_list omap_app -!assoc.
      apply Permutation_app_head, Permutation_app_comm.
    - iSplit; last done. iApply big_sepL2_app; first done.
      rewrite big_sepL2_singleton. done. }
  reseal.
Qed.

(** [r.msgsAfterAppend], likewise. *)
Lemma own_raft_phys_msgsAA r id s :
  own_raft_phys r id s -∗
  ∃ sl ms, r.[raft.raft.t, "msgsAfterAppend"] ↦ sl ∗ sl ↦* ms ∗
           own_slice_cap raftpb.Message.t sl (DfracOwn 1) ∗
           (∀ sl' m' a, r.[raft.raft.t, "msgsAfterAppend"] ↦ sl' -∗
              sl' ↦* (ms ++ [m']) -∗
              own_slice_cap raftpb.Message.t sl' (DfracOwn 1) -∗
              msg_abs m' a -∗
              own_raft_phys r id
                (s <| nstate.outbox := s.(nstate.outbox) ++ abs_list [a] |>)).
Proof.
  iIntros "H". iNamed_phys "H".
  iDestruct (raft_split_msgsAA with "Hr") as "[Hf Hback]".
  iExists _, msgsAA. iFrame "Hf HmsgsAA HmsgsAA_cap".
  iIntros (sl' m' a) "Hf HmsgsAA HmsgsAA_cap #Ha".
  iDestruct ("Hback" $! sl' with "Hf") as "Hr".
  iDestruct "Houtbox" as (as1 as2 Ho) "[#H1 #H2]".
  iAssert (outbox_rel (s.(nstate.outbox) ++ abs_list [a]) msgs (msgsAA ++ [m']))
    as "#Houtbox".
  { iExists as1, (as2 ++ [a]). iSplit.
    - iPureIntro. rewrite Ho /abs_list omap_app -!assoc //.
    - iSplit; first done. iApply big_sepL2_app; first done.
      rewrite big_sepL2_singleton. done. }
  reseal.
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

(** *** Reconfiguration

    The one accessor that changes [own_raft_phys]'s [cfg] index: the
    tracker comes out at the old configuration and goes back at a new one,
    with a new progress map ([nstate.progress]).  Only [own_tracker]
    mentions [cfg], so nothing else is re-established.  [switchToConfig]
    is the one user (for [newRaft]'s move from the empty configuration to
    the persisted one). *)
Section reconfig.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Lemma own_raft_phys_reconfig cfg0 cfg r id s :
  own_raft_phys cfg0 r id s -∗
  ∃ tv, r.[raft.raft.t, "trk"] ↦ tv ∗
        own_tracker cfg0 tv (trk.mk s.(nstate.votes) s.(nstate.progress) s.(nstate.prvals)) ∗
        (∀ tv' prs' pvs', r.[raft.raft.t, "trk"] ↦ tv' -∗
           own_tracker cfg tv' (trk.mk s.(nstate.votes) prs' pvs') -∗
           own_raft_phys cfg r id (s <| nstate.progress := prs' |> <| nstate.prvals := pvs' |>)).
Proof.
  iIntros "H".
  iEval (rewrite own_raft_phys_unseal) in "H". iNamed "H".
  iDestruct (raft_split_trk with "Hr") as "[Hf Hback]".
  iExists _. iFrame "Hf Htrk".
  iIntros (tv' prs' pvs') "Hf Htrk".
  iDestruct ("Hback" $! tv' with "Hf") as "Hr".
  iApply (own_raft_phys_intro cfg r id (s <| nstate.progress := prs' |> <| nstate.prvals := pvs' |>) with
    "Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox"); try done.
Qed.

(** The tracker replaced while the log is in use (2026-10-02): [restore]
    stores a fresh tracker into [r.trk], loads it back, calls
    [r.raftLog.lastIndex()] and only then hands the new tracker's (empty)
    voter map to [confchange.Restore] -- so between the store and that call
    the struct cannot be re-sealed without losing which tracker value it
    holds.  This accessor hands out the tracker field and the [raftLog]
    field (read-only: its value is [s.log]) together with the log, and
    takes them back at any tracker -- a new configuration [cfg], tally,
    progress map and values -- and any log state. *)
Lemma own_raft_phys_retrack cfg0 cfg r id s :
  own_raft_phys cfg0 r id s -∗
  ∃ tv, r.[raft.raft.t, "trk"] ↦ tv ∗
        own_tracker cfg0 tv (trk.mk s.(nstate.votes) s.(nstate.progress) s.(nstate.prvals)) ∗
        r.[raft.raft.t, "raftLog"] ↦ s.(nstate.log) ∗
        own_raftLog s.(nstate.log) s.(nstate.logst) ∗
        (∀ tv' votes' prs' pvs' ls',
           r.[raft.raft.t, "raftLog"] ↦ s.(nstate.log) -∗
           r.[raft.raft.t, "trk"] ↦ tv' -∗
           own_tracker cfg tv' (trk.mk votes' prs' pvs') -∗
           own_raftLog s.(nstate.log) ls' -∗
           own_raft_phys cfg r id (s <| nstate.votes := votes' |> <| nstate.progress := prs' |>
                                    <| nstate.prvals := pvs' |> <| nstate.logst := ls' |>)).
Proof.
  iIntros "H".
  iEval (rewrite own_raft_phys_unseal) in "H". iNamed "H".
  iDestruct (raft_split_raftLog_trk with "Hr") as "(Hlf & Hf & Hback)".
  iExists _. iFrame "Hf Htrk". rewrite -Hlogp. iFrame "Hlf Hlog".
  iIntros (tv' votes' prs' pvs' ls') "Hlf Hf Htrk Hlog".
  iDestruct ("Hback" $! tv' with "Hlf Hf") as "Hr".
  iApply (own_raft_phys_intro cfg r id
            (s <| nstate.votes := votes' |> <| nstate.progress := prs' |>
               <| nstate.prvals := pvs' |> <| nstate.logst := ls' |>) with
    "Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox"); try done.
Qed.

End reconfig.

(** A logging call through [r.logger], once the raft fields its arguments
    read have been loaded (each with its own lemma, by the caller): the
    variadic argument slice, the load of [r.logger], and the logger spec.
    Works on ["Hphys"].  A fixed sequence of steps, no search: it applies
    the same lemmas in the same order every time. *)
Ltac wp_raft_log :=
  wp_apply wp_slice_literal;
  (* depending on the arguments, [wp_apply] may already have discharged the
     precondition and introduced the slice *)
  try (iSplitR; [ done | ]); try iIntros "% [? _]"; try wp_auto;
  let lk := fresh "lok" in
  wp_apply (wp_raft_load_logger with "Hphys") as (lk) "[Hphys #Hlg]";
  wp_apply (wp_Logger__logf with "Hlg");
  [ solve_log_method | try iIntros "_"; iClear "Hlg"; try wp_auto ].
