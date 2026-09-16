(** * Raft components election neither reads nor writes *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raftlog.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_tracker.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** The (fixed) set of voters. *)
Context (cfg : gset w64).

(** [r.promotable()]: true exactly when this node is a voter.  It reads
    [r.id], [r.trk.Progress] and [r.raftLog], so it is stated against the
    raft struct rather than against three unrelated parameters.

    **In scope and unfinished** (2026-09-16).  The generated body
    ([new/code/go_etcd_io/raft/v3.v:5146]) is

        pr := r.trk.Progress[r.id]
        return pr != nil && !pr.IsLearner &&
               !r.raftLog.hasNextOrInProgressSnapshot()

    so there are *two* obstacles, and only one of them is the log:

    - [hasNextOrInProgressSnapshot] needs [own_raftLog] opened up, and
      [own_raftLog] is still an [Axiom] in [inv_raftlog.v].  (Note for
      whoever builds it: a [wp_raftLog__hasNextOrInProgressSnapshot] lemma
      has to exist again; it was deleted on 2026-09-16 as unreachable, which
      was true only *because* this spec was an axiom.)
    - [own_progress] ([inv_tracker.v]) does not record
      [pv.(tracker.Progress.IsLearner') = false].  Without it the
      postcondition as stated is **not derivable**: a voter whose [Progress]
      had [IsLearner = true] would make [promotable] return [false] while
      [id ∈ cfg].  The fact is true under our scope ([own_raft_phys] carries
      [HnoLearner], [own_tracker] carries [learners = ∅ ∧ learnersNext = ∅]);
      it was simply never written down.  It is being added to
      [own_progress].

    So the log is *necessary but not sufficient* here.  The statement is
    correct as written once both gaps are closed; do not weaken it. *)
Lemma wp_raft__promotable (r : loc) rv votes :
  {{{ is_pkg_init raft ∗ r ↦ rv ∗
      own_tracker cfg rv.(raft.raft.trk') votes ∗
      own_raftLog rv.(raft.raft.raftLog') }}}
    r @! (go.PointerType raft.raft) @! "promotable" #()
  {{{ (b : bool), RET #b;
      r ↦ rv ∗ own_tracker cfg rv.(raft.raft.trk') votes ∗
      own_raftLog rv.(raft.raft.raftLog') ∗
      ⌜ b = bool_decide (rv.(raft.raft.id') ∈ cfg) ⌝ }}}.
Proof. Admitted.

(** [r.hasUnappliedConfChanges()]: false, since there is no
    reconfiguration.

    **In scope and unfinished** (2026-09-16).  Blocked on [own_raftLog], and
    the tempting shortcut does not work: the generated body
    ([new/code/go_etcd_io/raft/v3.v:3732]) opens with

        if r.raftLog.applied >= r.raftLog.committed { return false }

    but [applied >= committed] is a fact about the log that nothing available
    implies, so the [scan] over [(applied, committed]] is **genuinely
    reachable** -- it is not dead under our scope.  Returning [false]
    therefore needs [own_raftLog] to say that no entry in that range has
    [Type] [EntryConfChange] or [EntryConfChangeV2], i.e. it needs the entry
    list exposed, which is exactly the design question recorded for
    [own_raftLog] in notes/raft-election-refinement.md. *)
Lemma wp_raft__hasUnappliedConfChanges (r : loc) l :
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    r @! (go.PointerType raft.raft) @! "hasUnappliedConfChanges" #()
  {{{ RET #false; own_raftLog l }}}.
(** Returns [false] because **no configuration change is ever requested** --
    a scope assumption sanctioned 2026-09-16 and now listed in
    [election_protocol.v].  Note what it is *not*: the function's early
    [return false] is guarded by [applied >= committed], which the election
    scope does not imply, so the result does not follow from "the voter set is
    fixed".  It follows from the log containing no [EntryConfChange] or
    [EntryConfChangeV2] entry, which makes the [scan] over
    [(applied, committed]] find nothing.

    Blocked on [own_raftLog] only: that assumption has to be a conjunct of
    the log predicate, and [own_raftLog] is still an opaque [Axiom] in
    [inv_raftlog.v].  Once it is a real definition carrying "no conf-change
    entries", this is a walk over [scan] with an empty result. *)
Proof. Admitted.

(** The ids of the voters, in some order, as [campaign] enumerates them.
    [campaign] calls this on [&r.trk.Config.Voters], so the receiver is that
    field ref and not the tracker itself. *)
Axiom wp_campaign_peer_ids : ∀ (trk : loc) tv votes,
  {{{ is_pkg_init quorum ∗ trk ↦ tv ∗ own_tracker cfg tv votes }}}
    (trk.[tracker.ProgressTracker.t, "Config"].[tracker.Config.t, "Voters"])
      @! (go.PointerType quorum.JointConfig) @! "IDs" #()
  {{{ (mref : loc) (idm : gmap w64 unit), RET #mref;
      trk ↦ tv ∗ own_tracker cfg tv votes ∗
      mref ↦$ idm ∗ ⌜ dom idm = cfg ⌝ }}}.

(** *** The parts of the raft struct election neither reads nor writes:
    the read-state slice, the read-only queue, and the pending
    [MsgReadIndex] slice.  Indexed by exactly those three fields, so that
    updating any other field of the struct leaves it alone. *)
(** The five [traceX] functions below are **not** assumptions: Goose
    translates each of them to a literal no-op,
    [λ: <> <>, exception_do (do: #())], so each spec is a two-line proof.
    They were axioms until 2026-09-16 purely because nobody had looked at the
    generated body. *)

(** Full ownership of those three fields and everything hanging off them:
    the [readStates] slice, the [readOnly] object together with its [acks]
    map and its [unconfirmedReads] slice, and the
    [pendingReadIndexMessages] slice.  The *contents* are existential --
    election never reads any of it -- but the ownership is real, so nothing
    else in the development can claim the same heap. *)
Definition own_raft_misc (readStates : slice.t) (ro : loc)
                         (pendingReadIndex : slice.t) : iProp Σ :=
  ∃ (rss : list raft.ReadState.t) (rov : raft.readOnly.t)
    (acks : gmap w64 w64) (ucr : list loc)
    (prims : list raftpb.Message.t),
  "HreadStates" ∷ readStates ↦* rss ∗
  "HreadStates_cap" ∷ own_slice_cap raft.ReadState.t readStates (DfracOwn 1) ∗
  "Hro" ∷ ro ↦ rov ∗
  "Hacks" ∷ rov.(raft.readOnly.acks') ↦$ acks ∗
  "Hucr" ∷ rov.(raft.readOnly.unconfirmedReads') ↦* ucr ∗
  "Hucr_cap" ∷ own_slice_cap loc
                 rov.(raft.readOnly.unconfirmedReads') (DfracOwn 1) ∗
  "Hpri" ∷ pendingReadIndex ↦* prims ∗
  "Hpri_cap" ∷ own_slice_cap raftpb.Message.t pendingReadIndex (DfracOwn 1).

Lemma wp_traceReceiveMessage (r : loc) (mp : loc) rs ro pri :
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceReceiveMessage #r #mp
  {{{ RET #(); own_raft_misc rs ro pri }}}.
Proof. wp_start as "Hm". by iApply "HΦ". Qed.

Lemma wp_traceSendMessage (r : loc) (mp : loc) rs ro pri :
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceSendMessage #r #mp
  {{{ RET #(); own_raft_misc rs ro pri }}}.
Proof. wp_start as "Hm". by iApply "HΦ". Qed.

Lemma wp_traceBecomeFollower (r : loc) rs ro pri :
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceBecomeFollower #r
  {{{ RET #(); own_raft_misc rs ro pri }}}.
Proof. wp_start as "Hm". by iApply "HΦ". Qed.

Lemma wp_traceBecomeCandidate (r : loc) rs ro pri :
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceBecomeCandidate #r
  {{{ RET #(); own_raft_misc rs ro pri }}}.
Proof. wp_start as "Hm". by iApply "HΦ". Qed.

Lemma wp_traceBecomeLeader (r : loc) rs ro pri :
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceBecomeLeader #r
  {{{ RET #(); own_raft_misc rs ro pri }}}.
Proof. wp_start as "Hm". by iApply "HΦ". Qed.

(** [reset] replaces [r.readOnly] with [newReadOnly(r.readOnly.option)].
    Two pieces are needed: reading the old object's [option] field, and
    installing the fresh object. *)
Lemma own_raft_misc_option rs ro pri :
  own_raft_misc rs ro pri -∗
  ∃ (o : raft.ReadOnlyOption.t),
    ro.[raft.readOnly.t, "option"] ↦ o ∗
    (ro.[raft.readOnly.t, "option"] ↦ o -∗ own_raft_misc rs ro pri).
Proof.
  iIntros "Hm". iNamed "Hm".
  iExists rov.(raft.readOnly.option').
  iDestruct (access_strict
               (A := ro.[raft.readOnly.t, "option"] ↦ rov.(raft.readOnly.option'))
               (A' := ro.[raft.readOnly.t, "option"] ↦ rov.(raft.readOnly.option'))
               (P := ro ↦ rov) (P' := ro ↦ rov) with "Hro") as "[Hopt Hback]".
  iFrame "Hopt". iIntros "Hopt".
  iDestruct ("Hback" with "Hopt") as "Hro".
  rewrite /own_raft_misc. iFrame.
Qed.

(** The old queue is dropped and a fresh one installed.  The lemma *consumes*
    [own_raft_misc] at [ro] and returns it at [ro'], which is what [reset]
    does -- so this is not the discredited [own_raft_misc rv -∗
    own_raft_misc rv'] shape warned about above: it is tied to an actual
    allocation. *)
Lemma wp_newReadOnly (o : raft.ReadOnlyOption.t) rs ro pri :
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.newReadOnly #o
  {{{ (ro' : loc), RET #ro'; own_raft_misc rs ro' pri }}}.
Proof.
  wp_start as "Hm". iNamed "Hm". wp_auto.
  wp_apply wp_map_make1 as "%mref Hmref".
  wp_alloc ro' as "Hro'". wp_auto.
  iApply "HΦ". rewrite /own_raft_misc.
  iExists rss, _, ∅, ([] : list loc), prims.
  iFrame "Hro'". simpl.
  iFrame "HreadStates HreadStates_cap Hmref Hpri Hpri_cap".
  iSplitL.
  { iApply own_slice_nil. }
  iApply own_slice_cap_nil.
Qed.

(** [resetRandomizedElectionTimeout] draws from the global RNG and writes
    [r.randomizedElectionTimeout].  The *RNG* is outside core raft and may be
    assumed; this wrapper is raft code, so it is a [Lemma].  The field it
    writes appears in no other conjunct of [own_raft_phys], and the model has
    no clock. *)
Lemma wp_raft__resetRandomizedElectionTimeout (r : loc) rv :
  {{{ is_pkg_init raft ∗ r ↦ rv }}}
    r @! (go.PointerType raft.raft) @! "resetRandomizedElectionTimeout" #()
  {{{ (n : w64), RET #();
      r ↦ (rv <| raft.raft.randomizedElectionTimeout' := n |>) }}}.
Proof.
  wp_start as "Hr". wp_auto.
  Show.
Admitted.

(** [abortLeaderTransfer] clears [leadTransferee], which [own_raft_phys]
    requires to be zero anyway. *)
Lemma wp_raft__abortLeaderTransfer (r : loc) rv :
  {{{ is_pkg_init raft ∗ r ↦ rv }}}
    r @! (go.PointerType raft.raft) @! "abortLeaderTransfer" #()
  {{{ RET #(); r ↦ (rv <| raft.raft.leadTransferee' := W64 0 |>) }}}.
Proof. wp_start as "Hr". wp_auto. by iApply "HΦ". Qed.

(** [wp_raft__appendEmptyEntry] used to live here.  It moved to
    [inv_raft_phys.v], because stating it honestly needs [own_raft_phys]:
    [appendEntry] queues a [MsgAppResp], so an axiom owning only the log is
    false. *)

End proof.
