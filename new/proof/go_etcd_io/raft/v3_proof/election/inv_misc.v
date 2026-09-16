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
    field ref and not the tracker itself.

    **In scope, and blocked on the *translation*, not on the proof**
    (2026-09-16).  This was an [Axiom] until today.  It is core raft, so under
    the scope rule it may not be assumed; it is now an [Admitted] [Lemma] with
    the machine-checked prefix below banked.  What blocks it is not anything
    about raft: it is a disagreement between what Goose emits for array
    indexing and what the model gives a step to.

    [quorum.JointConfig] is [[2]MajorityConfig], i.e. an **array**
    ([new/code/go_etcd_io/raft/v3/quorum.v:552]).  Goose translates the
    element read [c[0]] inside [JointConfig.IDs] (quorum.v:82, and again at
    :94 for [c[1]]) as

        ![MajorityConfig] (IndexRef JointConfig (![JointConfig] "c", #(W64 0)))

    -- it *loads* the operand and then asks [IndexRef] for a reference into
    the loaded **value**.  That is right for slices and wrong for arrays:

    - [index_ref_slice] ([new/golang/defn/slice.v:122]) takes [(#s, #i)] with
      [s : slice.t], a *value* -- a slice value carries [slice.ptr], so an
      address can be recovered from it;
    - [index_ref_array] ([new/golang/defn/array.v:50]) takes [(#l, #i)] with
      [l : loc], a *location* -- an [array.t V n] is [array.mk n (list V)]
      ([src/goose_lang/lang.v:528]) and carries no address at all, so there is
      nothing to take a reference into.

    So the translated body is **stuck** at that [IndexRef] and no Hoare triple
    about it is provable.  Measured, not inferred -- three one-line probes,
    each checked with [rocq compile -vok]:

        (* steps: goal becomes  Φ #(array_index_ref map.t (sint.Z 0) l)  *)
        Lemma probe_loc (l : loc) Φ :
          ⊢ WP (IndexRef quorum.JointConfig (#l, #(W64 0)))%E {{ Φ }}.
        Proof. iStartProof. wp_auto. Admitted.

        (* does NOT step: [wp_auto] reports "Failed to progress" *)
        Lemma probe_val (a : array.t loc 2) Φ :
          ⊢ WP (IndexRef quorum.JointConfig (#a, #(W64 0)))%E {{ Φ }}.
        Proof. iStartProof. wp_auto. Admitted.

        (* steps: goal becomes  WP match array.arr a !! 0 with ... end  *)
        Lemma probe_index_val (a : array.t loc 2) Φ :
          ⊢ WP (Index quorum.JointConfig (#a, #(W64 0)))%E {{ Φ }}.
        Proof. iStartProof. wp_auto. Admitted.

    i.e. Goose emits the one combination of operator and operand that has no
    rule.  Either of the other two would work, so the fix belongs in the Go
    fork's Goose and not here: for an addressable array operand emit
    [IndexRef T ("c", i)] (the address), or, since this occurrence is a plain
    read, emit the value form [Index T (![T] "c", i)], for which
    [index_array] ([new/golang/defn/array.v:54]) does have a rule.  With
    [Hvoters_arr] in hand the value form reduces straight to [voters_ref].

    Nothing else here is missing.  Once the operand steps, the remainder is
    a [wp_map_for_range] over [voters_ref] (the [Hvoters_dom] conjunct of
    [own_tracker] gives [dom voters = cfg]) followed by the pure step
    [wp_map_nil_for_range] ([new/golang/theory/map.v:305]) for the nil second
    component of the joint config, then [return: m].  The statement below is
    the right one; do not weaken it.

    The same defect is why [wp_JointConfig__CommittedIndex]
    ([v3_proof/readonly.v:718]) is an [Axiom]: [JointConfig.CommittedIndex]
    indexes the same array the same way (quorum.v:132,136). *)
Lemma wp_campaign_peer_ids : ∀ (trk : loc) tv votes,
  {{{ is_pkg_init quorum ∗ trk ↦ tv ∗ own_tracker cfg tv votes }}}
    (trk.[tracker.ProgressTracker.t, "Config"].[tracker.Config.t, "Voters"])
      @! (go.PointerType quorum.JointConfig) @! "IDs" #()
  {{{ (mref : loc) (idm : gmap w64 unit), RET #mref;
      trk ↦ tv ∗ own_tracker cfg tv votes ∗
      mref ↦$ idm ∗ ⌜ dom idm = cfg ⌝ }}}.
(* [Proof using Type], not the file's [W] default: [W] would force
   [package_sem] into the discharged signature, and this constant's former
   [Axiom] form did not have it.  Checked -- with [Proof using Type] the type
   of this lemma is syntactically identical to the axiom it replaces, so no
   call site changes.  See notes/gotchas.md. *)
Proof using Type.
  (* Everything down to the [Admitted] is machine-checked. *)
  intros trk tv votes.
  wp_start as "[Htrk Hown]". iNamed "Hown".
  (* [wp_auto] reads [r.trk.Config.Voters] out of [trk ↦ tv] and reduces the
     pointer method to the value method applied to the [JointConfig] value. *)
  wp_auto.
  (* Two [wp_call]s, not one: [JointConfig'ptr_IDs_unfold] is the wrapper
     [λ: "$r", MethodResolve JointConfig "IDs" (![JointConfig] "$r")], so the
     first call enters the wrapper and the second enters [JointConfig__IDsⁱᵐᵖˡ].
     A single [wp_call] leaves [WP quorum.JointConfig__IDsⁱᵐᵖˡ …] and the next
     [wp_auto] then reports "Failed to progress", which looks like the stuck
     point below but is not. *)
  wp_method_call. wp_call. wp_call.
  (* [GoAlloc JointConfig] gives ["c" ∷ c_ptr ↦ tv.(Config').(Voters')]; note
     this does *not* hit the [alloc_array ⤳ AngelicExit] escape hatch. *)
  wp_auto.
  (* [m := map[uint64]struct{}{}] *)
  wp_apply wp_map_make1. iIntros "%mref Hmref".
  wp_auto.
  (* STUCK, and this is the real stuck point.  The remaining program is

       let: "$range" := ![quorum.MajorityConfig]
                          (IndexRef quorum.JointConfig
                             (# tv.(tracker.ProgressTracker.Config')
                                  .(tracker.Config.Voters'), # (W64 0))%V) in
       (let: "id" := GoAlloc go.uint64 … in map.for_range … ) ;;;
       (the same at index 1) ;;;
       return: ![go.MapType go.uint64 (go.StructType [])] (# m_ptr)

     and a further [wp_auto] fails with "Failed to progress".  See the comment
     above the statement: the operand of [IndexRef] is an array *value* and
     the model only gives [IndexRef] a step on an array *location*. *)
Admitted.

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
