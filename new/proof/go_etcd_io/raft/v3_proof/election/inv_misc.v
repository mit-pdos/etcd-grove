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

    **In scope.  The translation defect that blocked this is fixed**
    (2026-09-17); what is left is ordinary proof work.

    Until 2026-09-17 Goose emitted the element read [c[0]] inside
    [JointConfig.IDs] as

        ![MajorityConfig] (IndexRef JointConfig (![JointConfig] "c", #(W64 0)))

    -- it *loaded* the operand and then asked [IndexRef] for a reference into
    the loaded **value**.  That is right for slices and wrong for arrays:

    - [index_ref_slice] ([new/golang/defn/slice.v:122]) takes [(#s, #i)] with
      [s : slice.t], a *value* -- a slice value carries [slice.ptr], so an
      address can be recovered from it;
    - [index_ref_array] ([new/golang/defn/array.v:50]) takes [(#l, #i)] with
      [l : loc], a *location* -- an [array.t V n] is [array.mk n (list V)]
      ([src/goose_lang/lang.v:528]) and carries no address at all, so there is
      nothing to take a reference into.

    So the body was **stuck** there and no Hoare triple about it was provable.
    The fix was in Goose ([goose/goose.go], [exprAddr]'s [*ast.IndexExpr]
    case): for an array operand take the array's address rather than loading
    it.  The emitted code is now

        ![MajorityConfig] (IndexRef JointConfig ("c", #(W64 0)))

    ([new/code/go_etcd_io/raft/v3/quorum.v:82], and :94 for [c[1]]), and
    [c_ptr] is exactly what the receiver's [GoAlloc JointConfig] produces, so
    [index_ref_array] applies.  Measured: the [wp_auto] below now steps the
    [IndexRef] to [#(array_index_ref map.t 0 c_ptr)] and stops at the *load*
    of that location -- an ownership obligation, not a missing rule.

    **What is left.**  Split element 0 out of ["c" : c_ptr ↦ …Voters'] with
    [array_acc] ([new/golang/theory/array.v]); [Hvoters_arr] says the element
    is [voters_ref], so the load yields it.  Then a [wp_map_for_range] over
    [voters_ref] (the [Hvoters_dom] conjunct of [own_tracker] gives
    [dom voters = cfg]), then the same at index 1, where the element is
    [map.nil] and the pure step [wp_map_nil_for_range]
    ([new/golang/theory/map.v:305]) applies, then [return: m].  The statement
    below is the right one; do not weaken it.

    [slices.Sort] is *not* involved -- that sort is in [campaign], not in
    [IDs].

    [wp_JointConfig__CommittedIndex] ([v3_proof/readonly.v:718]) is still an
    [Axiom] for what *was* this same defect: [JointConfig.CommittedIndex]
    indexes the same array the same way (quorum.v:132,136).  It is now
    unblocked too and should be discharged. *)
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
  (* The array index steps now.  The [wp_auto] above reduced
     [IndexRef quorum.JointConfig (# c_ptr, # (W64 0))] to
     [# (array_index_ref map.t 0 c_ptr)] and stopped at the *load* of it:

       let: "$range" := ![quorum.MajorityConfig]
                          (# (array_index_ref map.t 0 c_ptr)) in
       (let: "id" := GoAlloc go.uint64 … in map.for_range … ) ;;;
       (the same at index 1, IndexRef not yet stepped) ;;;
       return: ![go.MapType go.uint64 (go.StructType [])] (# m_ptr)

     That load is an ownership obligation, not a missing rule: use [array_acc]
     on ["c"] to peel element 0 off, with [Hvoters_arr] for the lookup side
     condition.  See the comment above the statement for the rest. *)
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
