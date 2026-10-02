(** * Raft components election neither reads nor writes *)

Require Export New.proof.go_etcd_io.raft.election_proof.inv_raftlog.
Require Export New.proof.go_etcd_io.raft.election_proof.inv_tracker.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** The (fixed) set of voters. *)
Context (cfg : gset w64).


(** *** The parts of the raft struct election neither reads nor writes:
    the read-state slice, the read-only queue, and the pending
    [MsgReadIndex] slice.  Indexed by exactly those three fields, so that
    updating any other field of the struct leaves it alone.

    The Hoare triples about the functions that touch these fields --
    [newReadOnly], the five [traceX] hooks, [resetRandomizedElectionTimeout],
    [abortLeaderTransfer] -- each live in their own
    spec/postulates/proof/link collection; see notes/decisions.md. *)

(** Full ownership of those three fields and everything hanging off them:
    the [readStates] slice, the [readOnly] object together with its [acks]
    map and its [unconfirmedReads] slice, and the
    [pendingReadIndexMessages] slice.  The *contents* are existential --
    election never reads any of it -- but the ownership is real, so nothing
    else in the development can claim the same heap. *)
(** The [readOnly] object: the struct, its [acks] map and its
    [unconfirmedReads] slice.  Its own predicate because [newReadOnly]
    allocates one: that spec owns nothing going in and hands back exactly
    this (2026-09-23; it used to consume and return the whole of
    [own_raft_misc], including two slices it never touches). *)
Definition own_read_only (ro : loc) : iProp Σ :=
  ∃ (rov : raft.readOnly.t) (acks : gmap w64 w64),
  "Hro" ∷ ro ↦ rov ∗
  "Hacks" ∷ rov.(raft.readOnly.acks') ↦$ acks ∗
  (** Scope (phase 1): no read-index requests, so [unconfirmedReads] is
      empty -- which is what makes [heartbeatCtx] return [nil].  Stated by
      putting the empty list in the points-to rather than as a separate
      [⌜ ucr = [] ⌝] over an existential [ucr]: the same assertion, and the
      re-seals that frame this predicate by name keep working
      (2026-10-01). *)
  "Hucr" ∷ rov.(raft.readOnly.unconfirmedReads') ↦* ([] : list loc) ∗
  "Hucr_cap" ∷ own_slice_cap loc
                 rov.(raft.readOnly.unconfirmedReads') (DfracOwn 1).

(** Full ownership of the three fields election neither reads nor writes
    and everything hanging off them: the [readStates] slice, the
    [readOnly] object, and the [pendingReadIndexMessages] slice.  The
    [readStates] contents are existential -- nothing in scope reads them --
    and the two read-index queues are empty (phase-1 scope, 2026-10-01);
    the ownership is real, so nothing else in the development can claim the
    same heap. *)
Definition own_raft_misc (readStates : slice.t) (ro : loc)
                         (pendingReadIndex : slice.t) : iProp Σ :=
  ∃ (rss : list raft.ReadState.t),
  "HreadStates" ∷ readStates ↦* rss ∗
  "HreadStates_cap" ∷ own_slice_cap raft.ReadState.t readStates (DfracOwn 1) ∗
  "Hro_obj" ∷ own_read_only ro ∗
  (** Scope (phase 1): no read-index requests, so no [MsgReadIndex] is
      pending -- which is what makes [releasePendingReadIndexMessages] a
      no-op.  The empty list is in the points-to, as for [Hucr] above. *)
  "Hpri" ∷ pendingReadIndex ↦* ([] : list raftpb.Message.t) ∗
  "Hpri_cap" ∷ own_slice_cap raftpb.Message.t pendingReadIndex (DfracOwn 1).


(** [reset] replaces [r.readOnly] with [newReadOnly(r.readOnly.option)],
    so it reads the old object's [option] field; it reaches the object
    through [own_raft_phys_readOnly] ([inv_raft_phys.v]), which also
    installs the new one. *)
Lemma own_read_only_option ro :
  own_read_only ro -∗
  ∃ (o : raft.ReadOnlyOption.t),
    ro.[raft.readOnly.t, "option"] ↦ o ∗
    (ro.[raft.readOnly.t, "option"] ↦ o -∗ own_read_only ro).
Proof.
  iIntros "Hro_obj". iNamed "Hro_obj".
  iExists rov.(raft.readOnly.option').
  iDestruct (access_strict
               (A := ro.[raft.readOnly.t, "option"] ↦ rov.(raft.readOnly.option'))
               (A' := ro.[raft.readOnly.t, "option"] ↦ rov.(raft.readOnly.option'))
               (P := ro ↦ rov) (P' := ro ↦ rov) with "Hro") as "[Hopt Hback]".
  iFrame "Hopt". iIntros "Hopt".
  iDestruct ("Hback" with "Hopt") as "Hro".
  rewrite /own_read_only. iFrame.
Qed.


End proof.
