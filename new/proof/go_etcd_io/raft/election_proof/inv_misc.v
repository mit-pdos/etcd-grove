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


End proof.
