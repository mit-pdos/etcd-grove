Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__restore.
Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__handleAppendEntries.

(** * [r.handleSnapshot(m)] ([raft.go:1827], [raft__handleSnapshotⁱᵐᵖˡ])

        var s pb.Snapshot
        if m.Snapshot != nil { s = *m.Snapshot }
        if r.restore(s) {
            r.logger.Infof(...)
            r.send(pb.Message{To: m.From, Type: pb.MsgAppResp, Index: r.raftLog.lastIndex()})
        } else {
            r.logger.Infof(...)
            r.send(pb.Message{To: m.From, Type: pb.MsgAppResp, Index: r.raftLog.committed})
        }

    The three exits of [restore_result], each with its acknowledgement
    ([app_resp], accepting): the old commit index when the snapshot is
    obsolete, and the snapshot's index after a fast-forward (the new commit
    index) or a restore (the new last index).  [m.Snapshot] points to [sv]
    ([↦□]: the receiver only reads it), so the [nil] arm is dead; the
    premises are [restore]'s. *)
Section results.
Context {ext : ffi_syntax}.

Definition handle_snap_result (id : w64) (s : nstate.t) (m : raftpb.Message.t)
    (sv : raftpb.Snapshot.t) (s' : nstate.t) : Prop :=
  let ls := s.(nstate.logst) in
  let es := ls.(logstate.sents) ++ ls.(logstate.uents) in
  let sid := snap_id sv in
  let to := m.(raftpb.Message.From') in
  (uint.Z sid.(raft.entryID.index') ≤ uint.Z ls.(logstate.committed) ∧
   s' = send_msgs s [app_resp id s to false ls.(logstate.committed) (W64 0) (W64 0)])
  ∨
  (uint.Z ls.(logstate.committed) < uint.Z sid.(raft.entryID.index') ∧
   plog_matches ls.(logstate.prev) es sid ∧
   s' = send_msgs (s <| nstate.logst := ls <| logstate.committed := sid.(raft.entryID.index') |> |>)
          [app_resp id s to false sid.(raft.entryID.index') (W64 0) (W64 0)])
  ∨
  (uint.Z ls.(logstate.committed) < uint.Z sid.(raft.entryID.index') ∧
   ¬ plog_matches ls.(logstate.prev) es sid ∧
   ∃ prs pvs,
     s' = send_msgs (s <| nstate.progress := prs |>
                       <| nstate.prvals := pvs |> <| nstate.logst := log_restore ls sid |>)
            [app_resp id s to false sid.(raft.entryID.index') (W64 0) (W64 0)]).

End results.

Definition wp_raft__handleSnapshot_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t)
    (m : raftpb.Message.t) (sv : raftpb.Snapshot.t) (voters : list w64),
  s.(nstate.role) = prole.Follower →
  s.(nstate.votes) = ∅ →
  id ∈ cfg →
  snap_scope cfg sv voters →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
      "#Hsv" ∷ m.(raftpb.Message.Snapshot') ↦□ sv ∗
      "#Hvoters" ∷ sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
                     .(raftpb.ConfState.Voters') ↦*□ voters }}}
    r @! (go.PointerType raft.raft) @! "handleSnapshot" #m
  {{{ (s' : nstate.t), RET #();
      own_raft_phys cfg r id s' ∗ ⌜ handle_snap_result id s m sv s' ⌝ }}}.

Module Type RAFT__HANDLESNAPSHOT.
  Parameter wp_raft__handleSnapshot : wp_raft__handleSnapshot_body.
  Arguments wp_raft__handleSnapshot {_ _ _ _ _ _ _ _}.
End RAFT__HANDLESNAPSHOT.
