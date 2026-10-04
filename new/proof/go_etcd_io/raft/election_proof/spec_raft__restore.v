Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** * [r.restore(s)] ([raft.go:1849], [raft__restoreⁱᵐᵖˡ])

    Three exits that matter, in the body's order:

    - [s.Metadata.Index <= committed]: obsolete, [false], nothing changes;
    - the log already has [(Term, Index)] ([matchTerm]): [commitTo(Index)]
      and [false] -- a fast-forward of the commit index;
    - otherwise [raftLog.restore(s)], then the tracker rebuilt from the
      snapshot's [ConfState] ([MakeProgressTracker], [confchange.Restore],
      [switchToConfig], [assertConfStatesEquivalent]) and [true].

    Three more are dead under the premises: the node is not a follower
    ([becomeFollower(Term+1)], [false]) -- both callers have just made it
    one, so [s.role = Follower]; [r.id] is in none of the [ConfState]'s
    sets ([false]) -- the voters are [cfg] and [id ∈ cfg]; and
    [confchange.Restore] failing ([panic]) -- its axiom covers the
    voters-only, zero-free case.

    [snap_scope cfg sv voters] is the fixed-voter-set scope for a snapshot,
    what [Step]'s ["Hsnap"] supplies: the [ConfState] is [cfg]'s voters,
    nothing else (no learners, no joint configuration, [AutoLeave] off --
    [assertConfStatesEquivalent] compares it with the one [switchToConfig]
    reports); [cfg] is zero-free ([confchange.Restore] skips [NodeID = 0]);
    and the index is below [2^61] ([log_store_ok]'s bound for a pending
    snapshot, [inv_raftlog.v]).

    The rebuilt tracker: a fresh, empty [Votes] map -- the tally was
    already empty ([s.votes = ∅]: a follower's, [follower_votes_ok]), so
    [nstate.votes] does not move -- a fresh progress map over the same
    [cfg] ([prs]), and [Progress] values [pvs] the spec does not pin -- a
    follower's are invisible to the protocol ([to_pstate]). *)
Definition snap_scope (cfg : gset w64) (sv : raftpb.Snapshot.t) (voters : list w64) : Prop :=
  let cs := sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState') in
  voters ≡ₚ elements cfg ∧ W64 0 ∉ cfg ∧
  cs.(raftpb.ConfState.Learners').(slice.len) = W64 0 ∧
  cs.(raftpb.ConfState.VotersOutgoing').(slice.len) = W64 0 ∧
  cs.(raftpb.ConfState.LearnersNext').(slice.len) = W64 0 ∧
  cs.(raftpb.ConfState.AutoLeave') = false ∧
  (uint.Z sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.Index') < 2^61)%Z.

Section results.
Context {ext : ffi_syntax}.

Definition restore_result (s : nstate.t) (sv : raftpb.Snapshot.t) (b : bool)
    (s' : nstate.t) : Prop :=
  let ls := s.(nstate.logst) in
  let es := ls.(logstate.sents) ++ ls.(logstate.uents) in
  let sid := snap_id sv in
  (uint.Z sid.(raft.entryID.index') ≤ uint.Z ls.(logstate.committed) ∧
   b = false ∧ s' = s)
  ∨
  (uint.Z ls.(logstate.committed) < uint.Z sid.(raft.entryID.index') ∧
   plog_matches ls.(logstate.prev) es sid ∧ b = false ∧
   s' = s <| nstate.logst := ls <| logstate.committed := sid.(raft.entryID.index') |> |>)
  ∨
  (uint.Z ls.(logstate.committed) < uint.Z sid.(raft.entryID.index') ∧
   ¬ plog_matches ls.(logstate.prev) es sid ∧ b = true ∧
   ∃ prs pvs, s' = s <| nstate.progress := prs |>
                     <| nstate.prvals := pvs |> <| nstate.logst := log_restore ls sid |>).

End results.

Definition wp_raft__restore_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t)
    (sv : raftpb.Snapshot.t) (voters : list w64),
  s.(nstate.role) = prole.Follower →
  s.(nstate.votes) = ∅ →
  id ∈ cfg →
  snap_scope cfg sv voters →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
      "#Hvoters" ∷ sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
                     .(raftpb.ConfState.Voters') ↦*□ voters }}}
    r @! (go.PointerType raft.raft) @! "restore" #sv
  {{{ (b : bool) (s' : nstate.t), RET #b;
      own_raft_phys cfg r id s' ∗ ⌜ restore_result s sv b s' ⌝ }}}.

Module Type RAFT__RESTORE.
  Parameter wp_raft__restore : wp_raft__restore_body.
  Arguments wp_raft__restore {_ _ _ _ _ _ _ _}.
End RAFT__RESTORE.
