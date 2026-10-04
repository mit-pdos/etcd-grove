Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [commit_ok cfg ps n]: a leader in protocol state [ps] may advance its
    commit index to [n] -- exactly the premises of the model's
    [step_commit] other than the role: [n] is past the current commit
    index and inside the log, the entry there is of the leader's own term,
    and a quorum of voters has acknowledged [n] ([acked_by], over
    [matched]).  Shared with [spec_stepLeader.v]. *)
Definition commit_ok (cfg : gset w64) (ps : pstate.t) (n : w64) : Prop :=
  (uint.Z ps.(pstate.commit) < uint.Z n)%Z ∧
  (uint.Z n ≤ plog_last_index_Z ps.(pstate.base) ps.(pstate.log))%Z ∧
  plog_term_at ps.(pstate.base) ps.(pstate.log) n = Some ps.(pstate.term) ∧
  is_quorum cfg (acked_by ps n).

(** [r.maybeCommit()] ([raft__maybeCommitⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:3381; [raft.go:773]):

      defer traceCommit(r)
      return r.raftLog.maybeCommit(entryID{term: r.Term, index: r.trk.Committed()})

    [Committed()] is the quorum index of the voters' [Match] values
    ([spec_ProgressTracker__Committed.v]); [raftLog.maybeCommit] moves
    [committed] there when it is ahead, the term is non-zero and the log
    has [r.Term] at that index ([spec_raftLog__maybeCommit.v]).  The
    deferred [traceCommit] is a no-op.

    On [true] the new commit index [N] satisfies [commit_ok] at the
    protocol reading of [s]: that is [step_commit].  The quorum is stated
    over [to_pstate s]'s [matched], which is the [Progress] [Match] values
    only for a leader -- hence [s.role = Leader]; the go code says
    "This can only be called in StateLeader".  [id ∈ cfg] makes the voter
    set non-empty, which is what makes [Committed()] a quorum index (for
    an empty configuration it is [MaxUint64]).  On [false] nothing
    changes. *)
Definition wp_raft__maybeCommit_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t),
  s.(nstate.role) = prole.Leader →
  id ∈ cfg →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "maybeCommit" #()
  {{{ (b : bool) (N : w64), RET #b;
      own_raft_phys cfg r id
        (if b then s <| nstate.logst :=
                       s.(nstate.logst) <| logstate.committed := N |> |>
         else s) ∗
      ⌜ b = true → commit_ok cfg (to_pstate s) N ⌝ }}}.

Module Type RAFT__MAYBECOMMIT.
  Parameter wp_raft__maybeCommit : wp_raft__maybeCommit_body.
  Arguments wp_raft__maybeCommit {_ _ _ _ _ _ _ _}.
End RAFT__MAYBECOMMIT.
