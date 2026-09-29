Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [p.ConfState()] is the [ConfState] of the active configuration: the
    voters (some permutation of [cfg]; really sorted), and -- since
    [own_tracker] is a simple configuration with no learners -- empty
    [VotersOutgoing], [Learners] and [LearnersNext].  Only [Voters] is
    handed back with its elements; for the others their length is all any
    caller needs. *)
Definition wp_ProgressTracker__ConfState_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (trk : loc) tv votes (prs : gmap w64 loc) (pvs : gmap w64 (tracker.Progress.t * tracker.Inflights.t)),
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker cfg tv votes prs pvs }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "ConfState" #()
  {{{ (cs : raftpb.ConfState.t) (xs : list w64), RET #cs;
      trk ↦ tv ∗ own_tracker cfg tv votes prs pvs ∗
      cs.(raftpb.ConfState.Voters') ↦* xs ∗ ⌜ xs ≡ₚ elements cfg ⌝ ∗
      ⌜ cs.(raftpb.ConfState.VotersOutgoing').(slice.len) = W64 0 ∧
        cs.(raftpb.ConfState.Learners').(slice.len) = W64 0 ∧
        cs.(raftpb.ConfState.LearnersNext').(slice.len) = W64 0 ∧
        cs.(raftpb.ConfState.AutoLeave') = false ⌝ }}}.

Module Type PROGRESSTRACKER__CONFSTATE.
  Parameter wp_ProgressTracker__ConfState : wp_ProgressTracker__ConfState_body.
  Arguments wp_ProgressTracker__ConfState {_ _ _ _ _ _ _ _}.
End PROGRESSTRACKER__CONFSTATE.
