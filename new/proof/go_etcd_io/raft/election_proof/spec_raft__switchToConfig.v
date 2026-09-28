Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [r.switchToConfig(cfg, trk)] installs a configuration and progress map
    in [r.trk], sets [r.isLearner], and returns the tracker's [ConfState].

    **Only the non-leader case is specified** ([s.role ≠ Leader]).  There
    the function returns right after computing [cs]: both of its leader
    branches -- stepping down on removal, and [maybeCommit]/[bcastAppend]
    to the new configuration -- are guarded by [state == StateLeader].
    That is the case [newRaft] needs, the only caller in scope
    (reconfiguration, [applyConfChange], is out of scope).

    The tracker is **on loan** ([nstate.lent], [defs.v]) on both sides: the
    caller holds the new tracker's heap, [own_tracker cfg tv' votes prs] at
    the tracker value the two writes produce, and gets it back together with
    a struct whose [r.trk] is pinned at [tv'].  Both sides are stated at
    the setter form [s <| lent := Some _ |>], the form
    [own_raft_phys_trk_lent] works at.  That is what lets [newRaft]
    call this before its tracker satisfies [own_tracker] -- the empty
    tracker [MakeProgressTracker] builds has no voters.

    [r.isLearner] ends up [false]: it is [ok && pr.IsLearner], and every
    [Progress] in [own_tracker] has [IsLearner = false]. *)
Definition wp_raft__switchToConfig_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t)
    (tv : tracker.ProgressTracker.t) (cfgv : tracker.Config.t) (prsm : loc)
    (votes : gmap w64 bool) (prs : gmap w64 loc),
  let tv' := tv <| tracker.ProgressTracker.Config' := cfgv |>
                <| tracker.ProgressTracker.Progress' := prsm |> in
  s.(nstate.role) ≠ role.Leader →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id (s <| nstate.lent := Some tv |>) ∗
      own_tracker cfg tv' votes prs }}}
    r @! (go.PointerType raft.raft) @! "switchToConfig" #cfgv #prsm
  {{{ (cs : raftpb.ConfState.t) (xs : list w64), RET #cs;
      own_raft_phys cfg r id (s <| nstate.lent := Some tv' |>) ∗
      own_tracker cfg tv' votes prs ∗
      cs.(raftpb.ConfState.Voters') ↦* xs ∗ ⌜ xs ≡ₚ elements cfg ⌝ ∗
      ⌜ cs.(raftpb.ConfState.VotersOutgoing').(slice.len) = W64 0 ∧
        cs.(raftpb.ConfState.Learners').(slice.len) = W64 0 ∧
        cs.(raftpb.ConfState.LearnersNext').(slice.len) = W64 0 ∧
        cs.(raftpb.ConfState.AutoLeave') = cfgv.(tracker.Config.AutoLeave') ⌝ }}}.

Module Type RAFT__SWITCHTOCONFIG.
  Parameter wp_raft__switchToConfig : wp_raft__switchToConfig_body.
  Arguments wp_raft__switchToConfig {_ _ _ _ _ _ _ _}.
End RAFT__SWITCHTOCONFIG.
