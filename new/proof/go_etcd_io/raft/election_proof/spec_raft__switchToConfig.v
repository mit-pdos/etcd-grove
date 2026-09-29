Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [r.switchToConfig(cfg, trk)] installs a configuration and progress map
    in [r.trk], sets [r.isLearner], and returns the tracker's [ConfState].

    **Only the non-leader case is specified** ([s.role ≠ Leader]).  There
    the function returns right after computing [cs]: both of its leader
    branches -- stepping down on removal, and [maybeCommit]/[bcastAppend]
    to the new configuration -- are guarded by [state == StateLeader].
    That is the case [newRaft] needs, the only caller in scope
    (reconfiguration, [applyConfChange], is out of scope).

    **It changes the configuration** [own_raft_phys] is indexed by, from
    [cfg0] to [cfg], and the progress map with it: the new [Config] and
    progress map come in as [own_config] (what [confchange.Restore]
    builds), and the struct goes out at [cfg] ([own_raft_phys_reconfig],
    [own_tracker_reconfig]).  Until 2026-09-29 the tracker was held on loan
    across the call instead, because the empty tracker [newRaft] starts
    from was not an [own_tracker].

    [r.isLearner] ends up [false]: it is [ok && pr.IsLearner], and every
    [Progress] in [own_tracker] has [IsLearner = false]. *)
Definition wp_raft__switchToConfig_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg0 cfg : gset w64) (r : loc) (id : w64) (s : nstate.t)
    (cfgv : tracker.Config.t) (prsm : loc) (prs : gmap w64 loc),
  s.(nstate.role) ≠ role.Leader →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg0 r id s ∗ own_config cfg cfgv prsm prs }}}
    r @! (go.PointerType raft.raft) @! "switchToConfig" #cfgv #prsm
  {{{ (cs : raftpb.ConfState.t) (xs : list w64) pvs, RET #cs;
      own_raft_phys cfg r id (s <| nstate.progress := prs |> <| nstate.prvals := pvs |>) ∗
      cs.(raftpb.ConfState.Voters') ↦* xs ∗ ⌜ xs ≡ₚ elements cfg ⌝ ∗
      ⌜ cs.(raftpb.ConfState.VotersOutgoing').(slice.len) = W64 0 ∧
        cs.(raftpb.ConfState.Learners').(slice.len) = W64 0 ∧
        cs.(raftpb.ConfState.LearnersNext').(slice.len) = W64 0 ∧
        cs.(raftpb.ConfState.AutoLeave') = false ⌝ }}}.

Module Type RAFT__SWITCHTOCONFIG.
  Parameter wp_raft__switchToConfig : wp_raft__switchToConfig_body.
  Arguments wp_raft__switchToConfig {_ _ _ _ _ _ _ _}.
End RAFT__SWITCHTOCONFIG.
