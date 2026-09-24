Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [MakeProgressTracker] builds the **empty** tracker: fresh, empty
    [Votes] and [Progress] maps, a joint configuration
    [[MajorityConfig{}; nil]] and nil learner sets.

    This is not [own_tracker]: that predicate is for a tracker over a
    non-empty voter set [cfg] ([Hcfg_ne]), and the empty tracker has none.
    [newRaft] never uses it as a tracker -- it only hands it to
    [confchange.Restore] as the starting point, and then [switchToConfig]
    overwrites its [Config] and [Progress] -- so its postcondition is the
    raw pieces [Restore] reads and [own_tracker] later needs ([Votes]). *)
Definition wp_MakeProgressTracker_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (maxInflight maxBytes : w64),
  {{{ is_pkg_init tracker }}}
    @! tracker.MakeProgressTracker #maxInflight #maxBytes
  {{{ (tv : tracker.ProgressTracker.t) (v0 : loc), RET #tv;
      ⌜ tv.(tracker.ProgressTracker.MaxInflight') = maxInflight ∧
        tv.(tracker.ProgressTracker.MaxInflightBytes') = maxBytes ∧
        array.arr tv.(tracker.ProgressTracker.Config').(tracker.Config.Voters')
          = [v0; map.nil] ∧
        tv.(tracker.ProgressTracker.Config').(tracker.Config.Learners') = map.nil ∧
        tv.(tracker.ProgressTracker.Config').(tracker.Config.LearnersNext') = map.nil ∧
        tv.(tracker.ProgressTracker.Config').(tracker.Config.AutoLeave') = false ⌝ ∗
      v0 ↦$ (∅ : gmap w64 unit) ∗
      tv.(tracker.ProgressTracker.Votes') ↦$ (∅ : gmap w64 bool) ∗
      tv.(tracker.ProgressTracker.Progress') ↦$ (∅ : gmap w64 loc) }}}.

Module Type MAKEPROGRESSTRACKER.
  Parameter wp_MakeProgressTracker : wp_MakeProgressTracker_body.
  Arguments wp_MakeProgressTracker {_ _ _ _ _ _ _ _}.
End MAKEPROGRESSTRACKER.
