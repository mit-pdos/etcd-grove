Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [confchange.Restore chg cs] replays a [ConfState] onto the empty
    configuration [chg.Tracker] and returns the resulting [Config] and
    [ProgressMap].

    **Not translated** ([new/code/go_etcd_io/raft/v3/confchange.v.toml]
    translates only the [Changer] type), so this triple is an [Axiom] --
    and, unlike [slices.Sort], one about **core raft** code.  It is stated
    for the one case this development needs: a voters-only [ConfState]
    applied to the empty tracker [MakeProgressTracker] builds.  Read against
    the Go ([confchange/restore.go], [confchange/confchange.go]) it says:

    - [toConfChangeSingle] turns [cs] into no outgoing changes and one
      [AddNode id] per [id ∈ cs.Voters], since [VotersOutgoing], [Learners]
      and [LearnersNext] are empty;
    - [chain] runs one [Changer.Simple(AddNode id)] per voter.  Each
      [Simple] starts with [checkAndCopy], which [Clone]s the config
      (a fresh [Voters[0]] map; [Voters[1]], [Learners], [LearnersNext]
      stay [nil]; [AutoLeave] is not copied, so [false]) and copies the
      progress map into a fresh one, each [Progress] shallow-copied into a
      fresh allocation.  [makeVoter] on a new id calls [initProgress], which
      adds [id] to [Voters[0]] and allocates a [Progress] with
      [State = StateProbe], [IsLearner = false] and a fresh
      [NewInflights(MaxInflight, MaxInflightBytes)]; on a repeated id it
      only re-marks it a voter.  [apply] **skips [NodeID = 0]**, hence the
      premise [0 ∉ voters].  No error is reachable: the config is never
      joint, one voter changes per step ([symdiff ≤ 1]), and
      [checkInvariants] holds throughout;
    - so the result is a fresh voter map and a fresh progress map, both
      with domain [set voters], each [Progress] owned exactly once (the
      intermediate copies are garbage, and so are the tracker's original
      maps, which are only read).

    **[voters ≠ []] is load-bearing for soundness, not just for the
    caller.**  With no voters there are no ops, and [chain] returns
    [chg.Tracker.Config] and [chg.Tracker.Progress] *themselves* -- the maps
    the premise already owns.  A postcondition handing out fresh points-tos
    for them would then duplicate ownership, i.e. prove [False].

    [NoDup voters] is *not* needed here ([Restore] de-duplicates); it is
    needed by [assertConfStatesEquivalent], whose [Equivalent] check fails
    on a [ConfState] with a repeated voter.

    [MaxInflight]'s bound is what [own_progress] (via [inflights_ok]) asks
    of the fresh [Inflights]; see [spec_tracker_NewInflights.v]. *)
Definition wp_confchange_Restore_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (chg : confchange.Changer.t) (cs : raftpb.ConfState.t)
    (voters : list w64) (dq : dfrac) (v0 : loc),
  let tv := chg.(confchange.Changer.Tracker') in
  voters ≠ [] →
  W64 0 ∉ voters →
  cs.(raftpb.ConfState.VotersOutgoing').(slice.len) = W64 0 →
  cs.(raftpb.ConfState.Learners').(slice.len) = W64 0 →
  cs.(raftpb.ConfState.LearnersNext').(slice.len) = W64 0 →
  (0 ≤ sint.Z tv.(tracker.ProgressTracker.MaxInflight') < 2 ^ 62)%Z →
  (* the empty configuration *)
  array.arr tv.(tracker.ProgressTracker.Config').(tracker.Config.Voters')
    = [v0; map.nil] →
  tv.(tracker.ProgressTracker.Config').(tracker.Config.Learners') = map.nil →
  tv.(tracker.ProgressTracker.Config').(tracker.Config.LearnersNext') = map.nil →
  {{{ is_pkg_init confchange ∗
      cs.(raftpb.ConfState.Voters') ↦*{dq} voters ∗
      v0 ↦$ (∅ : gmap w64 unit) ∗
      tv.(tracker.ProgressTracker.Progress') ↦$□ (∅ : gmap w64 loc) }}}
    @! confchange.Restore #chg #cs
  {{{ (cfgv : tracker.Config.t) (prsm : loc) (prs : gmap w64 loc)
      (vref : loc) (vm : gmap w64 unit),
      RET (#cfgv, #prsm, #interface.nil);
      cs.(raftpb.ConfState.Voters') ↦*{dq} voters ∗
      v0 ↦$ (∅ : gmap w64 unit) ∗
      tv.(tracker.ProgressTracker.Progress') ↦$□ (∅ : gmap w64 loc) ∗
      ⌜ array.arr cfgv.(tracker.Config.Voters') = [vref; map.nil] ∧
        cfgv.(tracker.Config.Learners') = map.nil ∧
        cfgv.(tracker.Config.LearnersNext') = map.nil ∧
        cfgv.(tracker.Config.AutoLeave') = false ⌝ ∗
      vref ↦$ vm ∗ ⌜ dom vm = list_to_set voters ⌝ ∗
      prsm ↦$ prs ∗ ⌜ dom prs = list_to_set voters ⌝ ∗
      ([∗ map] pr ∈ prs, ∃ pv iv, own_progress pr pv iv) }}}.

Module Type CONFCHANGE_RESTORE.
  Parameter wp_confchange_Restore : wp_confchange_Restore_body.
  Arguments wp_confchange_Restore {_ _ _ _ _ _ _ _}.
End CONFCHANGE_RESTORE.
