/- (D22 S-d2, 2026-10-21) Lean-first. -/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.SpecResults

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.appliedSnap(snap)` (`raft.go:766`):

    index := snap.GetMetadata().GetIndex()
    r.raftLog.stableSnapTo(index)
    r.appliedTo(index, 0 /* size */)
    cs := pb.EnsureConfState(snap.GetMetadata().GetConfState())
    r.trk = tracker.MakeProgressTracker(r.trk.MaxInflight, r.trk.MaxInflightBytes)
    cfg, trk, err := confchange.Restore(confchange.Changer{...}, cs)
    if err != nil { panic(...) }
    assertConfStatesEquivalent(r.logger, cs, r.switchToConfig(cfg, trk))

The acknowledgement of a snapshot's `Ready` (`MsgStorageAppendResp`'s `Snapshot`, both of
`Step`'s arms): the pending snapshot is dropped if it is the acknowledged one (`logStableSnap`)
and `applied` moves to the snapshot's index (`logAppliedTo`); then (2026-10-28, stage U0: the fork's
`raft37-goose-lean-a2`, the fix of `issues/raft-snapshot-during-apply-stale-confchange.md`; until
then `restore` did it) the tracker is rebuilt from the snapshot's `ConfState`, and the node is at
the configuration it denotes (`snapCfg sv cl`), with a fresh progress map `prs`, `Progress` values
`pvs` the spec does not pin (a follower's are invisible to the protocol, `toPState`) and its learner
flag. The raft struct comes in the acknowledgement's windows (`ownRaftPhysCVW`) and leaves quiet.

Premises: the hit happens exactly in the `sapp` window (`raftLog.stableSnapTo`'s: the storage
holds the snapshot, the application's receipt absorbed), not in `appliedSnap`'s own window, the
snapshot at or below the log's boundary (it is the pending one, or older: a second restore since
the `Ready`) -- which gives `appliedTo`'s guard (`index ≤ committed`) and keeps `applying` below
`offsetInProgress` -- and the two ghost flags of `LogGhOk`. (U0) And the rebuild's, which were
`restore`'s: a follower (so `appliedTo` proposes no automatic leave -- until stage U5 its premise -- and
`switchToConfig`'s, which at a leader would need its peers' `Match` values kept, and at a candidate
its tally kept: a node with a snapshot pending is a follower, `promotable`), with an empty tally
(`FollowerVotesOk`: the fresh tracker's `Votes` is empty), the `ConfState` well formed
(`SnapScope`: `Restore` answers the configuration it denotes, `restoreM_wf`, and
`assertConfStatesEquivalent` compares it with `switchToConfig`'s sets), and the snapshot owned
(`EnsureConfState` may write its `AutoLeave`; `raft.Step` holds its message's snapshot whole,
`msgIn`). (2026-10-29, stage U5: stated at `HasLC.hasLC`, as `raft.appliedTo.spec` it calls.) -/
abbrev raft.appliedSnap.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (sp : Loc) (sv : SnapshotM) (cl : CSLists),
  (snapHit s.logst.snap sv.Metadata'.Index' = true ↔ s.logst.sapp = true) →
  s.logst.aps = false →
  uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.prev.index' →
  -- (U0) the tracker's rebuild: a follower with an empty tally, a well-formed `ConfState`
  s.role = .follower →
  s.votes = ∅ →
  cl = sv.Metadata'.ConfState'.lists →
  SnapScope sv cl →
  -- the ghost flags `LogGhOk` reads: `Ready`'s unstable entries accepted (as at every
  -- acknowledgement, `raft.Step`'s premise), and no snapshot pending in the no-snapshot mode
  s.gh.unst = false →
  (s.gh.ns = true → s.logst.snap = none) →
  -- (D22 S-d4 item 3) with a snapshot pending and the storage not lent, the storage holds the log
  -- up to the acknowledged snapshot (`LogState.sxt`: the one its receipt left it at)
  (s.logst.snap ≠ none → s.logst.lent = false → uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.sxt) →
  -- and the snapshot handed out is at most the acknowledged one (it is the one)
  (∀ k, s.gh.snp = some k → uint.Z k.sid.index' ≤ uint.Z sv.Metadata'.Index') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCVW c c.voters r id s ∗
      -- (U0) owned (until then at any fraction)
      "Hsnap" ∷ ownSnapM sp (DFrac.own 1) sv }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"appliedSnap")) (Val #sp))
  {{ (prs : GMap w64 Loc) (pvs : GMap w64 Progress) (il : Bool), RET #(); ownSnapM sp (DFrac.own 1) sv ∗
      ownRaftPhysCV (snapCfg sv cl) (snapCfg sv cl).voters r id
        { s with logst := logAppliedTo (logStableSnap s.logst sv.Metadata'.Index')
                            sv.Metadata'.Index' (W64 0),
                 progress := prs, prvals := pvs, isLearner := il } }}

end spec

end EtcdGrove
end Perennial
