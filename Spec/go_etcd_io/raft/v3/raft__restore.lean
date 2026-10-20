/- Port of election_proof/spec_raft__restore.v (feb5c73d4).

## `r.restore(s)` (`raft.go:1849`, `raft.restore.impl`)

Three exits that matter, in the body's order:

- `s.Metadata.Index <= committed`: obsolete, `false`, nothing changes;
- the log already has `(Term, Index)` (`matchTerm`): `commitTo(Index)` and `false` -- a
  fast-forward of the commit index;
- otherwise `raftLog.restore(s)`, then the tracker rebuilt from the snapshot's
  `ConfState` (`MakeProgressTracker`, `confchange.Restore`, `switchToConfig`,
  `assertConfStatesEquivalent`) and `true`.

Three more are dead under the premises: the node is not a follower
(`becomeFollower(Term+1)`, `false`) -- both callers have just made it one, so `s.role =
.follower`; `r.id` is in none of the `ConfState`'s sets (`false`) -- it is in one of them, `CSLists.Has cl
id` (an incoming voter, a learner or an outgoing voter); and `confchange.Restore` failing (`panic`) -- the `ConfState` is
well formed (`SnapScope`), so `Restore` answers the configuration it denotes (`restoreM_wf`).

`SnapScope sv cl` is the scope for a snapshot, what `Step`'s `"Hsnap"` supplies (since
2026-10-14, reconfiguration stage B8, for any `ConfState`, joint included; until then
non-joint, with fixed voters): the lists `cl` the four slices hold are well formed (`CSWf`:
a voter, no `0` -- `confchange` skips `NodeID = 0` --, a learner no voter, a staged learner
an outgoing voter that is no incoming voter nor learner, no staged learner when not joint),
without repeats (`assertConfStatesEquivalent` compares them sorted with the sets
`switchToConfig` reports), not too many (`slices.Sort`'s bound, and `ownTrackerC`'s on the
progress map), `AutoLeave` off when not joint (`Restore` drops it then, and the comparison
would see it); and the index is below `2^61` (`LogStoreOk`'s bound for a pending snapshot,
`InvRaftlog.lean`). The node itself is one of the ids `found` searches (`CSLists.Has`).

The rebuilt tracker: a fresh, empty `Votes` map -- the tally was already empty
(`s.votes = ∅`: a follower's, `FollowerVotesOk`), so `NState.votes` does not move -- a
fresh progress map over the configuration's ids (`prs`), and `Progress` values `pvs` the
spec does not pin -- a follower's are invisible to the protocol (`toPState`). After a
restore the node is at the configuration the `ConfState` denotes (`snapCfg sv cl`, `csCfgM`).

Lean notes: Rocq's `snap_scope` and `restore_result` are `SnapScope` and
`RestoreResult` (Prop-valued definitions).

raft v3.7 (2026-10-15, stage R4): `s` is a `*pb.Snapshot` (`sp`), owned with its metadata set
(`ownSnapE sp 1 sv`, as `handleSnapshot`'s `EnsureSnapshot` leaves it; `EnsureConfState` may
write a nil field, which reads the same) and given back, the record unchanged (D7: once past the
early exits, its conf state frozen read-only with its `AutoLeave` set, `csOptA`'s third case,
which `ownSnapE` admits); `raftLog.restore` clones it (R3). The lists `cl` are the snapshot record's (`cl = sv.Metadata'.ConfState'.lists`;
until the retarget the caller's read-only slices, `ownCSL`). The `section results` (`SnapScope`,
`CSLists.Has`, `snapCfg`, `RestoreResult`, `restoreCfg`) moved verbatim to
`Proof/.../SpecResults.lean` in R1.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.Plog
public import Proof.go_etcd_io.raft.v3.InvRestore
public import Proof.go_etcd_io.raft.v3.SpecResults

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. At any configuration since 2026-10-14 (reconfiguration stage A3): the
struct at any `c` (`ownRaftPhysCV c c.voters`, joint or not); since B8 (the same day) the
snapshot's `ConfState` any well-formed one, joint included (`SnapScope`, its four slices
read-only, `ownCSL`), with the node one of its ids (`CSLists.Has`); after a restore the node is at
the configuration it denotes, otherwise still at `c` (`restoreCfg`). (Until B8 the `ConfState`
was non-joint with the voters `cfg`, `SnapScope cfg sv voters learners`, and a statement
`specS` with the node's own voters; `specS` had no caller and is gone.) -/
abbrev raft.restore.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (sp : Loc) (sv : SnapshotM) (cl : CSLists),
  s.role = .follower →
  s.votes = ∅ →
  cl = sv.Metadata'.ConfState'.lists →
  cl.Has id →
  SnapScope sv cl →
  -- (2026-10-19, D21 M3) outside the no-snapshot mode, where no snapshot is sent
  s.gh.ns = false →
  -- (2026-10-20, witness support) at a configuration without a witness: `ConfStateM` carries
  -- none yet, so a restore would lose it (notes/raft-witness.md); and of a conf state without one
  c.wit = W64 0 ∧ sv.Metadata'.ConfState'.Witness' = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hsnap" ∷ ownSnapE sp (DFrac.own 1) sv }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"restore")) (Val #sp))
  {{ (b : Bool) (s' : NState), RET #b;
      ownRaftPhysCV (restoreCfg c sv cl b) (restoreCfg c sv cl b).voters r id s' ∗
      ownSnapE sp (DFrac.own 1) sv ∗
      ⌜RestoreResult s sv cl b s'⌝ }}

end spec

end EtcdGrove
end Perennial
