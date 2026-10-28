/- Port of election_proof/spec_raft__restore.v (feb5c73d4).

## `r.restore(s)` (`raft.go:1849`, `raft.restore.impl`)

Three exits that matter, in the body's order:

- `s.Metadata.Index <= committed`: obsolete, `false`, nothing changes;
- (D22 S-b, D22j, 2026-10-19) `r.id` in none of the `ConfState`'s sets (the `found` search over
  its voters, learners and outgoing voters; a `nil` `ConfState` has none): `false`, nothing
  changes -- until then excluded by a premise `CSLists.Has cl id`, which no caller could
  discharge for a received snapshot (the message's protocol facts say the receiver is tracked,
  not that the snapshot's `ConfState` names it);
- the log already has `(Term, Index)` (`matchTerm`): `commitTo(Index)` and `false` -- a
  fast-forward of the commit index;
- otherwise `raftLog.restore(s)` and `true`. (Until 2026-10-28, stage U0, the tracker was then
  rebuilt from the snapshot's `ConfState` (`MakeProgressTracker`, `confchange.Restore`,
  `switchToConfig`, `assertConfStatesEquivalent`): the fork's `raft37-goose-lean-a2` moves that to
  `appliedSnap`, the fix of `issues/raft-snapshot-during-apply-stale-confchange.md`.)

One more is dead under the premises: the node is not a follower (`becomeFollower(Term+1)`,
`false`) -- both callers have just made it one, so `s.role = .follower`.

(Since D22 S-b′4, 2026-10-20, the premise is `SnapScopeIf id sv cl`: the scope only once the
lists name the node, which the `!found` exit tests before reading them; `Step` derives it from
the message's certificate.) `SnapScope sv cl` is the scope for a snapshot, what `Step`'s `"Hsnap"` supplied (since
2026-10-14, reconfiguration stage B8, for any `ConfState`, joint included; until then
non-joint, with fixed voters): the lists `cl` the four slices hold are well formed (`CSWf`:
a voter, no `0` -- `confchange` skips `NodeID = 0` --, a learner no voter, a staged learner
an outgoing voter that is no incoming voter nor learner, no staged learner when not joint),
without repeats (`assertConfStatesEquivalent` compares them sorted with the sets
`switchToConfig` reports), not too many (`slices.Sort`'s bound, and `ownTrackerC`'s on the
progress map), `AutoLeave` off when not joint (`Restore` drops it then, and the comparison
would see it); and the index is below `2^61` (`LogStoreOk`'s bound for a pending snapshot,
`InvRaftlog.lean`).

After a restore the node stays at its configuration `c` (2026-10-28, stage U0; until then it was
at the one the `ConfState` denotes, `snapCfg sv cl`, with a rebuilt tracker): the snapshot is the
log's pending one, whose configuration `appliedSnap` installs. The scope `SnapScope` and the empty
tally `s.votes = ∅` were the rebuild's; `restore` no longer reads them, and they stay premises
(the callers have them, and `appliedSnap` takes them) so that the statement moves only in its
postcondition.

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. At any configuration since 2026-10-14 (reconfiguration stage A3): the
struct at any `c` (`ownRaftPhysCV c c.voters`, joint or not); since B8 (the same day) the
snapshot's `ConfState` any well-formed one, joint included (`SnapScope`, its four slices
read-only, `ownCSL`) (since D22 S-b not necessarily naming the node: the `!found` exit refuses it,
`RestoreResult`'s first case); after a restore the node is at
the configuration it denotes, otherwise still at `c` (`restoreCfg`; since 2026-10-28, stage U0,
at `c` in every case: the configuration switches at `appliedSnap`). (Until B8 the `ConfState`
was non-joint with the voters `cfg`, `SnapScope cfg sv voters learners`, and a statement
`specS` with the node's own voters; `specS` had no caller and is gone.) -/
abbrev raft.restore.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (sp : Loc) (sv : SnapshotM) (cl : CSLists),
  s.role = .follower →
  s.votes = ∅ →
  cl = sv.Metadata'.ConfState'.lists →
  SnapScopeIf id sv cl →
  -- (2026-10-19, D21 M3) outside the no-snapshot mode, where no snapshot is sent
  s.gh.ns = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      -- (D22 S-d4 item 4) every pointer field set (`handleSnapshot`'s `EnsureSnapshot`)
      "Hsnap" ∷ ownSnapS sp (DFrac.own 1) sv ∗
      -- (D22 S-b′3, 2026-10-20) the snapshot certified in the storage's registry (it joins the
      -- log's `ksn`, `raftLog.restore`)
      "#Hcert" ∷ storCert s.logst.storage (snapTrip sv sv.Metadata'.ConfState'.lists) }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"restore")) (Val #sp))
  {{ (b : Bool) (s' : NState), RET #b;
      ownRaftPhysCV c c.voters r id s' ∗
      ownSnapE sp (DFrac.own 1) sv ∗
      ⌜RestoreResult id s sv cl b s'⌝ }}

end spec

end EtcdGrove
end Perennial
