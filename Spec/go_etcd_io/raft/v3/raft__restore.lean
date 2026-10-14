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
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.Plog
public import Proof.go_etcd_io.raft.v3.InvRestore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [FfiSyntax]

/-- The scope for a snapshot's `ConfState`; see the file header. -/
def SnapScope (sv : raftpb.Snapshot) (cl : CSLists) : Prop :=
  let cs := sv.Metadata'.ConfState'
  CSWf cl.outgoing cl.voters cl.learners cl.learnersNext ∧
  cl.voters.Nodup ∧ cl.learners.Nodup ∧ cl.outgoing.Nodup ∧ cl.learnersNext.Nodup ∧
  (cl.voters.length + cl.learners.length + cl.outgoing.length + cl.learnersNext.length : Int)
    ≤ 2 ^ 62 ∧
  (cl.outgoing = [] → cs.AutoLeave' = false) ∧
  uint.Z sv.Metadata'.Index' < 2^61

/-- `id` is in one of the sets `restore`'s `found` search reads: an incoming voter, a learner or
an outgoing voter (2026-10-14, reconfiguration stage B8; a staged learner is an outgoing voter,
`CSWf`). -/
def CSLists.Has (cl : CSLists) (id : w64) : Prop :=
  id ∈ cl.voters ∨ id ∈ cl.learners ∨ id ∈ cl.outgoing

/-- The configuration a snapshot's `ConfState` denotes (2026-10-14, reconfiguration stage B8). -/
abbrev snapCfg (sv : raftpb.Snapshot) (cl : CSLists) : CfgM :=
  csCfgM cl.outgoing cl.voters cl.learners cl.learnersNext sv.Metadata'.ConfState'.AutoLeave'

/-- The three exits of `restore`; see the file header. -/
def RestoreResult (s : NState) (sv : raftpb.Snapshot) (b : Bool) (s' : NState) : Prop :=
  let ls := s.logst
  let es := ls.sents ++ ls.uents
  let sid := snapId sv
  (uint.Z sid.index' ≤ uint.Z ls.committed ∧
   b = false ∧ s' = s)
  ∨
  (uint.Z ls.committed < uint.Z sid.index' ∧
   PlogMatches ls.prev es sid ∧ b = false ∧
   s' = { s with logst := { ls with committed := sid.index' } })
  ∨
  (uint.Z ls.committed < uint.Z sid.index' ∧
   ¬ PlogMatches ls.prev es sid ∧ b = true ∧
   ∃ prs pvs il, s' = { s with progress := prs, prvals := pvs, logst := logRestore ls sid,
                               isLearner := il })

/-- The configuration the node is at after `restore` (2026-10-14, reconfiguration stage A3; the
snapshot's any `ConfState`'s since B8): the snapshot's when it restored (`b`), the one it was
at otherwise. -/
def restoreCfg (c : CfgM) (sv : raftpb.Snapshot) (cl : CSLists) (b : Bool) : CfgM :=
  if b then snapCfg sv cl else c

end results

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
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (sv : raftpb.Snapshot) (cl : CSLists),
  s.role = .follower →
  s.votes = ∅ →
  cl.Has id →
  SnapScope sv cl →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "#Hcs" ∷ ownCSL sv.Metadata'.ConfState' cl }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"restore")) (Val #sv))
  {{ (b : Bool) (s' : NState), RET #b;
      ownRaftPhysCV (restoreCfg c sv cl b) (restoreCfg c sv cl b).voters r id s' ∗
      ⌜RestoreResult s sv b s'⌝ }}

end spec

end EtcdGrove
end Perennial
