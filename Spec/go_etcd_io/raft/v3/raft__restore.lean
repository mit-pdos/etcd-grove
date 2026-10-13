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
.follower`; `r.id` is in none of the `ConfState`'s sets (`false`) -- the voters are `cfg`
and `id ∈ cfg`; and `confchange.Restore` failing (`panic`) -- its axiom covers the
voters-only, zero-free case.

`SnapScope cfg sv voters` is the fixed-voter-set scope for a snapshot, what `Step`'s
`"Hsnap"` supplies: the `ConfState` is `cfg`'s voters, nothing else (no learners, no
joint configuration, `AutoLeave` off -- `assertConfStatesEquivalent` compares it with
the one `switchToConfig` reports); `cfg` is zero-free (`confchange.Restore` skips
`NodeID = 0`); and the index is below `2^61` (`LogStoreOk`'s bound for a pending
snapshot, `InvRaftlog.lean`).

The rebuilt tracker: a fresh, empty `Votes` map -- the tally was already empty
(`s.votes = ∅`: a follower's, `FollowerVotesOk`), so `NState.votes` does not move -- a
fresh progress map over the same `cfg` (`prs`), and `Progress` values `pvs` the spec
does not pin -- a follower's are invisible to the protocol (`toPState`).

Lean notes: Rocq's `snap_scope` and `restore_result` are `SnapScope` and
`RestoreResult` (Prop-valued definitions).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.Plog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [FfiSyntax]

/-- The fixed-voter-set scope for a snapshot; see the file header. -/
def SnapScope (cfg : GSet w64) (sv : raftpb.Snapshot) (voters : List w64) : Prop :=
  let cs := sv.Metadata'.ConfState'
  voters ≡ₚ elements cfg ∧ W64 0 ∉ cfg ∧
  cs.Learners'.len = W64 0 ∧
  cs.VotersOutgoing'.len = W64 0 ∧
  cs.LearnersNext'.len = W64 0 ∧
  cs.AutoLeave' = false ∧
  uint.Z sv.Metadata'.Index' < 2^61

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

end results

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev raft.restore.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (sv : raftpb.Snapshot) (voters : List w64),
  s.role = .follower →
  s.votes = ∅ →
  id ∈ cfg →
  SnapScope cfg sv voters →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "#Hvoters" ∷ sv.Metadata'.ConfState'.Voters' ↦*□ voters }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"restore")) (Val #sv))
  {{ (b : Bool) (s' : NState), RET #b;
      ownRaftPhys cfg r id s' ∗ ⌜RestoreResult s sv b s'⌝ }}

end spec

end EtcdGrove
end Perennial
