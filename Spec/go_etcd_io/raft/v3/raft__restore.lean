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
and `id ∈ cfg`; and `confchange.Restore` failing (`panic`) -- its spec covers the
non-joint, zero-free case.

`SnapScope cfg sv voters learners` is the fixed-voter-set scope for a snapshot, what
`Step`'s `"Hsnap"` supplies: the `ConfState`'s voters are `cfg`'s and its learners (since
2026-10-13, reconfiguration stage L; until then none) are outside `cfg`, zero-free and
without repeats; no joint configuration, `AutoLeave` off -- `assertConfStatesEquivalent`
compares it with the one `switchToConfig` reports; `cfg` is zero-free (`confchange.Restore`
skips `NodeID = 0`); and the index is below `2^61` (`LogStoreOk`'s bound for a pending
snapshot, `InvRaftlog.lean`). The node itself is a voter (`id ∈ cfg`: a learner receiving a
snapshot needs the `found` search over the learners, not done).

The rebuilt tracker: a fresh, empty `Votes` map -- the tally was already empty
(`s.votes = ∅`: a follower's, `FollowerVotesOk`), so `NState.votes` does not move -- a
fresh progress map over the same `cfg` and the snapshot's learners (`prs`), and `Progress` values `pvs` the spec
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
def SnapScope (cfg : GSet w64) (sv : raftpb.Snapshot) (voters learners : List w64) : Prop :=
  let cs := sv.Metadata'.ConfState'
  voters ≡ₚ elements cfg ∧ W64 0 ∉ cfg ∧
  -- (2026-10-13, stage L) the learners, none a voter nor `0`, no repeats (`Equivalent`
  -- compares them sorted with the tracker's)
  learners.Nodup ∧ (∀ k ∈ learners, k ∉ cfg ∧ k ≠ W64 0) ∧
  (GMap.size cfg + learners.length : Int) ≤ 2 ^ 62 ∧
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

/-- The configuration the node is at after `restore` (2026-10-14, reconfiguration stage A3):
the snapshot's -- its voters `cfg`, the learners the tracked ids outside them -- when it
restored (`b`), the one it was at otherwise. -/
def restoreCfg (c : CfgM) (cfg : GSet w64) (b : Bool) (s' : NState) : CfgM :=
  if b then CfgM.simple cfg (domSet s'.progress \ cfg) else c

end results

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. At any configuration since 2026-10-14 (reconfiguration stage A3): the
struct at any `c` (`ownRaftPhysCV c c.voters`, joint or not); the snapshot's configuration is
non-joint with the voters `cfg` (`SnapScope`), which need not be `c`'s; after a restore the node
is at the snapshot's configuration, otherwise still at `c` (`restoreCfg`). A joint snapshot
`ConfState` is out of scope (`SnapScope`: `confchange.Restore`'s spec covers the non-joint
case only). The old statement (the snapshot's voters the node's) is `raft.restore.specS`. -/
abbrev raft.restore.spec : Prop :=
  ∀ (c : CfgM) (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (sv : raftpb.Snapshot) (voters learners : List w64),
  s.role = .follower →
  s.votes = ∅ →
  id ∈ cfg →
  SnapScope cfg sv voters learners →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "#Hvoters" ∷ sv.Metadata'.ConfState'.Voters' ↦*□ voters ∗
      "#Hlearners" ∷ ownIdList sv.Metadata'.ConfState'.Learners' DFrac.discard learners }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"restore")) (Val #sv))
  {{ (b : Bool) (s' : NState), RET #b;
      ownRaftPhysCV (restoreCfg c cfg b s') (restoreCfg c cfg b s').voters r id s' ∗
      ⌜RestoreResult s sv b s'⌝ }}

/-- The statement until 2026-10-14: the snapshot's voters are the node's, `cfg`. -/
abbrev raft.restore.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (sv : raftpb.Snapshot) (voters learners : List w64),
  s.role = .follower →
  s.votes = ∅ →
  id ∈ cfg →
  SnapScope cfg sv voters learners →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "#Hvoters" ∷ sv.Metadata'.ConfState'.Voters' ↦*□ voters ∗
      "#Hlearners" ∷ ownIdList sv.Metadata'.ConfState'.Learners' DFrac.discard learners }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"restore")) (Val #sv))
  {{ (b : Bool) (s' : NState), RET #b;
      ownRaftPhys cfg r id s' ∗ ⌜RestoreResult s sv b s'⌝ }}

open Iris.ProofMode in
theorem raft.restore.spec_simple
    (H : raft.restore.spec (GF := GF) (hG := hG)) :
    raft.restore.specS (GF := GF) (hG := hG) := by
  intro cfg r id s sv voters learners Hrole Hvotes Hin Hscope
  iintro %Φ ⟨#Hpkg, Hphys, #Hvoters, #Hlearners⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ cfg r id s sv voters learners Hrole Hvotes Hin Hscope
    $$ [$Hpkg $Hphys $Hvoters $Hlearners]
  inext
  iintro %b %s' ⟨Hphys, %Hres⟩
  cases b
  · simp only [restoreCfg, Bool.false_eq_true, ↓reduceIte]
    ihave Hphys := ownRaftPhysC_toS $$ Hphys
    iapply HΦ
    iframe Hphys
    ipureintro; exact Hres
  · simp only [restoreCfg, ↓reduceIte]
    ihave Hphys := ownRaftPhysC_toS $$ Hphys
    iapply HΦ
    iframe Hphys
    ipureintro; exact Hres

end spec

end EtcdGrove
end Perennial
