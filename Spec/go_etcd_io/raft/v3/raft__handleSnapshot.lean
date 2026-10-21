/- Port of election_proof/spec_raft__handleSnapshot.v (feb5c73d4).

## `r.handleSnapshot(m)` (`raft.go:1827`, `raft.handleSnapshot.impl`)

    var s pb.Snapshot
    if m.Snapshot != nil { s = *m.Snapshot }
    if r.restore(s) {
        r.logger.Infof(...)
        r.send(pb.Message{To: m.From, Type: pb.MsgAppResp, Index: r.raftLog.lastIndex()})
    } else {
        r.logger.Infof(...)
        r.send(pb.Message{To: m.From, Type: pb.MsgAppResp, Index: r.raftLog.committed})
    }

The three exits of `RestoreResult`, each with its acknowledgement (`appResp`,
accepting): the old commit index when the snapshot is obsolete, and the snapshot's index
after a fast-forward (the new commit index) or a restore (the new last index).
`m.Snapshot` points to `sv` (`↦□`: the receiver only reads it), so the `nil` arm is
dead; the premises are `restore`'s.

Lean notes: Rocq's `handle_snap_result` is `HandleSnapResult` (a Prop-valued
definition). The Rocq `let to := …` is `dst`.

raft v3.7 (2026-10-15, stage R4): `s := pb.EnsureSnapshot(m.GetSnapshot())` and `r.restore(s)`
on the pointer. `m` is a `*pb.Message` (`ml`), taken as `stepFollower`/`stepCandidate` pass it
(`msgIn ml □`, its snapshot owned) and not given back: the message holds the snapshot `sv` (`sn =
some sv`), which `EnsureSnapshot` returns with its metadata set and `restore` takes and gives
back; the lists `cl` are its `ConfState`'s (`cl = sv.Metadata'.ConfState'.lists`; until the
retarget the read-only slices, `ownCSL`). Every reply shares `m`'s `From` cell.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__restore
public import Spec.go_etcd_io.raft.v3.raft__handleAppendEntries

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [FfiSyntax]

/-- The three exits; see the file header. -/
def HandleSnapResult (id : w64) (s : NState) (m : MessageM)
    (sv : SnapshotM) (cl : CSLists) (s' : NState) : Prop :=
  let ls := s.logst
  let es := ls.sents ++ ls.uents
  let sid := snapId sv
  let dst := m.From'
  (uint.Z sid.index' ≤ uint.Z ls.committed ∧
   s' = sendMsgs s [appResp id s dst false ls.committed (W64 0) (W64 0)])
  ∨
  (uint.Z ls.committed < uint.Z sid.index' ∧
   PlogMatches ls.prev es sid ∧
   s' = sendMsgs { s with logst := { ls with committed := sid.index' } }
          [appResp id s dst false sid.index' (W64 0) (W64 0)])
  ∨
  (uint.Z ls.committed < uint.Z sid.index' ∧
   ¬ PlogMatches ls.prev es sid ∧
   ∃ prs pvs il,
     s' = sendMsgs { s with progress := prs, prvals := pvs,
                            logst := logRestore ls (snapTrip sv cl), isLearner := il }
            [appResp id s dst false sid.index' (W64 0) (W64 0)])

/-- (2026-10-19, D21 M3) `handleSnapshot` keeps the no-snapshot mode (`NGhost.ns`). -/
theorem HandleSnapResult.ns {id : w64} {s : NState} {m : MessageM} {sv : SnapshotM} {cl : CSLists}
    {s' : NState} (H : HandleSnapResult id s m sv cl s') : s'.gh = s.gh := by
  unfold HandleSnapResult at H
  rcases H with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, _, _, _, rfl⟩ <;> rfl

/-- Whether `restore` restored the snapshot (its third exit): newer than the commit index, and
its last entry not in the log. -/
def SnapRestores (s : NState) (sv : SnapshotM) : Prop :=
  uint.Z s.logst.committed < uint.Z (snapId sv).index' ∧
  ¬ PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents) (snapId sv)

/-- The configuration after `handleSnapshot` (2026-10-14, reconfiguration stage A3; any
`ConfState`'s since B8): the one the snapshot's `ConfState` denotes after a restore, the old one
`c` otherwise. -/
def SnapCfgOk (c : CfgM) (s : NState) (sv : SnapshotM) (cl : CSLists) (c' : CfgM) :
    Prop :=
  (SnapRestores s sv ∧ c' = snapCfg sv cl) ∨
  (¬ SnapRestores s sv ∧ c' = c)

end results

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. At any configuration since 2026-10-14 (reconfiguration stage A3): the
struct at any `c`; since B8 the snapshot's `ConfState` any well-formed one, joint included, with
the node one of its ids (`restore`'s spec); afterwards the node is at the configuration `c'`
(`SnapCfgOk`). (The statement with the node's own voters, `specS`, had no caller and is gone.) -/
abbrev raft.handleSnapshot.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8)
    (rs : List Loc) (sv : SnapshotM) (cl : CSLists),
  s.role = .follower →
  s.votes = ∅ →
  sn = some sv →
  cl = sv.Metadata'.ConfState'.lists →
  cl.Has id →
  SnapScope sv cl →
  -- from another node (2026-10-10; `Step`'s premise): the reply goes to `m.From`
  m.From' ≠ id →
  -- (2026-10-19, D21 M3) outside the no-snapshot mode (`raft.restore`'s premise)
  s.gh.ns = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"handleSnapshot")) (Val #ml))
  {{ (s' : NState) (c' : CfgM), RET #();
      ownRaftPhysCV c' c'.voters r id s' ∗ ⌜HandleSnapResult id s m sv cl s'⌝ ∗
      ⌜SnapCfgOk c s sv cl c'⌝ }}

end spec

end EtcdGrove
end Perennial
