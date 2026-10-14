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
def HandleSnapResult (id : w64) (s : NState) (m : raftpb.Message)
    (sv : raftpb.Snapshot) (s' : NState) : Prop :=
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
     s' = sendMsgs { s with progress := prs, prvals := pvs, logst := logRestore ls sid,
                            isLearner := il }
            [appResp id s dst false sid.index' (W64 0) (W64 0)])

/-- Whether `restore` restored the snapshot (its third exit): newer than the commit index, and
its last entry not in the log. -/
def SnapRestores (s : NState) (sv : raftpb.Snapshot) : Prop :=
  uint.Z s.logst.committed < uint.Z (snapId sv).index' ∧
  ¬ PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents) (snapId sv)

/-- The configuration after `handleSnapshot` (2026-10-14, reconfiguration stage A3): the
snapshot's (its voters `cfg`, the learners the tracked ids outside them) after a restore, the
old one `c` otherwise. -/
def SnapCfgOk (c : CfgM) (cfg : GSet w64) (s : NState) (sv : raftpb.Snapshot) (s' : NState)
    (c' : CfgM) : Prop :=
  (SnapRestores s sv ∧ c' = CfgM.simple cfg (domSet s'.progress \ cfg)) ∨
  (¬ SnapRestores s sv ∧ c' = c)

end results

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. At any configuration since 2026-10-14 (reconfiguration stage A3): the
struct at any `c`, the snapshot's non-joint configuration with the voters `cfg` (`restore`'s
spec); afterwards the node is at the configuration `c'` (`SnapCfgOk`). The old statement is
`raft.handleSnapshot.specS`. -/
abbrev raft.handleSnapshot.spec : Prop :=
  ∀ (c : CfgM) (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (sv : raftpb.Snapshot) (voters learners : List w64),
  s.role = .follower →
  s.votes = ∅ →
  id ∈ cfg →
  SnapScope cfg sv voters learners →
  m.From' ≠ id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "#Hsv" ∷ m.Snapshot' ↦□ sv ∗
      "#Hvoters" ∷ sv.Metadata'.ConfState'.Voters' ↦*□ voters ∗
      "#Hlearners" ∷ ownIdList sv.Metadata'.ConfState'.Learners' DFrac.discard learners }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"handleSnapshot")) (Val #m))
  {{ (s' : NState) (c' : CfgM), RET #();
      ownRaftPhysCV c' c'.voters r id s' ∗ ⌜HandleSnapResult id s m sv s'⌝ ∗
      ⌜SnapCfgOk c cfg s sv s' c'⌝ }}

/-- The statement until 2026-10-14: the snapshot's voters are the node's, `cfg`. -/
abbrev raft.handleSnapshot.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (sv : raftpb.Snapshot) (voters learners : List w64),
  s.role = .follower →
  s.votes = ∅ →
  id ∈ cfg →
  SnapScope cfg sv voters learners →
  -- from another node (2026-10-10; `Step`'s premise): the reply goes to `m.From`
  m.From' ≠ id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "#Hsv" ∷ m.Snapshot' ↦□ sv ∗
      "#Hvoters" ∷ sv.Metadata'.ConfState'.Voters' ↦*□ voters ∗
      "#Hlearners" ∷ ownIdList sv.Metadata'.ConfState'.Learners' DFrac.discard learners }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"handleSnapshot")) (Val #m))
  {{ (s' : NState), RET #();
      ownRaftPhys cfg r id s' ∗ ⌜HandleSnapResult id s m sv s'⌝ }}

open Iris.ProofMode in
theorem raft.handleSnapshot.spec_simple
    (H : raft.handleSnapshot.spec (GF := GF) (hG := hG)) :
    raft.handleSnapshot.specS (GF := GF) (hG := hG) := by
  intro cfg r id s m sv voters learners Hrole Hvotes Hin Hscope Hfid
  iintro %Φ ⟨#Hpkg, Hphys, #Hsv, #Hvoters, #Hlearners⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ cfg r id s m sv voters learners Hrole Hvotes Hin Hscope Hfid
    $$ [$Hpkg $Hphys $Hsv $Hvoters $Hlearners]
  inext
  iintro %s' %c' ⟨Hphys, %Hres, %Hc'⟩
  have Hcs : ∃ L, c' = CfgM.simple cfg L := by
    rcases Hc' with ⟨-, h⟩ | ⟨-, h⟩
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  obtain ⟨L, rfl⟩ := Hcs
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  iapply HΦ
  iframe Hphys
  ipureintro; exact Hres

end spec

end EtcdGrove
end Perennial
