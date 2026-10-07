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
import EtcdGrove.Raft.Spec.raft__restore
import EtcdGrove.Raft.Spec.raft__handleAppendEntries

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
   ∃ prs pvs,
     s' = sendMsgs { s with progress := prs, prvals := pvs, logst := logRestore ls sid }
            [appResp id s dst false sid.index' (W64 0) (W64 0)])

end results

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev raft.handleSnapshot.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (sv : raftpb.Snapshot) (voters : List w64),
  s.role = .follower →
  s.votes = ∅ →
  id ∈ cfg →
  SnapScope cfg sv voters →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "#Hsv" ∷ m.Snapshot' ↦□ sv ∗
      "#Hvoters" ∷ sv.Metadata'.ConfState'.Voters' ↦*□ voters }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"handleSnapshot")) (Val #m))
  {{ (s' : NState), RET #();
      ownRaftPhys cfg r id s' ∗ ⌜HandleSnapResult id s m sv s'⌝ }}

end spec

end EtcdGrove
end Perennial
