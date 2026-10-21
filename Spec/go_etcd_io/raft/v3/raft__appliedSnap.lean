/- (D22 S-d2, 2026-10-21) Lean-first. -/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `r.appliedSnap(snap)` (`raft.go:766`):

    index := snap.GetMetadata().GetIndex()
    r.raftLog.stableSnapTo(index)
    r.appliedTo(index, 0 /* size */)

The acknowledgement of a snapshot's `Ready` (`MsgStorageAppendResp`'s `Snapshot`, both of
`Step`'s arms): the pending snapshot is dropped if it is the acknowledged one (`logStableSnap`)
and `applied` moves to the snapshot's index (`logAppliedTo`). The raft struct comes in the
acknowledgement's windows (`ownRaftPhysCVW`) and leaves quiet.

Premises: the hit happens exactly in the `sapp` window (`raftLog.stableSnapTo`'s: the storage
holds the snapshot, the application's receipt absorbed), not in `appliedSnap`'s own window, the
snapshot at or below the log's boundary (it is the pending one, or older: a second restore since
the `Ready`) -- which gives `appliedTo`'s guard (`index ≤ committed`) and keeps `applying` below
`offsetInProgress` -- `appliedTo`'s auto-leave premise, and the two ghost flags of `LogGhOk`. -/
abbrev raft.appliedSnap.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (sp : Loc) (dq : DFrac) (sv : SnapshotM),
  (snapHit s.logst.snap sv.Metadata'.Index' = true ↔ s.logst.sapp = true) →
  s.logst.aps = false →
  uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.prev.index' →
  (c.autoLeave = true → s.role ≠ .leader) →
  -- the ghost flags `LogGhOk` reads: `Ready`'s unstable entries accepted (as at every
  -- acknowledgement, `raft.Step`'s premise), and no snapshot pending in the no-snapshot mode
  s.gh.unst = false →
  (s.gh.ns = true → s.logst.snap = none) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCVW c c.voters r id s ∗ "Hsnap" ∷ ownSnapM sp dq sv }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"appliedSnap")) (Val #sp))
  {{ RET #(); ownSnapM sp dq sv ∗
      ownRaftPhysCV c c.voters r id
        { s with logst := logAppliedTo (logStableSnap s.logst sv.Metadata'.Index')
                            sv.Metadata'.Index' (W64 0) } }}

end spec

end EtcdGrove
end Perennial
