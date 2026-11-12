/- (D22 S-d1b, 2026-10-21) Lean-first. -/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

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

/-- `l.stableSnapTo(i)` (`log.go:369`) is `l.unstable.stableSnapTo(i)`: on a hit (a snapshot
pending at index `i`, `snapHit`) the snapshot is dropped and no longer in progress, and the log's
storage relation is the one with no snapshot pending (`logStableSnap`, `InvReadylog.lean`);
otherwise nothing changes.

The premise is that the hit happens exactly in the `sapp` window (`ownRaftLogW`): a hit needs
the storage to hold the snapshot (the application's receipt absorbed,
`ownRaftLog_absorb_snap`), which is what makes the dropped snapshot the storage's boundary, and
the window closes with it. Go checks only the index. The result is in `appliedSnap`'s window
(`aps`) on a hit: `applied` is still below the boundary until `appliedTo` moves it there. -/
abbrev raftLog.stableSnapTo.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i : w64),
  (snapHit ls.snap i = true ↔ ls.sapp = true) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLogW l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"stableSnapTo")) (Val #i))
  {{ RET #(); ownRaftLogW l (logStableSnap ls i) }}

end spec

end EtcdGrove
end Perennial
