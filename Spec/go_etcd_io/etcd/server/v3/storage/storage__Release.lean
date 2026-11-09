/-
## `(*storage).Release(snap)` (`storage.go:59-68`): trusted (names only)

**Users.** The apply thread's `snapshot` (after `SaveSnap` of the same snapshot) and the raft loop
(after saving a received snapshot) (2d).

**Why it is true.** `WAL.ReleaseLockTo(index)` unlocks the files wholly below the record's file,
which the purge may then delete (`Wal.Recs.release`: what is below `index` may be gone), then
`Snapshotter.ReleaseSnapDBs` removes the db files of lower indices (`Snap.releaseBelow`). Sound
only if a snapshot record at `index` was saved (else a restart would open at a purged record: the
WAL API's critique 2, `walBaseLb`): the update's premise.

**Changes** (from `specs-ref`'s `storage__Release.lean`, which lacked `walBaseLb`: the sweep's
"latent gap"): the saved record is the premise. **Margin.** One update for both effects.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.Api
public import Spec.go_etcd_io.raft.v3.Api
public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ServerStorage

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **Releases the WAL files and snapshot dbs below a saved snapshot.** -/
def storage.Release.spec : Prop :=
  ∀ (s : Loc) (wd sd : GoString) (q : Qp) (p : Loc) (dq : DFrac) (sn : Raft.Snapshot)
    (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ isStorage s wd sd ∗ storageOpen s q ∗ Raft.snapshotPts p dq sn ∗ ⌜diskOk⌝ ∗
      (AU <{ ∃∃ (R : Wal.Recs) (F : Nat → Option Snap.BeImage),
              Wal.walRecs wd R ∗ Snap.snapDbs sd F ∗ ⌜∃ w ∈ R.snaps, w.index = sn.index⌝ }> @ ⊤, ∅
        <{ Wal.walRecs wd (R.release (uint.nat sn.index)) ∗
            Snap.snapDbs sd (Snap.releaseBelow F (uint.nat sn.index)), COMM Q }>) }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!! go!"Release")) (Val #p))
  {{ RET #GoInterface.nil; storageOpen s q ∗ Raft.snapshotPts p dq sn ∗ Q }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
