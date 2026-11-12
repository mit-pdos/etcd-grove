/-
## `(*Snapshotter).ReleaseSnapDBs(snap)` (`snapshotter.go:45-70`): trusted (names only)

**Users.** `storage.Release` (names only). **Why it is true.** The directory opened and listed
(an error returned: `diskOk`'s, as `storage.Release`'s callers panic on it), every `*.snap.db` of a
lower index removed (an unparsable name skipped; a removal error other than a missing file only
logged: `diskOk`'s), no directory fsync: the removed images join `snapGone` (a crash may bring them
back). The update fires before the first removal (a crash after some removals leaves a directory
`snapCrashed` allows).
**Changes**: new. Verify-round (A8 provability F7, F9): `snapGone` (the removals are not durable);
`diskOk`'s failures named. **Margin.** One update for all the removals (a concurrent `DBFilePath`
of an index below may see the file until its removal; no caller does that).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Api
public import SpecPlan.Spec.go_uber_org.zap.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Snap

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]

/-- **Removes the database snapshots below the snapshot's index.** -/
def Snapshotter.ReleaseSnapDBs.spec : Prop :=
  ∀ (ss : Loc) (sd : GoString) (p : Loc) (dq : DFrac) (sn : Raft.Snapshot) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗ isSnapshotter ss sd ∗ Raft.snapshotPts p dq sn ∗ ⌜ServerStorage.diskOk⌝ ∗
      (AU <{ ∃∃ (F : Nat → Option BeImage) (H : Nat → BeImage → Prop), snapDbs sd F ∗ snapGone sd H }> @ ⊤, ∅
        <{ snapDbs sd (releaseBelow F (uint.nat sn.index)) ∗
            snapGone sd (goneAdd H F (releaseBelow F (uint.nat sn.index))), COMM Q }>) }}
    (App (Val (ss @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty @!! go!"ReleaseSnapDBs")) (Val #p))
  {{ RET #GoInterface.nil; Raft.snapshotPts p dq sn ∗ Q }}

end spec

end Snap
end EtcdGrove
end Perennial
