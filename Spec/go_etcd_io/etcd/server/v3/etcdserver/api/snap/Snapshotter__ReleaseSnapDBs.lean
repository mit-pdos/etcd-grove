/-
## `(*Snapshotter).ReleaseSnapDBs(snap)` (`snapshotter.go:45-70`): trusted (names only)

**Users.** `storage.Release` (names only). **Why it is true.** Every `*.snap.db` of a lower index
removed (an unparsable name skipped; a removal error logged: `diskOk`). **Changes**: new.
**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Api
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.Api

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
      (AU <{ ∃∃ (F : Nat → Option BeImage), snapDbs sd F }> @ ⊤, ∅
        <{ snapDbs sd (releaseBelow F (uint.nat sn.index)), COMM Q }>) }}
    (App (Val (ss @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty @!! go!"ReleaseSnapDBs")) (Val #p))
  {{ RET #GoInterface.nil; Raft.snapshotPts p dq sn ∗ Q }}

end spec

end Snap
end EtcdGrove
end Perennial
