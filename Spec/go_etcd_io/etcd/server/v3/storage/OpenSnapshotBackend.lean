/-
## `OpenSnapshotBackend(cfg, ss, snapshot, hooks)` (`backend.go:61-70`): translated

**Users.** 2d's `applySnapshot` (a received snapshot installed: the old backend closed first),
`RecoverSnapshotBackend` (`bootstrap`, names only). Snippet: `etcdserverboot/snap.go`.

**Proof sketch.** `ss.DBFilePath(index)` (`Snapshotter.DBFilePath.spec`: the update's read of
`snapDbs`; `ErrNoDBSnapshot`, returned, if there is no file: the update fired with `none`),
`os.Rename` onto `BackendPath()` (trusted, Perennial's `os`: the db file's image moves onto the
path: the update's commit removes it from `snapDbs`; a failure is `diskOk`'s: `applySnapshot` panics
on any error here), `OpenBackend.spec` over the renamed file.

**Changes** (from `specs-ref`'s `OpenSnapshotBackend.lean`, D22 S-f): over the snapshotter's model.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.Api
public import Spec.go_etcd_io.raft.v3.Api
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

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

/-- **Installs the snapshot's database as the backend and opens it.** -/
def OpenSnapshotBackend.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss : Loc) (p : Loc) (dq : DFrac)
    (sn : Raft.Snapshot) (h : Loc) (ci : GoInterface) (o : Option Snap.BeImage)
    (Q : Option Snap.BeImage → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ Zap.isLogger cfg.Logger' ∗ EtcdServer.backendBootRes cfg ∗ ⌜diskOk⌝ ∗
      Snap.isSnapshotter ss (Config.snapDirOf cfg.DataDir') ∗ Raft.snapshotPts p dq sn ∗
      isHooks h ci ∗ Snap.beFile (Config.backendPathOf cfg.DataDir') o ∗
      (AU <{ ∃∃ (F : Nat → Option Snap.BeImage), Snap.snapDbs (Config.snapDirOf cfg.DataDir') F }> @ ⊤, ∅
        <{ Snap.snapDbs (Config.snapDirOf cfg.DataDir')
              (fun j => if j = uint.nat sn.index then none else F j),
            COMM Q (F (uint.nat sn.index)) }>) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.OpenSnapshotBackend)) (Val #cfg)) (Val #ss)) (Val #p)) (Val #h))
  {{ (be : GoInterface) (err : GoInterface), RET (PairV #be #err); Raft.snapshotPts p dq sn ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ img, Q (some img) ∗
          beOpen be (Config.backendPathOf cfg.DataDir') img) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ Q none ∗ Snap.beFile (Config.backendPathOf cfg.DataDir') o)) }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
