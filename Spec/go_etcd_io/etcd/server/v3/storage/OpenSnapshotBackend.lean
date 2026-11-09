/-
## `OpenSnapshotBackend(cfg, ss, snapshot, hooks)` (`backend.go:61-70`): translated

**Users.** 2d's `applySnapshot` (a received snapshot installed: the old backend closed first),
`RecoverSnapshotBackend` (`bootstrap`, names only). Snippet: `etcdserverboot/snap.go`.

**Proof sketch.** `ss.DBFilePath(index)` (`Snapshotter.DBFilePath.spec`, its update a read of
`snapDbs` that fires nothing of the caller's: an atomic update read-only on the client's side is
built from the caller's by peeking, i.e. opened and closed with the state unchanged;
`ErrNoDBSnapshot`, returned: the caller's update then fired at that read with `none`, the state
unchanged since `releaseAt F i = F` when `F i = none`), its path `Snap.dbPathOf sd index`;
`os.Rename` of that path onto `BackendPath()` (`Snap.dbFile_rename.spec`, the trusted bridge from
`os.Rename` to the snapshotter's model: the caller's update fires at the rename, the image
`F index` is the backend file's; a missing file, if a concurrent release removed it, is the
`none` arm), `OpenBackend.spec` over the renamed file (its allocation step the caller's).

**Changes** (from `specs-ref`'s `OpenSnapshotBackend.lean`, D22 S-f): over the snapshotter's model.
Verify-round (A8 provability F5): over 4a's `New` (as `OpenBackend`'s); the rename through
`Snap.dbFile_rename` (the round-1 sketch cited a spec of `os.Rename` over OsFs that says nothing of
`snapDbs`); the removal recorded in `Snap.snapGone` (the rename is not fsynced: F9).

Last pass (backend-schema's request): the rename's revert state. Re-review (R-A8 N3): the backend
file and its revert state are taken inside the rename's update (`Snap.dbFile_rename`): the caller's
invariant holds them, the update moves the previous file into the revert list
(`Snap.revertSt path (o :: os)`), and the call holds only the renamed file, which `New` takes. A
concurrent `SaveDBFrom` can settle the revert state meanwhile; two installs in a row extend the list;
a crash inside the call finds the file and the revert state in the invariant.

Verify round, crash pass: `Snap.revertSt` is 4a's list form `Backend.beRevs` (the transitional
`False` for two or more pending renames is gone), so a second install before a directory sync is
provable (R-A8 N3's list form). The one crash window left is inside `New` (`OpenBackend`'s recorded
gap). Statement unchanged.

Changes: verify-round (repair3-boot, the crash pass's request 1): the rename's update now also puts
the renamed file (`beFile path (some img)`) in the caller's state, beside the revert list, and the
caller's continuation `Q (some img)` gives `OpenBackend`'s `Backend.beOpenUpd` of it (4a's `New`
fires it at bbolt's open) with the allocation step over its `R γ`. So the renamed file is never in
the call alone: a crash between the rename and the open finds it in the caller's state (the
re-review's text said so of the old statement, which kept it in the call). The window is closed.

**Margin.** The error's cause is not stated.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.Api
public import Spec.go_etcd_io.raft.v3.Api
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Perennial.ProgramLogic.Bounds

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

/-- **Installs the snapshot's database as the backend and opens it**: the db file of the
snapshot's index renamed onto the backend's path (the caller's update at the rename), then 4a's
`New` over it with the caller's allocation step at that image. -/
def OpenSnapshotBackend.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss : Loc) (p : Loc) (dq : DFrac)
    (sn : Raft.Snapshot) (h : Loc) (ci : GoInterface) (o : Option Snap.BeImage)
    (Bs : Backend.BktInfo → Prop) (Fh : Backend.Fp) (Pk K R : Backend.BeNames → IProp GF)
    (Q : Option Snap.BeImage → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ Zap.isLogger cfg.Logger' ∗ EtcdServer.backendBootRes cfg ∗
      ⌜diskOk ∧ cfg.MemoryMlock' = false ∧ Backend.bktsOk Bs⌝ ∗ Backend.envOk ∗ Backend.safeRegOk ∗
      threadTok ∗ Snap.isSnapshotter ss (Config.snapDirOf cfg.DataDir') ∗ Raft.snapshotPts p dq sn ∗
      isHooks h ci ∗
      (AU <{ ∃∃ (F : Nat → Option Snap.BeImage) (H : Nat → Snap.BeImage → Prop) (o : Option Snap.BeImage)
                (os : List (Option Snap.BeImage)),
              Snap.snapDbs (Config.snapDirOf cfg.DataDir') F ∗ Snap.snapGone (Config.snapDirOf cfg.DataDir') H ∗
              Backend.beFile (Config.backendPathOf cfg.DataDir') o ∗
              Snap.revertSt (Config.backendPathOf cfg.DataDir') os }> @ ⊤, ∅
        <{ Snap.snapDbs (Config.snapDirOf cfg.DataDir') (Snap.releaseAt F (uint.nat sn.index)) ∗
            Snap.snapGone (Config.snapDirOf cfg.DataDir') (Snap.goneAdd H F (Snap.releaseAt F (uint.nat sn.index))) ∗
            (match F (uint.nat sn.index) with
             | some img => Backend.beFile (Config.backendPathOf cfg.DataDir') (some img) ∗
                 Snap.revertSt (Config.backendPathOf cfg.DataDir') (o :: os)
             | none => Backend.beFile (Config.backendPathOf cfg.DataDir') o ∗
                 Snap.revertSt (Config.backendPathOf cfg.DataDir') os),
            COMM Q (F (uint.nat sn.index)) }>) ∗
      (∀ (img : Snap.BeImage), Q (some img) -∗
        Backend.beOpenUpd (Config.backendPathOf cfg.DataDir') (some img) cfg.UnsafeNoFsync' R ∗
        ∀ γ : Backend.BeNames, R γ -∗ Backend.beNew γ img ={⊤}=∗
          Pk γ ∗ Backend.hookOk γ (hooksIface h) Fh (Pk γ) ∗ Backend.commitOk γ (Pk γ) ∗ K γ) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.OpenSnapshotBackend)) (Val #cfg)) (Val #ss)) (Val #p)) (Val #h))
  {{ (be : GoInterface) (err : GoInterface), RET (PairV #be #err); Raft.snapshotPts p dq sn ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (b : Loc) (γ : Backend.BeNames), ⌜be = Backend.beIface b⌝ ∗
          Backend.isBackend γ b (Config.backendPathOf cfg.DataDir') (Pk γ) ∗ K γ ∗ Backend.beHookFp γ Fh ∗
          (□ ∀ bi, ⌜Bs bi⌝ -∗ Backend.beBkt γ bi) ∗ Backend.beDurInv γ (Config.backendPathOf cfg.DataDir') ∗
          (if cfg.UnsafeNoFsync' then iprop(True) else Backend.beSynced γ)) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ Q none ∗ threadTok)) }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
