/- Lean-first (no Rocq counterpart).

# The etcd examples' extensions: the request ids' issue record and Linux files (2026-11-15)

Since the WAL's integration into the main tree (branch `wal-lean`), `fileutil` is translated with
its bodies, and its package initializer runs its `init` (lock_linux.go): the `F_OFD_GETLK` probe
through `syscall.FcntlFlock`, whose model is over the Linux file extension (`fsExt`,
`GooseLang/Ext/Fs`). Every etcd program's initialization reaches it through the server, so its
`wp_initialize'` takes `[ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]`, and the etcd examples'
closed theorems (`examples/{etcd,k8s}/*/Adequacy.lean`) run over this list of extensions instead of
`TrivialExt.lean`'s `trivialExts` (`[idIssueExt]`): `[idIssueExt, fsExt]`, the extension's own
semantics (`fs_semantics`, every step `FsStep` allows: no premise on the environment; since S3e,
2026-11-17, restricted by `etcdSQ`: no file I/O error, `etcdFsSem`) and ghost state,
as the osfs programs' results do (`GooseLang/Ext/Fs/Adequacy.lean`'s `fsExts`). Their new premise is
the file extension's initial state, `FsInit` (the files as on disk, the roots well formed): each
says that the program runs on a real file system (the user's decision (A), 2026-11-15,
`notes/wal-units/lean-integration.md`, session 3). The probe takes no extension step
(`syscall.FcntlFlock.wp_getlk`), so the programs' proofs need none of the extension's start
resources.
-/
module

public import GooseLang.Ext.IdIssue.Specs
public import GooseLang.Ext.Fs.Ghost
public import GooseLang.Ext.Fs.SemOk
public import GooseLang.Ext.Fs.NoMapLockErr
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- **The etcd examples' extensions**: the request ids' issue record (`idutil`'s `Generator.Next`)
and the Linux file extension (`fileutil`'s package initializer). -/
@[reducible] def etcdFsExts : GooseExts := ⟨[idIssueExt, Fs.fsExt]⟩

attribute [local instance] etcdFsExts

/-- **Every file and every path** (an `IoSet` covering all of them). -/
def allIo : Fs.IoSet := ⟨fun _ _ => True, fun _ => True⟩

/-- **The file system does not fail** (S3e, 2026-11-17, `notes/bbolt-integration-plan.md`, D-I5): no
I/O error (`NoIoErr`) and no error of `flock`, `mmap`, `munmap` (`NoMapLockErr`) on any file or path:
the premise on steps of the etcd examples' closed theorems (the user's accepted "file I/O does not
fail" premise), which bbolt's error-free `Open` and `Close` need (the backend's `theFs` packs it,
`FsNoErrAll`). -/
abbrev etcdSQ : Fs.StepPrem := Fs.StepPrem.and (Fs.NoIoErr allIo) (Fs.NoMapLockErr allIo)

/-- The file extension's semantics here: its steps restricted by `etcdSQ`, its crashes not (the
programs do not crash). Until S3e the extension's own (`Fs.fs_semantics`, no premise). -/
@[reducible] def etcdFsSem : ExtSemantics Fs.fsExt := Fs.fsSemWithS etcdSQ (fun _ _ => True)

/-- Their semantics: the request ids' issue record's, and the file extension's under `etcdSQ`
(`etcdFsSem`; until S3e `Fs.fs_semantics`, every step of the model, with no premise on the
environment). -/
@[reducible] def etcdFsExtsSemantics : GooseSemantics := ⟨(idIssue_semantics, etcdFsSem, ⟨⟩)⟩

/-- The model's facts hold of the restricted semantics (`etcdSQ` keeps steps). -/
theorem etcdFsSemOk : letI := etcdFsSem; Fs.FsSemOk :=
  Fs.fsSemWithS_ok etcdSQ (fun _ _ => True) (Fs.noIoErr_noMapLockErr_keeps allIo allIo)

/-- The restricted semantics' file system does not fail (`backend.FsNoErrAll`, at `allIo`). -/
theorem etcdFsNoErr : letI := etcdFsSem; backend.FsNoErrAll := by
  letI := etcdFsSem
  haveI : Fs.FsStepSat etcdSQ := Fs.fsSemWithS_sat etcdSQ (fun _ _ => True)
  exact ⟨⟨allIo, fun _ _ => trivial, fun _ => trivial,
    Fs.fsStepSat_and_left (Fs.NoIoErr allIo) (Fs.NoMapLockErr allIo),
    Fs.fsStepSat_and_right (Fs.NoIoErr allIo) (Fs.NoMapLockErr allIo)⟩⟩

/-- Their ghost state: each extension's own. -/
@[reducible] def etcdFsExtsInterp : GooseInterp := ⟨(idIssue_interp, Fs.fs_interp, ⟨⟩)⟩

attribute [local instance] etcdFsExtsSemantics etcdFsExtsInterp etcdFsSem

/-- The programs have the issue record (by computation; a local instance of a closed theorem). -/
theorem etcdFsExts_hasIdIssue : HasExt idIssueExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

/-- The programs have the Linux file extension (by computation; a local instance of a closed
theorem). -/
theorem etcdFsExts_hasFs : letI := etcdFsSem; HasExt Fs.fsExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

end EtcdGrove
end Perennial
