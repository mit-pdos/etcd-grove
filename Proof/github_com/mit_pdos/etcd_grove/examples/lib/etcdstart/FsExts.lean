/- Lean-first (no Rocq counterpart).

# The etcd examples' extensions: the request ids' issue record and Linux files (2026-11-15)

Since the WAL's integration into the main tree (branch `wal-lean`), `fileutil` is translated with
its bodies, and its package initializer runs its `init` (lock_linux.go): the `F_OFD_GETLK` probe
through `syscall.FcntlFlock`, whose model is over the Linux file extension (`fsExt`,
`GooseLang/Ext/Fs`). Every etcd program's initialization reaches it through the server, so its
`wp_initialize'` takes `[ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]`, and the etcd examples'
closed theorems (`examples/{etcd,k8s}/*/Adequacy.lean`) run over this list of extensions instead of
`TrivialExt.lean`'s `trivialExts` (`[idIssueExt]`): `[idIssueExt, fsExt]`, the extension's own
semantics (`fs_semantics`, every step `FsStep` allows: no premise on the environment) and ghost state,
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

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- **The etcd examples' extensions**: the request ids' issue record (`idutil`'s `Generator.Next`)
and the Linux file extension (`fileutil`'s package initializer). -/
@[reducible] def etcdFsExts : GooseExts := ⟨[idIssueExt, Fs.fsExt]⟩

attribute [local instance] etcdFsExts

/-- Their semantics: each extension's own (`Fs.fs_semantics`: every step of the file extension's
model, with no premise on the environment). -/
@[reducible] def etcdFsExtsSemantics : GooseSemantics := ⟨(idIssue_semantics, Fs.fs_semantics, ⟨⟩)⟩

/-- Their ghost state: each extension's own. -/
@[reducible] def etcdFsExtsInterp : GooseInterp := ⟨(idIssue_interp, Fs.fs_interp, ⟨⟩)⟩

attribute [local instance] etcdFsExtsSemantics etcdFsExtsInterp

/-- The programs have the issue record (by computation; a local instance of a closed theorem). -/
theorem etcdFsExts_hasIdIssue : HasExt idIssueExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

/-- The programs have the Linux file extension (by computation; a local instance of a closed
theorem). -/
theorem etcdFsExts_hasFs : HasExt Fs.fsExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

end EtcdGrove
end Perennial
