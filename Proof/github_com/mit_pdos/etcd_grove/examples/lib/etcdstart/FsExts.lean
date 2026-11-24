/- Lean-first (no Rocq counterpart).

# The etcd examples' extensions: the request ids' issue record and Linux files (2026-11-15)

Since the WAL's integration into the main tree (branch `wal-lean`), `fileutil` is translated with
its bodies, and its package initializer runs its `init` (lock_linux.go): the `F_OFD_GETLK` probe
through `syscall.FcntlFlock`, whose model is over the Linux file extension (`fsExt`,
`GooseLang/Ext/Fs`). Every etcd program's initialization reaches it through the server, so its
`wp_initialize'` takes `[ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]`, and the etcd examples'
closed theorems (`examples/{etcd,k8s}/*/Adequacy.lean`) run over this list of extensions instead of
`TrivialExt.lean`'s `trivialExts` (`[idIssueExt]`): `[idIssueExt, fsExt]`, the extension's own
semantics restricted by `etcdSQ` (`etcdFsSem`: no file I/O error, no error of `flock`, `mmap`,
`munmap`; S3e, 2026-11-17) and ghost state, as the osfs programs' results do
(`GooseLang/Ext/Fs/Adequacy.lean`'s `fsExts`). Their premise on the file extension's initial state is
`FsInit` (the files as on disk, the roots well formed): each says that the program runs on a real file
system (the user's decision (A), 2026-11-15, `notes/wal-units/lean-integration.md`, session 3).

**The semantics: the file system does not fail** (S3e's `etcdSQ`; since wal-link P2, 2026-11-19, the
server's WAL is the real WAL over the file extension, layer 1, whose no-error specs use the `NoIoErr`
half: `etcdFsExts_sat`, `notes/wal-link-scope.md` §3.4 P2). It is an assumption on the environment,
which every closed theorem over these extensions states by being about this semantics: the theorems are
about the runs in which no file system call that can succeed fails. The specs hold over it
(`etcdFsSemOk`).
-/
module

public import GooseLang.Ext.IdIssue.Specs
public import GooseLang.Ext.Fs.Ghost
public import GooseLang.Ext.Fs.SemOk
public import GooseLang.Ext.Fs.Adequacy
public import GooseLang.Ext.Fs.NoIoErr
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

/-- Every step of the restricted semantics has no I/O error (`etcdSQ`'s first half: what the WAL's
no-error specs use). -/
theorem etcdFsExts_sat : Fs.FsStepSat (Fs.NoIoErr allIo) (S := etcdFsSem) :=
  letI := etcdFsSem
  haveI : Fs.FsStepSat etcdSQ := Fs.fsSemWithS_sat etcdSQ (fun _ _ => True)
  Fs.fsStepSat_and_left (Fs.NoIoErr allIo) (Fs.NoMapLockErr allIo)

/-- Every step of the restricted semantics has no lock or mapping error (`etcdSQ`'s second half: what the
WAL's area carries for `cut`'s lock, `WalA.satL`; wal-fsfix2). -/
theorem etcdFsExts_satL : Fs.FsStepSat (Fs.NoMapLockErr allIo) (S := etcdFsSem) :=
  letI := etcdFsSem
  haveI : Fs.FsStepSat etcdSQ := Fs.fsSemWithS_sat etcdSQ (fun _ _ => True)
  Fs.fsStepSat_and_right (Fs.NoIoErr allIo) (Fs.NoMapLockErr allIo)

attribute [local instance] etcdFsExts_hasFs etcdFsSemOk

section start
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The local start resources of `[idIssueExt, fsExt]`: the file extension's (`osStart`). -/
theorem etcdFsExts_localStart [L : GooseLocalGS GF] (w : ExtsLocalState etcdFsExts.exts) :
    extsLocalStart (GF := GF) w ⊢ Fs.osStart (Fs.gooseOsGS (L := L)) (extLocal Fs.fsExt w) :=
  (sep_elim_right (P := iprop(True))).trans sep_elim_left

/-- **The start resources of the file extension** (`fs_start` for `[idIssueExt, fsExt]`): the
invariant of the mapped cells, every file, and the tree's shared view (`osShared`), nothing logged. -/
theorem etcdFs_start [hG : HeapGS .hasLC GF] (σ : state) (h : Fs.FsInit (extLocal Fs.fsExt σ.world)) :
    ⊢ extsLocalStart (GF := GF) σ.world ={⊤}=∗
      Fs.osInv (L := hG.goose_localGS) ∗
      ([∗map] i ↦ f ∈ (extLocal Fs.fsExt σ.world).fs.files, Fs.osFileStart (L := hG.goose_localGS) i f) ∗
      Fs.osShared (L := hG.goose_localGS) (extLocal Fs.fsExt σ.world).fs.roots
        ((extLocal Fs.fsExt σ.world).fs.treeDur, []) := by
  have Hl := etcdFsExts_localStart (GF := GF) (L := hG.goose_localGS) σ.world
  have hdisk : ∀ i f, (extLocal Fs.fsExt σ.world).fs.files !! i = some f →
      ∃ vs sz, f = Fs.OsFile.ofDisk vs sz := fun i f hf =>
    let ⟨img, sz, _, e⟩ := (h.2.2.2.2.2.2.1 i f hf).2; ⟨img, sz, e⟩
  iintro Hs
  icases Hl $$ Hs with Hs
  unfold Fs.osStart Fs.osStartF Fs.treeStart Fs.bytesMap Fs.metaMap
  icases Hs with ⟨⟨Hb, Hm, Hv⟩, Hd⟩
  ihave Hfs := Fs.start_files (Fs.gooseOsGS (L := hG.goose_localGS)) hdisk $$ [Hb Hm]
  · iframe
  imod Fs.osInv_alloc (L := hG.goose_localGS) ⊤ $$ Hv with #Hinv
  imod Fs.osSwitchKit_open (L := hG.goose_localGS) _ _ ⊤ $$ Hd with Hsh
  imodintro
  iframe Hinv Hsh
  iapply BigSepM.bigSepM_mono (fun {i f} _ =>
    (Fs.fileStart_eq (L := hG.goose_localGS) i f).1) $$ Hfs

end start

end EtcdGrove
end Perennial
