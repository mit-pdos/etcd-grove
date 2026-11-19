/- Lean-first (no Rocq counterpart).

# The etcd examples' extensions: the request ids' issue record and Linux files (2026-11-15)

Since the WAL's integration into the main tree (branch `wal-lean`), `fileutil` is translated with
its bodies, and its package initializer runs its `init` (lock_linux.go): the `F_OFD_GETLK` probe
through `syscall.FcntlFlock`, whose model is over the Linux file extension (`fsExt`,
`GooseLang/Ext/Fs`). Every etcd program's initialization reaches it through the server, so its
`wp_initialize'` takes `[ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]`, and the etcd examples'
closed theorems (`examples/{etcd,k8s}/*/Adequacy.lean`) run over this list of extensions instead of
`TrivialExt.lean`'s `trivialExts` (`[idIssueExt]`): `[idIssueExt, fsExt]`, as the osfs programs'
results do (`GooseLang/Ext/Fs/Adequacy.lean`'s `fsExts`). Their premise on the file extension's
initial state is `FsInit` (the files as on disk, the roots well formed): each says that the program
runs on a real file system (the user's decision (A), 2026-11-15, `notes/wal-units/lean-integration.md`,
session 3).

**The semantics: no I/O error** (wal-link P2, 2026-11-19; `notes/wal-link-scope.md` §3.4 P2, §6
"Added", Q3 approved by the user 2026-11-17). Since the server's WAL is the real WAL over the file
extension (layer 1), the file extension's semantics is restricted by the premise on steps
`NoIoErr etcdIoAll` (`GooseLang/Ext/Fs/Premises.lean`): no covered call (on any inode, on any path,
`etcdIoAll`) fails with an I/O error when the model has an outcome with errno 0 for it from that state
(`fsSemWithS (NoIoErr etcdIoAll) (fun _ _ => True)`: no premise on crashes, as there is no crash in
these runs). It is an assumption on the environment, which every closed theorem over these
extensions states by being about this semantics: the theorems are about the runs in which no file
system call that can succeed fails. The specs hold over it (`etcdFsExts_semOk`, from
`noIoErr_keeps`), and the WAL's no-error specs use its `FsStepSat` (`etcdFsExts_sat`).
-/
module

public import GooseLang.Ext.IdIssue.Specs
public import GooseLang.Ext.Fs.Ghost
public import GooseLang.Ext.Fs.SemOk
public import GooseLang.Ext.Fs.Adequacy
public import GooseLang.Ext.Fs.NoIoErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- **The etcd examples' extensions**: the request ids' issue record (`idutil`'s `Generator.Next`)
and the Linux file extension (`fileutil`'s package initializer). -/
@[reducible] def etcdFsExts : GooseExts := ⟨[idIssueExt, Fs.fsExt]⟩

attribute [local instance] etcdFsExts

/-- **No I/O error on any file or path** (the closed theorems' premise on the file extension's steps;
see the file header): every inode and every path is covered. -/
def etcdIoAll : Fs.IoSet := ⟨fun _ _ => True, fun _ => True⟩

/-- **The file extension's semantics in the etcd examples** (see the file header): its steps
restricted by `NoIoErr etcdIoAll` (no I/O error on any call that can succeed), no premise on
crashes. -/
@[reducible] def etcdFsSem : ExtSemantics Fs.fsExt :=
  Fs.fsSemWithS (Fs.NoIoErr etcdIoAll) (fun _ _ => True)

/-- Their semantics: the issue record's own, and the file extension's restricted by the no-I/O-error
premise (`etcdFsSem`). -/
@[reducible] def etcdFsExtsSemantics : GooseSemantics := ⟨(idIssue_semantics, etcdFsSem, ⟨⟩)⟩

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
theorem etcdFsExts_hasFs : HasExt Fs.fsExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

/-- The specs hold over the restricted semantics (`noIoErr_keeps`; a local instance of a closed
theorem). -/
theorem etcdFsExts_semOk : Fs.FsSemOk (S := etcdFsSem) :=
  Fs.fsSemWithS_ok _ _ (Fs.noIoErr_keeps _)

/-- Every step of the restricted semantics satisfies the premise (what the WAL's no-error specs use). -/
theorem etcdFsExts_sat : Fs.FsStepSat (Fs.NoIoErr etcdIoAll) (S := etcdFsSem) :=
  Fs.fsSemWithS_sat _ _

attribute [local instance] etcdFsExts_hasFs etcdFsExts_semOk

section start
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The local start resources of `[idIssueExt, fsExt]`: the file extension's (`osStart`). -/
theorem etcdFsExts_localStart [L : GooseLocalGS GF] (w : ExtsLocalState etcdFsExts.exts) :
    extsLocalStart (GF := GF) w ⊢ Fs.osStart (Fs.gooseOsGS (L := L)) (extLocal Fs.fsExt w) :=
  (sep_elim_right (P := iprop(True))).trans sep_elim_left

/-- **The start resources of the file extension** (`fs_start` for `[idIssueExt, fsExt]`): the
invariant of the mapped cells, every file, and the tree's history. -/
theorem etcdFs_start [hG : HeapGS .hasLC GF] (σ : state) (h : Fs.FsInit (extLocal Fs.fsExt σ.world)) :
    ⊢ extsLocalStart (GF := GF) σ.world ={⊤}=∗
      Fs.osInv (L := hG.goose_localGS) ∗
      ([∗map] i ↦ f ∈ (extLocal Fs.fsExt σ.world).fs.files, Fs.osFileStart (L := hG.goose_localGS) i f) ∗
      Fs.osTree (L := hG.goose_localGS) (DFrac.own 1) (extLocal Fs.fsExt σ.world).fs.roots
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
  imodintro
  iframe Hinv
  isplitl [Hfs]
  · iapply BigSepM.bigSepM_mono (fun {i f} _ =>
      (Fs.fileStart_eq (L := hG.goose_localGS) i f).1) $$ Hfs
  · unfold Fs.osTree; iexact Hd

end start

end EtcdGrove
end Perennial
