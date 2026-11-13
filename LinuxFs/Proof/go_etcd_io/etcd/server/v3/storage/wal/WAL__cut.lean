/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__cut.lean` (W2).
**Unfinished (`sorry`).** The steps (S/wal.go:875-965) and what each needs:
1. `w.tail().Seek(0, SeekCurrent)`, `Truncate(off)`: the tail's whole `OsMeta`, half of which is
   `walInv`'s (`segRes`): a crash-aware truncate opening `walInv` around the step (W6's tail
   write, `wal-save2`; the stream stops at its end with or without the zeros after it).
2. `w.sync()` (`WAL.sync.spec`): `walSyncedLb |H|`, the layout's synced offset raised.
3. the name: `w.seq()`, `max(w.enti, w.snapi) + 1`, `walName` (`fmt.SprintfWalName`), `filepath.Join`.
4. `w.fp.Open()` (`CutPipe.lean`'s `wp_walPipeH_open`, over `filePipeline.Open.spec`, proved): `pipeQ j n` from the handle's `walPipeH`
   (the claim on `pipeTmp (n + 1)`, `n + 1 < 2^63` from the spec's bound and `n ≤ cuts.length`),
   giving `pipeFile j dir n lf` (`N.tmp` whole, zeros, its claim) and `pipeMain γ (n + 1)`.
5. `w.locks = append(...)`, `newFileEncoder(N.tmp, prevCrc)`, `saveCrc`, `encode(Metadata)`,
   `saveState`, `w.sync()`: **over a tail that is the owned `N.tmp`**, not a crash-tracked segment:
   `walHandleIn`'s tail is the last segment, so `sync`/`saveState` need a second mode (the W2 log's
   "(b) the cut's `N.tmp`, owned wholly"), or the cut's proof inlines them over
   `encoder.encode.specG`/`saveCrc.spec` with the whole-resource bridge `os.File.writerStream`
   and `Fdatasync` (zeros `zrun_synced`).
6. `os.Rename(N.tmp, fpath)` (`os.Rename.specFileSnc`, two claims: `pipeTmp n`'s and the WAL
   directory's `WalDirClaim`): the client update opens `walInv` and takes the layout to `cutLay`
   with `alt = some lay` (`crashOkA_cut`, `cutLay_abs`); `N.tmp`'s halves deposited (`segRes`).
7. `fileutil.Fsync(w.dirFile)` (`os.File.Sync.specDirS`: `osCommitLb n`): `walInv` opened after
   the step (`wp_notCrashed_acc`) to drop `alt` (`crashOk_dirSync`).
8. `newTail.Close()`, `fileutil.LockFile(fpath, O_WRONLY)` (an open of an existing `.wal` file in
   shared mode: `os.OpenFile.wp_fileS`), `Seek(off)`, `w.locks[last] = newTail`,
   `newFileEncoder`, the log line.
The handle after (`walPipeH_next`, `tmpClaim_absent`): `walPipeH fp dir (cuts.length + 1)` from
`pipeMain γ (n + 1)` and the claim the
next `Open` hands back, on `pipeTmp (n + 2) = pipeTmp n` (`pipeTmp_add_two`): the renamed name's,
now absent, which is what the rename leaves.
Also open: `walHandleIn`'s non-tail locks (`walLockH`: an exclusive `LockedFile.File` field) versus
`LockFile`'s persistent `fileutil.lockedFile`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cut
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveState
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeG
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__Open
public import LinuxFs.Spec.os.Rename
public import LinuxFs.Spec.os.File__SyncS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.cut.wp_proof (P : WalPbIn GF) (Mr : WalMarshal)
    (_wp_sync : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr)
    (_wp_saveState : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.spec (W := W) P Mr)
    (_wp_saveCrc : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveCrc.spec (GF := GF) (hG := hG))
    (_wp_encode : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specG (GF := GF) (hG := hG))
    (_wp_Open : go_etcd_io.etcd.server.v3.storage.wal.filePipeline.Open.spec (GF := GF) (hG := hG))
    (_wp_Rename : os.Rename.specFileSnc (GF := GF) (hG := hG))
    (_wp_SyncDir : os.File.Sync.specDirS (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.cut.spec (W := W) P Mr := by
  sorry

end proof

end EtcdGrove
end Perennial
