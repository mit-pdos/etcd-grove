/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__cut.lean` (W2).
**Unfinished (`sorry` after step 2).** Done: steps 1 (`Seek`, `os.File.Truncate.specWalTail`) and 2
(`WAL.sync.specCut`), both hypotheses (`WAL__cutTail.lean`), with their error exits. Next: step 3 over
`CutName.lean` (`w.seq()` inline: `tail`, `Name`, `filepath.Base` = `baseModel_child_walFileName`,
`parseWALName` = `scanWalName_walFileName`, the `lg.Fatal` branch unreachable; `walName` over
`fmt.SprintfWalName.spec`; `filepath.Join` = `child dir bt`, `join_child`). The steps (S/wal.go:875-965)
and what each needs:
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
6. `os.Rename(N.tmp, fpath)` (`os.Rename.specFileSnc` with `CutAu.lean`'s `walCut_osAUnc`, proved; two claims: `pipeTmp n`'s and the WAL
   directory's `WalDirClaim`): the client update opens `walInv` and takes the layout to `cutLay`
   with `alt = some lay` (`crashOkA_cut`, `cutLay_abs`); `N.tmp`'s halves deposited (`segRes`).
7. `fileutil.Fsync(w.dirFile)` (`os.File.Sync.specDirS`: `osCommitLb n`): `walInv` opened after
   the step (`wp_notCrashed_acc`) to drop `alt` and clear the pending-cut flag: `CutSync.lean`'s
   `walInvBody_cutSynced` (proved; takes the claim's ¼, the key, the tail record and `walCutFrag (some dir)`).
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
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutTail
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutName

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

/-- An offset below ext4's maximum, as a signed word. -/
theorem cut_off_toInt (a b : Nat) (h : a + b ≤ 0xffffffff000) :
    0 ≤ (W64 ((a : Int) + (b : Int))).toInt ∧ (W64 ((a : Int) + (b : Int))).toInt ≤ 0xffffffff000 ∧
      (W64 ((a : Int) + (b : Int))).toInt = a + b := by
  have : (W64 ((a : Int) + (b : Int))).toInt = a + b := by
    word
  omega

theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.cut.wp_proof [os.file.FieldAssumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_TruncTail : os.File.Truncate.specWalTail (W := W) Mr)
    (wp_syncCut : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specCut (W := W) P Mr)
    (_wp_sync : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr)
    (_wp_saveState : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.spec (W := W) P Mr)
    (_wp_saveCrc : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveCrc.spec (GF := GF) (hG := hG))
    (_wp_encode : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specG (GF := GF) (hG := hG))
    (_wp_Open : go_etcd_io.etcd.server.v3.storage.wal.filePipeline.Open.spec (GF := GF) (hG := hG))
    (_wp_Rename : os.Rename.specFileSnc (GF := GF) (hG := hG))
    (_wp_SyncDir : os.File.Sync.specDirS (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.cut.spec (W := W) P Mr := by
  intro R jr r w dir h hrest hst hcnt hcuts hcpos
  wp_start as ⟨#Harea, Hh⟩
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, Hopen, %Hpure⟩
  obtain ⟨hsplit, hfd, hoff, hsz, hpend, hidx, hidx1⟩ := Hpure
  obtain ⟨ls, rfl⟩ := List.getLast?_eq_some_iff.1 Hlt
  rw [List.dropLast_concat]
  wp_auto
  -- step 1: the tail's offset, its truncate
  wp_apply (wp_tail w locks ls lt (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls] as ⟨Hlocks, Hls⟩
  · iframe
  ihave #Hlt0 := Hltf
  iunfold fileutil.lockedFile at Hlt0
  iStructNamed Hlt0
  wp_method_call
  wp_call
  (try wp_auto)
  iunfold walTailW at Htw
  icases Htw with ⟨Hf, Hfdo, Hoff, Htk, %m, %bs, Hm, Hbs, %hmb, Hv⟩
  obtain ⟨ho1, ho2, ho3⟩ := cut_off_toInt h.o0 h.out.length (by omega)
  wp_apply (os.File.Seek.wp_cur f fd name (DFrac.own 1) _ hfd ho1 ho2) $$ [$Hf $Hoff] as ⟨Hf, Hoff⟩
  (try wp_auto)
  wp_apply (wp_tail w locks ls lt (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls] as ⟨Hlocks, Hls⟩
  · iframe
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply (wp_TruncTail R jr r f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out hoff)
    $$ [Hf Hfdo Hoff Htk Hm Hbs Hv] as %terr Htr
  · iframe Harea
    iunfold walTailW
    iframe Hf Hfdo Hoff Htk
    iexists m, bs
    iframe Hm Hbs Hv
    ipureintro; exact hmb
  icases Htr with (⟨%he, Htw⟩ | %he)
  rotate_left
  · rcases terr with ei | _
    rotate_left
    · exact absurd rfl he
    wp_auto
    iapply HΦ
    iright; ipureintro; exact he
  subst he
  wp_auto
  -- step 2: sync
  wp_apply (wp_syncCut R jr r w dir { h with sz := h.o0 + h.out.length } hrest rfl)
    $$ [Hlg Hdir Hdf Hdff Hmd Hsp Hdec Hrc Hns Henti Hsnapi He Henc Htw Hdh Hlocks Hls Hcap Hlks Hfp
      Hpipe Hopen] as %serr Hsy
  · iframe Harea
    iunfold walHandleIn
    iexists lg, df, sp, e, fp, lt, f, mds, locks, ls ++ [lt], fd, dfd, name, dnm, j, rc
    rw [show WalHS.crc Mr { h with sz := h.o0 + h.out.length } = WalHS.crc Mr h from rfl]
    simp only
    iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
      Hlocks Hls Hcap Hltf Hfp Hpipe Henv Hcrc Hopen
    rw [List.dropLast_concat]
    iframe Hlks
    ipureintro
    exact ⟨by simp, hsplit, hfd, Nat.le_refl _, by omega, by omega, hidx, hidx1⟩
  icases Hsy with (⟨%he, Hh, #Hsyn⟩ | %he)
  rotate_left
  · rcases serr with ei | _
    rotate_left
    · exact absurd rfl he
    wp_auto
    iapply HΦ
    iright; ipureintro; exact he
  subst he
  wp_auto
  sorry

end proof

end EtcdGrove
end Perennial
