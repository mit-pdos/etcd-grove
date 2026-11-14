/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__cut.lean` (W2).
**Proved** (no `sorry`), over the hypotheses `os.File.Truncate.specWalTail` and `WAL.sync.specCut` (steps
1-2, to be proved on `wal-tc2` and with W6's `sync`) and the callees' specs. Steps 7-8: the directory fsync
(`fileutil.Fsync.specDirS`) and `CutFin.lean`'s `walInv_cutSynced` at the next step (`wp_notCrashed_acc`);
`Close`, `LockFile` over `openWALFiles.lean`'s `walOpen_triple` (`os.OpenFile.wp_fileS` of the renamed name),
`Seek`, `w.locks[last]`, `Sum32`, `newFileEncoder`, the log line; the new handle at the new segment
(`walPipeH_next`, `tailCrc_cut`, the out-record from `walCutQ`). The steps (S/wal.go:875-965)
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
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutPipe
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PipeLemmas
public import LinuxFs.Spec.os.File__Name
public import LinuxFs.Spec.path.filepath.Base
public import LinuxFs.Spec.path.filepath.Join
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.parseWALName
public import Spec.fmt.SprintfWalName
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutPre
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.digest__Sum32
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PreSync
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutHdr
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutHdrStream
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutRen
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutAu
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutFin
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.openWALFiles
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.FsyncS
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.LockFile
public import LinuxFs.Spec.os.File__Close
public import LinuxFs.Spec.go_uber_org.zap.Logger__Info
public import LinuxFs.Spec.go_uber_org.zap.String
public import LinuxFs.Spec.time.Duration__Seconds
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since
public import GooseLang.Ext.Fs.NotCrashedAcc

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

-- (the proof term's instantiation at the end of the declaration exceeds the default budget)
set_option maxHeartbeats 1000000 in
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
    (wp_FsyncDir : go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.specDirS (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_LockFile : go_etcd_io.etcd.client.pkg.v3.fileutil.LockFile.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_Name : os.File.Name.spec (GF := GF) (hG := hG))
    (wp_Base : filepath.Base.spec (GF := GF) (hG := hG))
    (wp_parse : go_etcd_io.etcd.server.v3.storage.wal.parseWALName.spec (GF := GF) (hG := hG))
    (wp_SprintfWal : fmt.SprintfWalName.spec (GF := GF) (hG := hG))
    (wp_Join : filepath.Join.spec (GF := GF) (hG := hG))
    (wp_Sum32 : go_etcd_io.etcd.pkg.v3.crc.digest.Sum32.spec (GF := GF) (hG := hG))
    (wp_newFileEncoder : go_etcd_io.etcd.server.v3.storage.wal.newFileEncoder.spec (GF := GF)
      (hG := hG))
    (wp_WriteAt : os.File.WriteAt.specLong (GF := GF) (hG := hG))
    (wp_Fdatasync : go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.spec (GF := GF) (hG := hG))
    (wp_syncPreL : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specPreL (GF := GF) (hG := hG))
    (wp_saveStatePre : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.specPre P Mr) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.cut.spec (W := W) P Mr := by
  intro R jr r w dir h hrest hst hcnt hcuts hsorted hcpos hmdsz
  wp_start as ⟨#Harea, Hh⟩
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk, Hopen, %Hpure⟩
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
      Hlocks Hls Hcap Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
    rw [List.dropLast_concat]
    iframe Hlks
    ipureintro
    exact ⟨Hen, by simp, hsplit, hfd, Nat.le_refl _, by omega, by omega, hidx, hidx1⟩
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
  -- the synced handle, a variable
  have hh1e : (cutSynced { h with sz := h.o0 + h.out.length }).H = h.H ∧
      (cutSynced { h with sz := h.o0 + h.out.length }).md = h.md ∧
      (cutSynced { h with sz := h.o0 + h.out.length }).cuts = h.cuts ∧
      (cutSynced { h with sz := h.o0 + h.out.length }).rest = h.rest ∧
      (cutSynced { h with sz := h.o0 + h.out.length }).st = h.st ∧
      (cutSynced { h with sz := h.o0 + h.out.length }).enti = h.enti ∧
      (cutSynced { h with sz := h.o0 + h.out.length }).snapi = h.snapi ∧
      (cutSynced { h with sz := h.o0 + h.out.length }).pc = h.pc ∧
      (cutSynced { h with sz := h.o0 + h.out.length }).pend = [] ∧
      (cutSynced { h with sz := h.o0 + h.out.length }).sz =
        (cutSynced { h with sz := h.o0 + h.out.length }).o0 +
          (cutSynced { h with sz := h.o0 + h.out.length }).out.length :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [cutSynced]; omega⟩
  generalize cutSynced { h with sz := h.o0 + h.out.length } = h1 at hh1e ⊢
  obtain ⟨h1H, h1md, h1cuts, h1rest, h1st, h1enti, h1snapi, h1pc, h1pend, h1sz⟩ := hh1e
  -- step 3: the name
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk, Hopen, %Hpure⟩
  obtain ⟨hsplit, hfd, hoff, hsz, hpend, hidx, hidx1⟩ := Hpure
  obtain ⟨ls, rfl⟩ := List.getLast?_eq_some_iff.1 Hlt
  try rw [h1H]
  try rw [h1md]
  try rw [h1cuts]
  try rw [h1st]
  try rw [h1enti]
  try rw [h1snapi]
  try rw [h1pc]
  try rw [h1pend]
  iunfold walDirH at Hdh
  icases Hdh with ⟨%Rd, %qd, %X, %hj, %nm0, %ph, #Hdk, Hcl, Hpd, #Hsid, Hperm, Hdfd, #Hnamed, Hout, Htf, Hnf, %hdh⟩
  obtain ⟨hnm0w, hnm0c, hname, htmps, hXw, ⟨sq, ix, hnm0, hsq0⟩, hlargest⟩ := hdh
  have hsq : sq + 1 < 2 ^ 64 := by omega
  iunfold walPipeH at Hpipe
  icases Hpipe with ⟨%γp, %Rp, %dqp, %szp, %np, #Hisfp, Hmain, Hpc, %hnp, %hfpn⟩
  ihave #Hisfp' := Hisfp
  iunfold isFilePipe at Hisfp'
  icases Hisfp' with ⟨%plg, -, -, -, -, -, -, -, -, -, -, #Hos, -, #Hpkg, %hszp⟩
  ihave %hclean := osPathS_cleanAbs Rd dir (DFrac.own qd) j $$ Hpd
  wp_auto
  wp_join iprop(∃ nx : w64, next_ptr ↦ nx ∗ w_ptr ↦ w ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"snapi" w ↦ h.snapi ∗
      ⌜uint.nat nx = max (uint.nat h.enti) (uint.nat h.snapi)⌝)
    with [next w Hsnapi] as ⟨%nx, next, w, Hsnapi, %hnx⟩
  · iexists _; iframe; ipureintro; word
  · iexists _; iframe; ipureintro; word
  -- `w.seq()`, inline
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply (wp_tail w locks ls lt (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls] as ⟨Hlocks, Hls⟩
  · iframe
  iclear Hlt0 File
  ihave #Hlt1 := Hltf
  iunfold fileutil.lockedFile at Hlt1
  ihave %hltn := typedPointsto_not_null lt _ _ $$ Hlt1
  iStructNamed Hlt1
  simp only [decide_eq_false hltn]
  (try wp_auto)
  iunfold walTailW at Htw
  icases Htw with ⟨Hf, Hfdo, Hoff, Htk, %m, %bs, Hm, Hbs, %hmb, Hv⟩
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply wp_Name f fd _ _ $$ [$Hf] as Hf
  (try wp_auto)
  wp_apply wp_Base as %bn %hbn
  rw [hname, hnm0, baseModel_child_walFileName] at hbn
  subst hbn
  (try wp_auto)
  obtain ⟨hsuf, hscan⟩ := scanWalName_walFileName sq ix
  wp_apply wp_parse as %sq' %ix' %perr %hpe
  obtain ⟨rfl, rfl, rfl⟩ := hpe.1 _ _ hsuf hscan
  (try wp_auto)
  -- `walName(seq + 1, next + 1)`
  wp_func_call
  wp_call
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go.uint64 #(W64 sq + W64 1), interface.mkOk go.uint64 #(nx + W64 1)]
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  (try wp_auto)
  wp_apply wp_SprintfWal _ _ _ _ $$ [$Hasl] as %bt ⟨-, %hbt⟩
  have hmx : max (uint.nat h.enti) (uint.nat h.snapi) + 1 < 2 ^ 64 := by
    rw [← h1enti, ← h1snapi]; exact hidx1
  rw [cutName_str sq _ nx hsq hmx hnx] at hbt
  subst hbt
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoString)
    [dir, walFileName (sq + 1) (max (uint.nat h.enti) (uint.nat h.snapi) + 1)]
  isplitr
  · ipureintro; rfl
  iintro %jsl ⟨Hjsl, -⟩
  (try wp_auto)
  wp_apply wp_Join _ _ _ (by simp [walFileName_length]; omega) $$ [$Hjsl] as %fpath ⟨%hfpath, -⟩
  rw [join_child hclean (walFileName_nameOk _ _)] at hfpath
  subst hfpath
  (try wp_auto)
  -- step 4: `w.fp.Open()`
  ihave Hpipe : walPipeH fp dir j h.pc $$ [Hmain Hpc]
  · iunfold walPipeH
    iexists γp, Rp, dqp, szp, np
    iframe Hmain Hpc Hisfp
    isplitr
    · ipureintro; exact hnp
    · ipureintro; exact hfpn
  wp_apply (wp_walPipeH_open _wp_Open fp dir j h.pc hcnt) $$ [$Hpipe] as %ntl %oerr Hop
  icases Hop with (⟨%he, %γp, %Rp, %dqp, %szp, %np, #Hisfp, Hmain, Hpf, %hnp⟩ | %he)
  rotate_left
  · rcases oerr with ei | _
    rotate_left
    · exact absurd rfl he
    (try wp_auto)
    iapply HΦ
    iright; ipureintro; exact he
  subst he
  (try wp_auto)
  -- step 5: the headers, on the owned `N.tmp`
  iunfold pipeFile at Hpf
  icases Hpf with ⟨%f2, %fd2, %i2, %m2, %ht, #Hlf2, Hf2, Hoff2, Hfd2, Hm2, Hz2, Hn2, %hpf⟩
  obtain ⟨hfd2, hmaps2, hcur2, hcut2, hlo2, hsz8, hszmax⟩ := hpf
  wp_apply wp_slice_literal (V := Loc) [ntl]
  isplitr
  · ipureintro; rfl
  iintro %l1 ⟨Hl1, -⟩
  wp_apply wp_slice_append $$ [$Hls $Hcap $Hl1] as %locks' ⟨Hls, Hcap, -⟩
  (try wp_auto)
  -- `prevCrc`: the encoder's CRC
  iunfold ownEncoder at Henc
  icases Henc with ⟨%pw0, %hc0, %b0, %u0, %bs0, %us0, #Hmu0, Hbw0, Hpw0, Hcf0, Hdc0, Hb0, Hbs0, %hb0,
    Hu0, Hus0, %hus0⟩
  iunfold ownDecCrc at Hdc0
  icases Hdc0 with ⟨%l0, %tab0, %hl0, Hl0, #Htab0⟩
  subst hl0
  (try wp_auto)
  wp_apply (wp_Sum32 l0 _ tab0 (DFrac.own 1)) $$ [Hl0] as Hl0
  · iexact Hl0
  (try wp_auto)
  -- `w.tail().File`, `newFileEncoder`
  rw [show ls ++ [lt] ++ [ntl] = (ls ++ [lt]) ++ [ntl] by simp]
  wp_apply (wp_tail w locks' (ls ++ [lt]) ntl (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls]
    as ⟨Hlocks, Hls⟩
  · iframe
  ihave #Hlf2' := Hlf2
  iunfold fileutil.lockedFile at Hlf2'
  iStructNamed Hlf2'
  (try wp_auto)
  ihave #Hioi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil $$ []
  · iPkgInit
  wp_apply (wp_newFileEncoder f2 fd2 _ _ (W64 0) _ hfd2 (by decide) (by decide))
    $$ [Hf2 Hoff2] as %e2 ⟨Henc2, Hf2, Hoff2, %he2⟩
  · iframe; iframe #
  (try wp_auto)
  -- the headers' stream over `N.tmp`, from offset 0 (its zeros), bounded by the headers' length
  have hcrc0 : WalHS.crc Mr h1 = tailCrc Mr h.H h.md h.cuts := by
    rw [WalHS.crc_done Mr h1 (by rw [h1rest, hrest]), h1H, h1md, h1cuts]
  have hsorted' : h.cuts.Pairwise (· ≤ ·) := hsorted.imp Nat.le_of_lt
  have hle' : ∀ b ∈ h.cuts, b ≤ h.H.length := fun b hb => Nat.le_of_lt (hcuts b hb)
  have hTS : tailStream Mr h.H h.md (h.cuts ++ [h.H.length]) =
      recFrames walCodec (chainRecs walCodec (tailCrc Mr h.H h.md h.cuts)
        (cutHdrDs Mr h.md (walLastHS (h.H.map WalOpG.toM)))) := by
    rw [tailStream_recs, tailRecs_cut Mr h.H h.md h.cuts hsorted' hle']
  have hL : (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length ≤ 0xffffffff000 := by
    rw [hTS]; exact cutHdrs_fit Mr h.md _ _ (by rw [← hst]; exact hmdsz)
  icases (osZerosA_unfold i2 0 m2.size (DFrac.own 1)).1 $$ Hz2 with ⟨%zs2, %hzs2, Hz2⟩
  ihave HW0 := os.fileW_start f2 fd2 (child dir (pipeTmp np)) (DFrac.own 1) (DFrac.own 1)
    (openFd i2 (wal.walOpenFlag true ||| W64 0x80000)) m2 0 (zs2.map (fun c => ((0 : w8), c)))
    hlo2 (Nat.zero_le _) (by simp [hzs2]) $$ [Hf2 Hfd2 Hoff2 Hm2 Hz2]
  · iframe
  ihave #Hws := os.File.writerStreamI wp_WriteAt f2 fd2 (child dir (pipeTmp np)) (DFrac.own 1)
    (DFrac.own 1) (openFd i2 (wal.walOpenFlag true ||| W64 0x80000)) m2
    (zs2.map (fun c => ((0 : w8), c))) (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length
    hfd2 (by unfold openFd; dsimp only; decide) hmaps2 (by omega) $$ Hos
  ihave #HwsP := (io.writerStream_P _ _ _ _).1 $$ Hws
  ihave HW0' : os.fileWI f2 fd2 (child dir (pipeTmp np)) (DFrac.own 1) (DFrac.own 1)
    (openFd i2 (wal.walOpenFlag true ||| W64 0x80000)) m2 (zs2.map (fun c => ((0 : w8), c))) []
    $$ [HW0]
  · iunfold os.fileWI; iframe; iframe #
  -- the headers' frames, record by record
  have hFr := cutHdrRecs_frames Mr h.md (walLastHS (h.H.map WalOpG.toM)) (WalHS.crc Mr h1)
  rw [← hcrc0] at hTS
  rw [← hTS] at hFr
  generalize hc0 : WalHS.crc Mr h1 = c0 at hFr hTS hL ⊢
  -- `saveCrc(prevCrc)`
  wp_apply (_wp_saveCrc w e2 (wal.fileWi f2) _ _ (fun ys => ys.length ≤
      (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length) [] [] c0 c0
      (fun xs ys hp hy => Nat.le_trans hp.length_le hy) (by rw [hFr]; simp))
    $$ [HwsP] [He Henc2 HW0'] as %serr1 ⟨%pend1, He, Henc2, Hr1⟩
  · iexact HwsP
  · iframe; iframe #
  icases Hr1 with (⟨%ys1, ⟨%he1, %hys1⟩, HW1⟩ | ⟨%a1, %b1, ⟨%he1, -, -⟩, -⟩)
  rotate_left
  · rcases serr1 with ei | _
    rotate_left
    · exact absurd rfl he1
    (try wp_auto)
    iapply HΦ
    iright; ipureintro; exact he1
  subst he1
  (try wp_auto)
  -- `encode(&Record{Type: MetadataType, Data: w.metadata})`
  unfold go_etcd_io.etcd.server.v3.storage.wal.MetadataType
  (try wp_auto)
  imod (typedPointsto_dfractional _ _).dfractional_persist (DFrac.own 1) $$ «$v0» with #Ht1
  have hmdr : recSize (recOf ⟨metadataType, hash.crc32.crc32c (hash.crc32.crc32c c0 []) h.md, h.md⟩)
      < 2 ^ 47 := recSize_hdr _ _ _ (by decide) (by omega)
  wp_apply (_wp_encode e2 (wal.fileWi f2) _ _ (fun ys => ys.length ≤
      (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length) ([] ++ ys1) pend1
      (hash.crc32.crc32c c0 []) «$a0_ptr» metadataType h.md hmdr
      (fun xs ys hp hy => Nat.le_trans hp.length_le hy) (by
        have h1 := congrArg List.length hys1
        rw [hFr]; simp only [List.length_append, List.length_nil] at h1 ⊢; split <;> omega))
    $$ [HwsP] [Henc2 HW1 «$a0»] as %serr2 ⟨%pend2, Henc2, -, Hr2⟩
  · iexact HwsP
  · iframe Henv Henc2 HW1
    iunfold encRecIn
    iexists _
    iframe «$a0»
    have hd : (recOf ⟨metadataType, 0#32, h.md⟩).data = some h.md := by
      simp [recOf, metadataType, crcType]
    rw [hd]
    have hmt : metadataType = W64 1 := rfl
    rw [hmt]
    isplitl
    · iexact Ht1
    isplitr
    · iexact Hmds
    · ipureintro; trivial
  icases Hr2 with (⟨%ys2, ⟨%he2', %hys2⟩, HW2⟩ | ⟨%a2, %b2, ⟨%he2', -, -⟩, -⟩)
  rotate_left
  · rcases serr2 with ei | _
    rotate_left
    · exact absurd rfl he2'
    (try wp_auto)
    iapply HΦ
    iright; ipureintro; exact he2'
  subst he2'
  (try wp_auto)
  -- `saveState(w.state)`
  rw [← hst] at hFr
  have hlen12 := congrArg List.length hys1
  have hlen2 := congrArg List.length hys2
  simp only [List.length_append, List.length_nil] at hlen12 hlen2
  wp_apply (wp_saveStatePre w e2 sp sp h.st (wal.fileWi f2) _ _ (fun ys => ys.length ≤
      (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length) ([] ++ ys1 ++ ys2) pend2
      (hash.crc32.crc32c (hash.crc32.crc32c c0 []) h.md)
      (fun xs ys hp hy => Nat.le_trans hp.length_le hy) (fun hne => by
        refine ⟨?_, recSize_hdr _ _ _ (by decide) (by omega)⟩
        rw [hFr, if_neg hne]; simp only [stateFrame, List.length_append, List.length_nil]; omega))
    $$ [HwsP] [Hsp He Henc2 HW2] as %serr3 ⟨He, Hr3⟩
  · iexact HwsP
  · iframe Henv Hsp He Henc2 HW2 Hst
  ihave Hu : (⌜serr3 = GoInterface.nil⌝ ∗ ∃ (pend3 ys3 : List w8),
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"state" w ↦ sp ∗
      ownEncoder e2 (wal.fileWi f2) (crcAfter walCodec c0 (cutHdrDs Mr h.md h.st)) pend3 ∗
      os.fileWI f2 fd2 (child dir (pipeTmp np)) (DFrac.own 1) (DFrac.own 1)
        (openFd i2 (wal.walOpenFlag true ||| W64 0x80000)) m2 (zs2.map (fun c => ((0 : w8), c)))
        ([] ++ ys1 ++ ys2 ++ ys3) ∗
      ⌜ys3 ++ pend3 = pend2 ++ (if hsEmptyP h.st then [] else stateFrame Mr
        (hash.crc32.crc32c (hash.crc32.crc32c c0 []) h.md) h.st)⌝) ∨ ⌜serr3 ≠ GoInterface.nil⌝
    $$ [Hr3]
  · icases Hr3 with (⟨%hE, Hspf, Henc2, HW3⟩ | ⟨%hNE, Hspf, %pend3, Henc2,
      (⟨%ys3, ⟨%he3, %hys3⟩, HW3⟩ | ⟨%a3, %b3, ⟨%he3, -, -⟩, -⟩)⟩)
    · ileft
      isplitr
      · ipureintro; exact hE.1
      iexists pend2, []
      rw [crcAfter_cutHdrs, if_pos hE.2, List.append_nil]
      iframe
      ipureintro; rw [if_pos hE.2]; simp
    · ileft
      isplitr
      · ipureintro; exact he3
      iexists pend3, ys3
      rw [crcAfter_cutHdrs, if_neg hNE]
      iframe
      ipureintro; rw [if_neg hNE]; exact hys3
    · iright; ipureintro; exact he3
  icases Hu with (⟨%he3, %pend3, %ys3, Hspf, Henc2, HW3, %hys3⟩ | %he3)
  rotate_left
  · rcases serr3 with ei | _
    rotate_left
    · exact absurd rfl he3
    (try wp_auto)
    iapply HΦ
    iright; ipureintro; exact he3
  subst he3
  (try wp_auto)
  -- `w.sync()`: the headers flushed and `N.tmp` fdatasynced
  have hlen3 := congrArg List.length hys3
  simp only [List.length_append] at hlen3
  have hall : ([] ++ ys1 ++ ys2 ++ ys3 ++ pend3) = tailStream Mr h.H h.md (h.cuts ++ [h.H.length]) := by
    calc [] ++ ys1 ++ ys2 ++ ys3 ++ pend3 = ys1 ++ (ys2 ++ (ys3 ++ pend3)) := by simp
      _ = (ys1 ++ (ys2 ++ pend2)) ++ (if hsEmptyP h.st then [] else stateFrame Mr
          (hash.crc32.crc32c (hash.crc32.crc32c c0 []) h.md) h.st) := by rw [hys3]; simp
      _ = ((ys1 ++ pend1) ++ WalEnc.frame (walRecEnc ⟨metadataType,
            hash.crc32.crc32c (hash.crc32.crc32c c0 []) h.md, h.md⟩)) ++
          (if hsEmptyP h.st then [] else stateFrame Mr
            (hash.crc32.crc32c (hash.crc32.crc32c c0 []) h.md) h.st) := by rw [hys2]; simp
      _ = tailStream Mr h.H h.md (h.cuts ++ [h.H.length]) := by
          rw [hys1, hFr]; split <;> simp [stateFrame]
  ihave #Hmds2 := Hmds
  iunfold recBytes at Hmds2
  icases Hmds2 with ⟨%hmdsn, #Hmdsb⟩
  ihave #Hzpk : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  have hlenL : ([] ++ ys1 ++ ys2 ++ ys3).length + pend3.length ≤
      (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length := by
    have := congrArg List.length hall; simp only [List.length_append] at this ⊢; omega
  have hsyncOk := os.fileWI_preSyncOk wp_Fdatasync f2 fd2 (child dir (pipeTmp np)) (DFrac.own 1)
    (DFrac.own 1) (openFd i2 (wal.walOpenFlag true ||| W64 0x80000)) m2
    (zs2.map (fun c => ((0 : w8), c)))
  wp_apply (wp_syncPreL w lg dir mds h.md e2 (ls ++ [lt]) ntl f2 h.snapi h.enti _ _ _
      (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length ([] ++ ys1 ++ ys2 ++ ys3) pend3 _
      hlenL hsyncOk)
    $$ [Hws] [Hlg Hdir Hmd Hns Henti Hsnapi He Hlocks Hls Hcap Henc2 HW3] as %serr4 ⟨Hpre, Henc2, Hr4⟩
  · iexact Hws
  · iframe Henv Hzpk Henc2 HW3
    iunfold walPreInL
    iexists locks'
    iframe
    iframe #
    ipureintro; exact he2
  icases Hr4 with (⟨%he4, HS⟩ | ⟨%he4, -⟩)
  rotate_left
  · rcases serr4 with ei | _
    rotate_left
    · exact absurd rfl he4
    (try wp_auto)
    iapply HΦ
    iright; ipureintro; exact he4
  subst he4
  rw [hall]
  iunfold walPreInL at Hpre
  icases Hpre with ⟨%locks'', Hlg, -, Hdir, Hmd, -, Hns, -, Henti, Hsnapi, He, -, Hlocks, Hls,
    Hcap, -⟩
  iclear Hbw0 Hpw0 Hcf0 Hb0 Hbs0 Hu0 Hus0 Hl0 Hws HwsP
  (try wp_auto)
  -- the new segment's offset: the headers' end
  wp_apply (wp_tail w locks'' (ls ++ [lt]) ntl (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls]
    as ⟨Hlocks, Hls⟩
  · iframe
  (try wp_auto)
  wp_method_call
  wp_call
  (try wp_auto)
  iunfold os.fileS at HS
  icases HS with ⟨%mS, %ysS, %hokS, Hf2, Hfd2, Hoff2, HmS, HbS, -⟩
  obtain ⟨hoS1, hoS2, hoS3⟩ := cut_off_toInt 0 (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length
    (by omega)
  rw [show (((0 + (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length : Nat) : Int)) =
    ((0 : Nat) : Int) + (((tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length : Nat) : Int)
    by omega]
  wp_apply (os.File.Seek.wp_cur f2 fd2 _ (DFrac.own 1) _ hfd2 hoS1 hoS2) $$ [$Hf2 $Hoff2]
    as ⟨Hf2, Hoff2⟩
  (try wp_auto)
  -- step 6: `os.Rename(newTail.Name(), fpath)`
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply wp_Name f2 fd2 _ _ $$ [$Hf2] as Hf2
  (try wp_auto)
  -- the new segment
  have hz0 : ∀ x ∈ zs2.map (fun c => ((0 : w8), c)), x.1 = 0 := by
    intro x hx; obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx; rfl
  obtain ⟨hbsS, hLle⟩ := streamOk_vals hokS hz0
  have hcutS : mS.cut = none := by rw [metaChain_cut hokS.2.1]; exact hcut2
  have hszS : mS.size = max m2.size (0 + (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length) :=
    metaChain_size hokS.2.1 (Nat.zero_le _)
  have hysS : ysS.length = mS.size := by have := hokS.2.2.2.2.2.2.1; omega
  generalize hg : (⟨walFileName (sq + 1) (max (uint.nat h.enti) (uint.nat h.snapi) + 1), i2, mS.synced,
    ysS.map (fun x => durB x.1)⟩ : SegG) = g
  have hgbsL : g.bs.length = ysS.length := by rw [← hg]; simp
  have hgbs : g.bs = (tailStream Mr h.H h.md (h.cuts ++ [h.H.length]) ++ List.replicate
      (g.bs.length - (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length) 0).map durB ∧
      (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length ≤ g.bs.length := by
    rw [hgbsL]; rw [← hg]; exact ⟨hbsS, hLle⟩
  have hgmeta : g.om.size = g.bs.length ∧ g.om.cut = none ∧ g.om.lo = g.bs.length ∧
      g.om.hi = g.bs.length := by
    rw [hgbsL, hysS, ← hg]; simp [OsMeta.synced, hcutS]
  have hL8 := recFrames_mod8 walCodec (tailRecs Mr h.H h.md (h.cuts ++ [h.H.length]))
  rw [← tailStream_recs] at hL8
  have hgz : g.bs.length - (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length = 0 ∨
      8 ≤ g.bs.length - (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length := by
    rw [hgbsL, hysS, hszS]; exact cutHdrZeros _ _ hsz8 hL8
  have hLpos : 8 ≤ (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length := by
    rw [hFr]; simp only [List.length_append, WalEnc.frame_length]; omega
  have hgne : g.bs ≠ [] := by
    intro h0; have h2 := hgbs.2; rw [h0, List.length_nil] at h2; omega
  have hfitH : RecsFit walCodec (chainRecs walCodec (tailCrc Mr h.H h.md h.cuts)
      (cutHdrDs Mr h.md (walLastHS (h.H.map WalOpG.toM)))) := by
    apply recsFit_of_frames
    rw [← tailRecs_cut Mr h.H h.md h.cuts hsorted' hle', ← tailStream_recs]; omega
  -- the old tail
  rw [h1H, h1enti, h1snapi] at hidx
  have hbs0 : bs.length = (tailStream Mr h.H h.md h.cuts).length ∧ bs.length = m.size := by
    have := tailStream_len_split Mr h1 hsplit (by rw [h1rest, hrest]) h1pend
    rw [h1H, h1md, h1cuts] at this
    refine ⟨?_, hmb.2.1.1⟩
    rw [this, hmb.2.1.1, hmb.1, h1sz]
  have hm0x : m.lo = m.size ∧ m.hi = m.size := ⟨hmb.2.1.2.2.2.1, hmb.2.1.2.2.2.2⟩
  -- the name
  have hlt : go.GoStringLt nm0 (walFileName (sq + 1) (max (uint.nat h.enti) (uint.nat h.snapi) + 1)) := by
    rw [hnm0]; exact walFileName_lt sq ix (sq + 1) _ (by omega) hsq
  have hbtw := walNameP_walFileName (sq + 1) (max (uint.nat h.enti) (uint.nat h.snapi) + 1)
  have hcurbt := cutName_free hlargest hlt hbtw
  -- the update's resources (`walCutP`): quarters of the WAL claim, halves of the tmp claim
  have hq3 : qQuarter + ((1 : Qp).half + qQuarter) = 1 := by
    apply Subtype.ext
    show (1 : Rat) / 2 / 2 + ((1 : Rat) / 2 + (1 : Rat) / 2 / 2) = 1
    grind
  ihave Hcl' : osNames j (.except X) (DFrac.own (qQuarter + qQuarter)) hj $$ [Hcl]
  · rw [show qQuarter + qQuarter = (1 : Qp).half from Qp.half_add_half _]; iexact Hcl
  icases (osNames_frac j (.except X) qQuarter qQuarter hj).1 $$ Hcl' with ⟨Hcl1, Hcl2⟩
  icases (osNames_join j (.only [pipeTmp np]) (1 : Qp).half (1 : Qp).half ht (Qp.half_add_half 1)).2
    $$ Hn2 with ⟨Hn2a, Hn2b⟩
  icases (walOpenW_cut w dir).1 $$ Hopen with ⟨Hopen, Hpk, Hcf⟩
  ihave #Hinv : walInv (W := W) walCodec Mr R jr r $$ [Harea]
  · iunfold WalFs.walAreaOk at Harea; icases Harea with ⟨#H, -, -⟩; iexact H
  ihave Hau := walCut_osAUnc Mr R jr r dir j X hj (pipeTmp np) ht h1.γ h.H h.md h.cuts
    (h1.o0 + h1.out.length) h1.ino m bs g ⟨[h1.ino], [(j, .except X)], [dir]⟩
    (walFileName (sq + 1) (max (uint.nat h.enti) (uint.nat h.snapi) + 1)) nm0
    (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length (sq + 1)
    (max (uint.nat h.enti) (uint.nat h.snapi) + 1) (by simp)
    (htmps _ (pipeTmp_mem np)) hcuts hcpos ⟨hnm0w, hnm0c⟩ ⟨rfl, by omega, hlt⟩ hbtw hcurbt hbs0 hm0x
    rfl hgbs hgmeta hfitH hgz (by rw [← hg]) hgne $$ Hinv [Hdk Htk Hv Hcl1 Hn2a Hpk Hcf Hout Hm Hbs HmS HbS]
  · iunfold walCutP
    iframe Hdk Htk Hcl1 Hn2a Hpk Hcf Hout Hm Hbs Hsyn Hnamed
    isplitl [Hv]
    · iunfold tailVar; iexact Hv
    rw [← hg]
    iframe
  -- the rename
  ihave Hpd' : osPathS Rd dir (DFrac.own (qd.half + qd.half)) j $$ [Hpd]
  · rw [Qp.half_add_half]; iexact Hpd
  icases (osPathS_frac Rd dir qd.half qd.half j).1 $$ Hpd' with ⟨Hpd1, Hpd2⟩
  have hgi : g.ino = i2 := by rw [← hg]
  have hbX : (NameSet.except X).Mem (walFileName (sq + 1) (max (uint.nat h.enti) (uint.nat h.snapi) + 1)) :=
    fun hb => by rw [hXw _ hb] at hbtw; cases hbtw
  wp_apply (_wp_Rename dir (pipeTmp np) dir
      (walFileName (sq + 1) (max (uint.nat h.enti) (uint.nat h.snapi) + 1)) j j g.ino
      (.only [pipeTmp np]) (.except X) Rd (DFrac.own qd.half) (DFrac.own qd.half) ht hj
      (1 : Qp).half (1 : Qp).half qQuarter ((1 : Qp).half + qQuarter) (1 : Qp).half _
      (pipeTmp_nameOk np) (walFileName_nameOk _ _) (by simp [NameSet.Mem]) hbX (by simp)
      (by rw [hgi]; exact hcur2) (fun J hJ => by rw [hcurbt] at hJ; cases hJ)
      (Qp.half_add_half 1) hq3)
    $$ [Hpd1 Hpd2 Hperm Hn2b Hcl2 Hau] as %rerr ⟨Hpd1, Hpd2, Hperm, %ro, %hro, HQ, Hro⟩
  · iframe; iframe #
  iclear Hlt1 Hmu0 Htab0 Ht1 Hmdsb «$res0»
  -- the rename's outcome: an error returns
  rcases rerr with ei | _
  · (try wp_auto)
    iapply HΦ
    iright; ipureintro; nofun
  obtain ⟨⟨x, s0⟩, rfl⟩ := Option.isSome_iff_exists.1 (hro rfl)
  generalize hbt : walFileName (sq + 1) (max (uint.nat h.enti) (uint.nat h.snapi) + 1) = bt
    at hbtw hcurbt hbX hlt hg ⊢
  generalize hL : (tailStream Mr h.H h.md (h.cuts ++ [h.H.length])).length = L
    at hoS1 hoS2 hgbs hgz hLpos hgmeta hL8 hlenL hszS ⊢
  iunfold walCutQ at HQ
  icases HQ with ⟨Htm1, Hcw1, -, Htk, Hv, Hpk, Hout, Hcf, HmG, HbG⟩
  iunfold renFileOut at Hro
  icases Hro with ⟨#Hlog, Htm2, Hcw2⟩
  iunfold logOut at Hlog
  icases Hlog with ⟨-, #Hlogd⟩
  iunfold osLogged at Hlogd
  icases Hlogd with ⟨-, -, #Hlb⟩
  iunfold claimOut at Htm2 Hcw2
  isimp only at Htm2 Hcw2
  isimp only [cutClaim] at Hcw1
  ihave Hcw : osNames j (.except X) (DFrac.own (qQuarter + qQuarter))
      (hj.log x (renFileEnt j (pipeTmp np) j bt g.ino hj s0) (<[bt := .file g.ino]> hj.cur)) $$ [Hcw1 Hcw2]
  · iapply (osNames_frac _ _ _ _ _).2; iframe
  rw [show qQuarter + qQuarter = (1 : Qp).half from Qp.half_add_half _] at *
  (try wp_auto)
  -- step 7: `fileutil.Fsync(w.dirFile)`
  wp_apply wp_Now as %t0 -
  (try wp_auto)
  wp_apply (wp_FsyncDir df dfd dnm (DFrac.own 1) Rd j ph (x + 1)) $$ [Hdff Hdfd] as %ferr ⟨Hdff, Hdfd, Hfr⟩
  · iframe; iframe #
  icases Hfr with (%hfe | ⟨%hfe, #Hcm⟩)
  · rcases ferr with ei | _
    rotate_left
    · exact absurd rfl hfe
    (try wp_auto)
    iapply HΦ
    iright; ipureintro; nofun
  subst hfe
  (try wp_auto)
  iapply wp_notCrashed_acc
  · rfl
  iintro Hnc
  imod (walInv_cutSynced Mr R jr r dir j X hj x (renFileEnt j (pipeTmp np) j bt g.ino hj s0)
      (<[bt := .file g.ino]> hj.cur) bt g.ino (DFrac.own (1 : Qp).half) h1.γ
      ((h.H, h.md, h.cuts ++ [h.H.length], L, g.ino, none) : TailG) (x + 1) (by omega)
      ((renFileEnt_writes _ _ _ _ _ _ _ _).2 ⟨rfl, Or.inr rfl⟩) hbtw (GMap.lookup_insert _ _ _) rfl)
    $$ Hinv Hnc Hdk Hcw Htk Hv Hcf Hcm with ⟨Hnc, Hcw, Htk, Hv, Hcf⟩
  imodintro
  iframe Hnc
  -- the fsync's duration
  ihave #Henv0 := Henv
  iunfold encEnv at Henv0
  icases Henv0 with ⟨-, -, -, #Htime, #Hmet⟩
  iunfold wal.metricsInit at Hmet
  icases Hmet with ⟨⟨%hs, #Hhs, #Hhspec⟩, -, -⟩
  iunfold wal.histSpec at Hhspec
  wp_apply wp_Since as %dur -
  (try wp_auto)
  -- (`MethodResolve` on a `Duration` needs `NotInterface go.int64`: `go.int64` is a plain `def`, which
  -- `notInterface_Named` does not unfold)
  haveI _hni : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
  wp_pures
  wp_apply (wp_Seconds dur) as %fl -
  (try wp_auto)
  wp_apply Hhspec
  iclear Hhspec Hhs
  (try wp_auto)
  -- step 8: `newTail.Close()`
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply (wp_Close f2 fd2 _ _) $$ [Hf2 Hfd2] as %cerr -
  · iframe; iframe #
  (try wp_auto)
  -- `fileutil.LockFile(fpath, O_WRONLY, PrivateFileMode)`
  ihave Hpd : osPathS Rd dir (DFrac.own qd) j $$ [Hpd1 Hpd2]
  · iapply (show osPathS (GF := GF) Rd dir (DFrac.own (qd.half + qd.half)) j ⊢
      osPathS Rd dir (DFrac.own qd) j by rw [Qp.half_add_half])
    iapply (osPathS_frac Rd dir qd.half qd.half j).2; iframe
  ihave #Hfupk : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil $$ []
  · iPkgInit
  have hbn : NameOk bt := by rw [← hbt]; exact walFileName_nameOk _ _
  wp_apply (wp_LockFile (child dir bt) (W64 1) (W32 384) _ Unit _ _
      (walOpen_triple Rd dir bt (DFrac.own qd) j g.ino (.except X) (DFrac.own (1 : Qp).half)
        (hj.log x (renFileEnt j (pipeTmp np) j bt g.ino hj s0) (<[bt := .file g.ino]> hj.cur))
        (1 : Qp).half (W64 1) (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide)
        (by decide) hbn hbX (GMap.lookup_insert _ _ _)))
    $$ [Hpd Hcw Hperm] as %lf3 %lerr Hlp
  · iframe; iframe #
  iunfold fileutil.lockPost at Hlp
  icases Hlp with ⟨%u, (⟨%hle, ⟨Hpd, Hcw, Hperm⟩, %f3, %fd3, %i3, ⟨%hfd3, %hi3⟩, #Hlf3, Hf3, Hoff3, Hfd3⟩ |
    ⟨⟨%hle, -⟩, -⟩)⟩
  rotate_left
  · rcases lerr with ei | _
    rotate_left
    · exact absurd rfl hle
    (try wp_auto)
    iapply HΦ
    iright; ipureintro; nofun
  subst hle hi3
  (try wp_auto)
  -- `newTail.Seek(off, io.SeekStart)`
  ihave #Hlf3' := Hlf3
  iunfold fileutil.lockedFile at Hlf3'
  iStructNamed Hlf3'
  (try wp_auto)
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply (os.File.Seek.wp_start f3 fd3 _ _ (W64 0) _ hfd3 hoS1 hoS2) $$ [$Hf3 $Hoff3] as ⟨Hf3, Hoff3⟩
  (try wp_auto)
  -- `w.locks[len(w.locks)-1] = newTail`
  ihave %hlen := ownSlice_len locks'' (DFrac.own 1) _ $$ Hls
  simp only [List.length_append, List.length_singleton] at hlen
  have hix : 0 ≤ sint.Z (locks''.len - W64 1) ∧ sint.Z (locks''.len - W64 1) < sint.Z locks''.len := by
    obtain ⟨hl1, hl2⟩ := hlen; constructor <;> word
  rw [if_pos hix]
  wp_apply (wp_store_slice_index locks'' (sint.Z (locks''.len - W64 1)) _ lf3) $$ [$Hls] as Hls
  · ipureintro
    obtain ⟨hl1, hl2⟩ := hlen
    simp only [List.length_append, List.length_singleton]
    constructor <;> word
  have hset : (ls ++ [lt] ++ [ntl]).set (sint.Z (locks''.len - W64 1)).toNat lf3 = (ls ++ [lt]) ++ [lf3] := by
    have : (sint.Z (locks''.len - W64 1)).toNat = (ls ++ [lt]).length := by
      obtain ⟨hl1, hl2⟩ := hlen; simp only [List.length_append, List.length_singleton]; word
    rw [this, List.set_append_right _ _ (Nat.le_refl _)]
    simp
  rw [hset]
  (try wp_auto)
  -- `prevCrc = w.encoder.crc.Sum32()`
  iunfold ownEncoder at Henc2
  icases Henc2 with ⟨%pw2, %hc2, %b2, %u2, %bs2, %us2, #Hmu2, Hbw2, Hpw2, Hcf2, Hdc2, Hb2, Hbs2, %hb2,
    Hu2, Hus2, %hus2⟩
  iunfold ownDecCrc at Hdc2
  icases Hdc2 with ⟨%l2, %tab2, %hl2, Hl2, #Htab2⟩
  subst hl2
  (try wp_auto)
  wp_apply (wp_Sum32 l2 _ tab2 (DFrac.own 1)) $$ [Hl2] as Hl2
  · iexact Hl2
  (try wp_auto)
  -- `w.encoder, err = newFileEncoder(w.tail().File, prevCrc)`
  wp_apply (wp_tail w locks'' (ls ++ [lt]) lf3 (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls]
    as ⟨Hlocks, Hls⟩
  · iframe
  (try wp_auto)
  wp_apply (wp_newFileEncoder f3 fd3 _ _ (W64 ((0 : Nat) + (L : Int))) _ hfd3 hoS1 hoS2)
    $$ [Hf3 Hoff3] as %e3 ⟨Henc3, Hf3, Hoff3, %he3⟩
  · iframe; iframe #
  (try wp_auto)
  -- the log line
  wp_apply wp_String as %fs -
  (try wp_auto)
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [fs]
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply wp_Info lg _ _ $$ []
  · iframe #
  -- the new handle: its tail the new segment
  have hcrc' : WalHS.crc Mr ({ h with cuts := h.cuts ++ [h.H.length], ino := g.ino, o0 := L, out := [], pend := [], rest := 0, γ := h1.γ, sz := g.bs.length, pc := h.pc + 1 } : WalHS) =
      crcAfter walCodec c0 (cutHdrDs Mr h.md h.st) := by
    rw [WalHS.crc_done Mr _ rfl]
    simp only
    rw [tailCrc_cut Mr h.H h.md h.cuts hsorted' hle', ← hst, ← hcrc0, hc0]
  have htm : TailMeta g.om g.bs := by
    rw [← hg]
    exact tailMeta_synced _ _ (by simp [hysS]) (by rw [hokS.2.2.2.1]; exact hmaps2)
  have hgsz : g.bs.length ≤ 0xffffffff000 := by rw [hgbsL, hysS, hszS]; omega
  have hfd3' : openFd g.ino (W64 1 ||| W64 524288) = ⟨g.ino, false, true⟩ := by
    unfold openFd; congr 1
  icases Hfdo with ⟨%rd, Hfdo⟩
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists ({ h with cuts := h.cuts ++ [h.H.length], ino := g.ino, o0 := L, out := [], pend := [], rest := 0, γ := h1.γ, sz := g.bs.length, pc := h.pc + 1 } : WalHS)
  isplitl
  rotate_left
  · isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · iexact Hsyn
  iunfold walHandleIn
  iexists lg, df, sp, e3, fp, lf3, f3, mds, locks'', ls ++ [lt] ++ [lf3], fd3, dfd, child dir bt, dnm, j, rc
  rw [hcrc']
  simp only
  iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hspf Hst Hdec Hrc Hns Hmu Henti Hsnapi He Hlocks Hls Hcap
    Hlf3 Hfp Henv Hcrc Hwpk Henc3
  isplitr
  · ipureintro; exact he3
  isplitl [Hf3 Hfd3 Hoff3 Htk HmG HbG Hv]
  · iunfold walTailW
    iframe Hf3 Htk
    isplitl [Hfd3]
    · iexists false; rw [hfd3'] at *; iexact Hfd3
    isplitl [Hoff3]
    · rw [show ((L : Nat) : Int) + ((([] : List w8).length : Nat) : Int) = ((0 : Nat) : Int) + ((L : Nat) : Int)
        by simp]
      iexact Hoff3
    iexists g.om, g.bs
    iframe HmG HbG
    isplitr
    · ipureintro; exact ⟨hgmeta.1, htm, by omega, hfd3⟩
    iunfold tailVar at Hv
    iexact Hv
  isplitl [Hdk Hcw Hpd Hsid Hperm Hdfd Hnamed Hout Htf Hnf]
  · iunfold walDirH
    iexists Rd, qd, X, (hj.log x (renFileEnt j (pipeTmp np) j bt g.ino hj s0) (<[bt := .file g.ino]> hj.cur)),
      bt, ph
    iframe Hdk Hcw Hpd Hsid Hperm Hdfd Hnamed
    rw [walOut_cut]
    iframe Hout Htf Hnf
    ipureintro
    exact ⟨hbtw, GMap.lookup_insert _ _ _, rfl, htmps, hXw, ⟨sq + 1, _, hbt.symm, by omega⟩,
      cutDir_largest g.ino hlargest hlt⟩
  isplitr
  · ipureintro; simp
  isplitl [Hlks Hf Hfdo]
  · simp only [List.dropLast_concat]
    iapply (BigSepL.bigSepL_snoc (Φ := fun _ lf => walLockH lf)).2
    iframe Hlks
    iunfold walLockH
    iexists f, fd, name, ⟨h1.ino, rd, true⟩
    iframe Hltf Hf Hfdo
  isplitl [Hmain Htm1 Htm2]
  · iapply walPipeH_next fp dir h.pc γp Rp dqp j szp np hnp hfpn
    iframe Hisfp Hmain
    iapply tmpClaim_absent j (pipeTmp np)
      (ht.log x (renFileEnt j (pipeTmp np) j bt g.ino hj s0) (GMap.delete (pipeTmp np) ht.cur))
      (GMap.lookup_delete _ _)
    iapply (osNames_join _ _ _ _ _ (Qp.half_add_half 1)).1
    iframe
  isplitl [Hopen Hpk Hcf]
  · iapply (walOpenW_cut w dir).2
    iframe
  ipureintro
  refine ⟨WalHS.split_fresh Mr _ rfl hL.symm rfl rfl, hfd3, hgbs.2, hgsz,
    by have := hgbs.2; simp only [List.length_nil]; omega,
    ⟨fun _ => hidx.1 (by rw [h1rest, hrest]), hidx.2⟩, hmx⟩

end proof

end EtcdGrove
end Perennial
