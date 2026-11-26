/-
`(*WAL).sync` with no I/O error (`Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__syncNoErr.lean`):
`WAL__sync.lean`'s `wp_core` over the tail's writer with no error (`wal.tailWriterWNE`, `TailWriterWNE.lean`)
and the tail's fdatasync with no error (`fileutil.Fdatasync.wp_tailWNE`, `TailFdatasyncNE.lean`), the
flush over a writer called only with bytes (`encoder.flush.specPNE`: nothing pending, no `Write`); the
error arms gone. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncNoErr
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailWriterWNE
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailFdatasyncNE

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
variable [syscall_sem : syscall.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- **The core of `w.sync()` with no I/O error** (`wp_core`'s success arm, always; the pending bytes end
at most at `maxBytes`). -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_coreNE
    (hS0 : ∀ st i, Sio.ino st i) (Mr : WalMarshal)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_flush : go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.specPNE (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS)
    (lg e lt f : Loc) (locks : GoSlice) (lfs : List Loc) (fd : w64) (name : GoString)
    (hrest : h.rest = 0) (hsplit : WalHS.Split Mr h) (hoff : h.o0 + h.out.length ≤ h.sz)
    (hsz : h.sz ≤ 0xffffffff000) (Hen : e ≠ null) (Hlt : lfs.getLast? = some lt)
    (hroom : h.o0 + h.out.length + h.pend.length ≤ maxBytes) :
    {{ WalFs.walAreaOk walCodec Mr R jr r ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
        ownEncoder e (wal.fileWi f) (h.crc Mr) h.pend ∗
        walTailW (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out TailMetaW ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
        locks ↦* lfs ∗ fileutil.lockedFile lt f ∗ encEnv ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
        WalFs.walOpenWI (W := W) w dir h.inc }}
      (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"sync")) (Val #()))
    {{ (err : GoInterface), RET #err;
        ⌜err = GoInterface.nil⌝ ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
          ownEncoder e (wal.fileWi f) (h.crc Mr) [] ∗
          walTailW (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0
            (max h.sz (h.o0 + h.out.length + h.pend.length)) (h.out ++ h.pend) TailMetaS ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
          locks ↦* lfs ∗ WalFs.walOpenWI (W := W) w dir h.inc ∗ WalFs.walSyncedLb dir h.inc h.H.length ∗
          ⌜max h.sz (h.o0 + h.out.length + h.pend.length) ≤ 0xffffffff000⌝ }} := by
  wp_start as ⟨#Harea, Hlg, #Hzap, Hns, He, Henc, Htw, Hlocks, Hls, #Hltf, #Henv, #Hwpk, Hopen⟩
  ihave #Hzpk : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  obtain ⟨ls, rfl⟩ := List.getLast?_eq_some_iff.1 Hlt
  wp_auto
  simp only [decide_eq_false Hen]
  wp_auto
  icases ownEncoder_pend_le e (wal.fileWi f) (h.crc Mr) h.pend $$ Henc with ⟨%hpl, Henc⟩
  have hokW : tailOkWNE Mr h.H h.md h.cuts h.o0 (h.out ++ h.pend) :=
    ⟨⟨by rw [(WalHS.split_rest0 hsplit hrest).1]; exact List.prefix_refl _,
      by simp only [List.length_append]; omega⟩, by simp only [List.length_append]; omega⟩
  ihave Htw := (show walTailW (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out TailMetaW ⊢
      walTailWS (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out by
    unfold walTailWS; rw [Nat.max_eq_left hoff]
    iintro H; iframe H; ipureintro; exact Nat.le_trans hoff (Nat.le_max_left _ _)) $$ Htw
  ihave Hws := wal.tailWriterWNE hS0 Mr R jr r f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz $$ Harea
  wp_apply (wp_flush e (wal.fileWi f)
      (walTailWS (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz) (fun _ _ => iprop(False))
      (tailOkWNE Mr h.H h.md h.cuts h.o0) h.out h.pend (h.crc Mr)
      (fun _ _ hp hy => tailOkWNE_prefix hp hy) hokW) $$ [Hws]
      [Henc Htw] as %err ⟨Henc, Hres⟩
  · iexact Hws
  · iframe; iframe #
  icases Hres with (⟨%Herr, Htw⟩ | ⟨%Herr, -, HB⟩)
  rotate_left
  · iexfalso; iexact HB
  subst Herr
  iunfold walTailWS at Htw
  icases Htw with ⟨Htw, %hbx⟩
  wp_auto
  ihave #Henv0 := Henv
  iunfold encEnv at Henv0
  icases Henv0 with ⟨#Hproto, #Hbin, #Hsync, #Htime, #Hmet⟩
  iunfold wal.metricsInit at Hmet
  icases Hmet with ⟨⟨%hs, #Hhs, #Hhspec⟩, -, -⟩
  iunfold wal.histSpec at Hhspec
  wp_apply wp_Now as %t -
  wp_apply (wp_tail w locks ls lt (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls] as ⟨Hlocks, Hls⟩
  · iframe
  ihave #Hlt0 := Hltf
  iunfold fileutil.lockedFile at Hlt0
  iStructNamed Hlt0
  wp_auto
  ihave Hopen2 := (walOpenWI_cut (W := W) w dir h.inc).1 $$ Hopen
  icases Hopen2 with ⟨Hoc, Hpk, Hcf⟩
  icases walOpenWCI_incLb w dir h.inc $$ Hoc with ⟨Hoc, #Hil⟩
  have hwr := (WalHS.split_rest0 hsplit hrest).2
  ihave Htw := (show walTailW (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0
      (max h.sz (h.o0 + (h.out ++ h.pend).length)) (h.out ++ h.pend) TailMetaW ⊢
      walTailW (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0
      (max h.sz (h.o0 + h.out.length + h.pend.length)) (h.out ++ h.pend) TailMetaW by
    rw [List.length_append, Nat.add_assoc]) $$ Htw
  wp_apply (fileutil.Fdatasync.wp_tailWNE hS0 wp_Fd Mr R jr r f fd name dir h.γ h.ino h.H h.md h.cuts
      h.o0 (max h.sz (h.o0 + h.out.length + h.pend.length)) (h.out ++ h.pend) hwr h.inc) $$ [Htw Hcf]
      as ⟨Hcf, Htw, #HS⟩
  · iframe Hil; iframe; iexact Harea
  have hmb : maxBytes = 0xffffffff000 := rfl
  simp only [List.length_append] at hbx
  have hbx' : max h.sz (h.o0 + h.out.length + h.pend.length) ≤ 0xffffffff000 := by omega
  wp_apply wp_Since as %dur -
  try wp_auto
  by_cases Hif : sint.Z (W64 1000000000) < sint.Z dur
  all_goals first | simp only [decide_eq_true Hif] | simp only [decide_eq_false Hif]
  all_goals (wp_pures; try wp_auto)
  · wp_apply wp_Duration as %f1 -
    wp_apply wp_Duration as %f2 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    try wp_auto
    wp_apply wp_Warn lg _ _ $$ []
    · iframe #
    try wp_auto
    wp_apply (wp_Seconds_ptr _ dur) $$ [took] as %fl took
    · iframe
    try wp_auto
    wp_apply Hhspec
    try wp_auto
    iapply HΦ
    isplitr
    · ipureintro; rfl
    ihave Hopen : WalFs.walOpenWI (W := W) w dir h.inc $$ [Hoc Hpk Hcf]
    · iapply (walOpenWI_cut (W := W) w dir h.inc).2; iframe
    iframe Hlg Hns He Henc Htw Hlocks Hls Hopen HS
    ipureintro; exact hbx'
  · try wp_auto
    wp_apply (wp_Seconds_ptr _ dur) $$ [took] as %fl took
    · iframe
    try wp_auto
    wp_apply Hhspec
    try wp_auto
    iapply HΦ
    isplitr
    · ipureintro; rfl
    ihave Hopen : WalFs.walOpenWI (W := W) w dir h.inc $$ [Hoc Hpk Hcf]
    · iapply (walOpenWI_cut (W := W) w dir h.inc).2; iframe
    iframe Hlg Hns He Henc Htw Hlocks Hls Hopen HS
    ipureintro; exact hbx'

/-- `sync.specNoErr`: `wp_coreNE` over the handle. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proofNoErr
    (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_flush : go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.specPNE (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specNoErr (Sio := Sio) (W := W) P Mr := by
  intro hS0 R jr r w dir h hrest hroom
  wp_start_folded as ⟨#Harea, Hh⟩
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk, Hopen, %Hpure⟩
  obtain ⟨hsplit, hfd, hoff, hsz, hidx, hidx1⟩ := Hpure
  wp_apply (go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_coreNE hS0 Mr wp_tail wp_flush wp_Fd wp_Now
      wp_Since wp_Seconds_ptr wp_Duration wp_Warn R jr r w dir h lg e lt f locks lfs fd name hrest
      hsplit hoff hsz Hen Hlt hroom) $$ [Hlg Hns He Henc Htw Hlocks Hls Hopen] as %err Hr
  · iframe; iframe #
  iapply HΦ
  icases Hr with ⟨%H0, Hlg, Hns, He, Henc, Htw, Hlocks, Hls, Hopen, #HS, %hbx⟩
  iframe HS
  isplitr
  · ipureintro; exact H0
  iunfold walHandleIn
  iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
  rw [show WalHS.crc Mr { h with out := h.out ++ h.pend, pend := [], sz := max h.sz (h.o0 + h.out.length + h.pend.length) } = WalHS.crc Mr h from rfl]
  ihave Htw := walTailW_mono f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 _ _ TailMetaS TailMeta
    (fun _ _ hm => hm.meta) $$ Htw
  simp only
  iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
    Hlocks Hls Hcap Hlks Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
  ipureintro
  refine ⟨Hen, Hlt, WalHS.split_flush hsplit, hfd, ?_, hbx, hidx, hidx1⟩
  simp only [List.length_append]; omega

/-- `sync.specCNoErr`: `wp_coreNE` over the handle after `Close` closed the pipeline. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proofCNoErr
    (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_flush : go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.specPNE (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specCNoErr (Sio := Sio) (W := W) P Mr := by
  intro hS0 R jr r w dir j h nmd nf hrest hroom
  wp_start_folded as ⟨#Harea, Hh⟩
  iunfold walHandleC at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, #Henv, #Hcrc, #Hwpk, Hopen, %Hpure⟩
  obtain ⟨hsplit, hfd, hoff, hsz, hidx, hidx1⟩ := Hpure
  wp_apply (go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_coreNE hS0 Mr wp_tail wp_flush wp_Fd wp_Now
      wp_Since wp_Seconds_ptr wp_Duration wp_Warn R jr r w dir h lg e lt f locks lfs fd name hrest
      hsplit hoff hsz Hen Hlt hroom) $$ [Hlg Hns He Henc Htw Hlocks Hls Hopen] as %err Hr
  · iframe; iframe #
  iapply HΦ
  icases Hr with ⟨%H0, Hlg, Hns, He, Henc, Htw, Hlocks, Hls, Hopen, #HS, %hbx⟩
  iframe HS
  isplitr
  · ipureintro; exact H0
  iunfold walHandleC
  iexists lg, df, sp, e, lt, f, mds, locks, lfs, fd, dfd, name, dnm, rc
  rw [show WalHS.crc Mr { h with out := h.out ++ h.pend, pend := [], sz := max h.sz (h.o0 + h.out.length + h.pend.length) } = WalHS.crc Mr h from rfl]
  simp only
  iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
    Hlocks Hls Hcap Hlks Hltf Hfp Henv Hcrc Hwpk Hopen
  ipureintro
  refine ⟨Hen, Hlt, WalHS.split_flush hsplit, hfd, ?_, hbx, hidx, hidx1⟩
  simp only [List.length_append]; omega

end proof

end EtcdGrove
end Perennial
