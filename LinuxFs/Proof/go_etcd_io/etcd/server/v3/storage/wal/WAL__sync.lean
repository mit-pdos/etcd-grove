/-
`(*WAL).sync`: the encoder's `flush` (over the tail's guarded writer, `wal.tailWriter`) and the tail's
`Fdatasync` (`fileutil.Fdatasync.wp_tail`, the crash-aware fdatasync), whose success raises the
invariant's synced mark (`walSyncedLb`). `wp_proofIn` proves `sync.specIn` (the pending bytes inside
the tail's preallocated size); `wp_proof` (`sync.spec`) the same over the writer past the size
(`wal.tailWriterW`, `walTailWS`; the pending bytes at most the page writer's buffer, `ownEncoder_pend_le`) and
the window's fdatasync (`fileutil.Fdatasync.wp_tailW`) (W6 log, twenty-fifth session), from one core,
`wp_core` (what `sync` reads of the handle), which also proves `specC` (`wp_proofC`, the handle after `Close`
closed the pipeline, the tail synced: `TailMetaS`) and, through `sync.spec`, `specCut` (`wp_proofCut`, W6 log,
twenty-sixth session). The leaf calls: `time.Now`/`Since` (Perennial's), `Duration.Seconds` (part copy), zap's
`Duration`/`Warn` (part copies), `walFsyncSec.Observe` (`wal.histSpec`, from `encEnv`). The lock
token's pending-cut flag (`walCutFrag none`, which the fdatasync's commit needs) comes out of the
sealed `walOpenW` by `walOpenW_cut`. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncC
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutTail
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenWLocked
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeG
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__flush
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailWriterW
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailFdatasync
public import LinuxFs.Spec.go_uber_org.zap.Logger__Warn
public import LinuxFs.Spec.go_uber_org.zap.Duration
public import LinuxFs.Spec.time.Duration__Seconds_ptr
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalEnc WalFs

/-- **A handle with every record encoded**: its writer's and page writer's bytes are the tail's
stream past `o0`. -/
theorem WalHS.split_rest0 [GooseExts] {Mr : WalMarshal} {h : WalHS} (hs : h.Split Mr)
    (hr : h.rest = 0) :
    h.out ++ h.pend = (tailStream Mr h.H h.md h.cuts).drop h.o0 ∧
      h.o0 + (h.out ++ h.pend).length = (tailStream Mr h.H h.md h.cuts).length := by
  obtain ⟨h1, h2, -⟩ := hs
  have he : h.encRecs Mr = tailRecs Mr h.H h.md h.cuts := by
    unfold WalHS.encRecs; rw [hr, Nat.sub_zero, List.take_length]
  rw [he, ← tailStream_recs] at h1 h2
  have hl : ((tailStream Mr h.H h.md h.cuts).take h.o0).length = h.o0 := by
    rw [List.length_take]; omega
  constructor
  · conv => rhs; rw [← h1]
    rw [List.append_assoc, List.drop_left' hl]
  · have := congrArg List.length h1
    simp only [List.length_append] at this ⊢
    omega

/-- The tail's guard holds of everything the encoder has accepted, inside the size. -/
theorem tailOk_rest0 [GooseExts] {Mr : WalMarshal} {h : WalHS} (hs : h.Split Mr)
    (hr : h.rest = 0) (hsz : h.o0 + h.out.length + h.pend.length ≤ h.sz) :
    tailOk Mr h.H h.md h.cuts h.o0 h.sz (h.out ++ h.pend) := by
  refine ⟨?_, ?_⟩
  · rw [(WalHS.split_rest0 hs hr).1]; exact List.prefix_refl _
  · simp only [List.length_append]; omega

/-- The split after a flush. -/
theorem WalHS.split_flush [GooseExts] {Mr : WalMarshal} {h : WalHS} (hs : h.Split Mr) :
    WalHS.Split Mr { h with out := h.out ++ h.pend, pend := [] } := by
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨?_, h2, h3⟩
  have he : WalHS.encRecs Mr { h with out := h.out ++ h.pend, pend := [] } = h.encRecs Mr := rfl
  simp only [he, List.append_nil, List.append_assoc] at h1 ⊢
  exact h1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable [syscall_sem : syscall.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proofIn [os.file.FieldAssumptions]
    (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_flush : go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.specP (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specIn (W := W) P Mr := by
  intro R jr r w dir h hrest hin
  wp_start as ⟨#Harea, Hh⟩
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk, Hopen, %Hpure⟩
  obtain ⟨hsplit, hfd, hoff, hsz, hidx, hidx1⟩ := Hpure
  ihave #Hzpk : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  obtain ⟨ls, rfl⟩ := List.getLast?_eq_some_iff.1 Hlt
  wp_auto
  simp only [decide_eq_false Hen]
  wp_auto
  ihave Hws := wal.tailWriter Mr R jr r f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz $$ Harea
  wp_apply (wp_flush e (wal.fileWi f)
      (walTailW (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz) (fun _ _ => iprop(True))
      (tailOk Mr h.H h.md h.cuts h.o0 h.sz) h.out h.pend (h.crc Mr)
      (fun _ _ hp hy => tailOk_prefix hp hy) (tailOk_rest0 hsplit hrest hin)) $$ [Hws]
      [Henc Htw] as %err ⟨Henc, Hres⟩
  · iexact Hws
  · iframe; iframe #
  icases Hres with (⟨%Herr, Htw⟩ | ⟨%Herr, -⟩)
  rotate_left
  · -- the flush failed
    rcases err with ei | _
    rotate_left
    · exact absurd rfl Herr
    wp_auto
    iapply HΦ
    iright; ipureintro; exact Herr
  subst Herr
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
  ihave Hopen2 := (walOpenW_cut (W := W) w dir).1 $$ Hopen
  icases Hopen2 with ⟨Hoc, Hpk, Hcf⟩
  have hwr := (WalHS.split_rest0 hsplit hrest).2
  wp_apply (fileutil.Fdatasync.wp_tail wp_Fd Mr R jr r f fd name dir h.γ h.ino h.H h.md h.cuts
      h.o0 h.sz (h.out ++ h.pend) hwr) $$ [Htw Hcf] as %en ⟨Htw, Hcf, Hsy⟩
  · iframe; iexact Harea
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
    icases Hsy with (⟨%H0, #HS⟩ | %H0)
    · ileft
      isplitr
      · ipureintro; subst H0; rfl
      iframe HS
      ihave Hopen : WalFs.walOpenW (W := W) w dir $$ [Hoc Hpk Hcf]
      · iapply (walOpenW_cut (W := W) w dir).2; iframe
      iunfold walHandleIn
      iexists lg, df, sp, e, fp, lt, f, mds, locks, ls ++ [lt], fd, dfd, name, dnm, j, rc
      rw [show WalHS.crc Mr { h with out := h.out ++ h.pend, pend := [] } = WalHS.crc Mr h from rfl]
      simp only
      iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
        Hlocks Hls Hcap Hlks Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
      ipureintro
      refine ⟨Hen, by simp, WalHS.split_flush hsplit, hfd, ?_, hsz, hidx, hidx1⟩ <;>
        simp only [List.length_append, List.length_nil] <;> omega
    · iright; ipureintro; unfold errnoErr; simp; exact H0
  · try wp_auto
    wp_apply (wp_Seconds_ptr _ dur) $$ [took] as %fl took
    · iframe
    try wp_auto
    wp_apply Hhspec
    try wp_auto
    iapply HΦ
    icases Hsy with (⟨%H0, #HS⟩ | %H0)
    · ileft
      isplitr
      · ipureintro; subst H0; rfl
      iframe HS
      ihave Hopen : WalFs.walOpenW (W := W) w dir $$ [Hoc Hpk Hcf]
      · iapply (walOpenW_cut (W := W) w dir).2; iframe
      iunfold walHandleIn
      iexists lg, df, sp, e, fp, lt, f, mds, locks, ls ++ [lt], fd, dfd, name, dnm, j, rc
      rw [show WalHS.crc Mr { h with out := h.out ++ h.pend, pend := [] } = WalHS.crc Mr h from rfl]
      simp only
      iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
        Hlocks Hls Hcap Hlks Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
      ipureintro
      refine ⟨Hen, by simp, WalHS.split_flush hsplit, hfd, ?_, hsz, hidx, hidx1⟩ <;>
        simp only [List.length_append, List.length_nil] <;> omega
    · iright; ipureintro; unfold errnoErr; simp; exact H0

/-- **The core of `w.sync()`** (`sync.spec`, `specC`, `specCut`): what `sync` reads of the handle (the
logger, `unsafeNoSync`, the encoder, the tail's writer state, the locks, the ghost handle), the pending
bytes flushed past the size if need be (`wal.tailWriterW`) and the window's fdatasync
(`fileutil.Fdatasync.wp_tailW`): the tail synced and durable (`TailMetaS`), its size below ext4's
maximum offset. *Error*: everything lost. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_core [os.file.FieldAssumptions]
    (Mr : WalMarshal)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_flush : go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.specP (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS)
    (lg e lt f : Loc) (locks : GoSlice) (lfs : List Loc) (fd : w64) (name : GoString)
    (hrest : h.rest = 0) (hsplit : WalHS.Split Mr h) (hoff : h.o0 + h.out.length ≤ h.sz)
    (hsz : h.sz ≤ 0xffffffff000) (Hen : e ≠ null) (Hlt : lfs.getLast? = some lt) :
    {{ WalFs.walAreaOk walCodec Mr R jr r ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
        ownEncoder e (wal.fileWi f) (h.crc Mr) h.pend ∗
        walTailW (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out TailMetaW ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
        locks ↦* lfs ∗ fileutil.lockedFile lt f ∗ encEnv ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
        WalFs.walOpenW (W := W) w dir }}
      (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"sync")) (Val #()))
    {{ (err : GoInterface), RET #err;
        (⌜err = GoInterface.nil⌝ ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
          ownEncoder e (wal.fileWi f) (h.crc Mr) [] ∗
          walTailW (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0
            (max h.sz (h.o0 + h.out.length + h.pend.length)) (h.out ++ h.pend) TailMetaS ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
          locks ↦* lfs ∗ WalFs.walOpenW (W := W) w dir ∗ WalFs.walSyncedLb dir h.H.length ∗
          ⌜max h.sz (h.o0 + h.out.length + h.pend.length) ≤ 0xffffffff000⌝) ∨
        (⌜err ≠ GoInterface.nil⌝ ∗ WalFs.walOpenW (W := W) w dir) }} := by
  wp_start as ⟨#Harea, Hlg, #Hzap, Hns, He, Henc, Htw, Hlocks, Hls, #Hltf, #Henv, #Hwpk, Hopen⟩
  ihave #Hzpk : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  obtain ⟨ls, rfl⟩ := List.getLast?_eq_some_iff.1 Hlt
  wp_auto
  simp only [decide_eq_false Hen]
  wp_auto
  icases ownEncoder_pend_le e (wal.fileWi f) (h.crc Mr) h.pend $$ Henc with ⟨%hpl, Henc⟩
  have hokW : tailOkW Mr h.H h.md h.cuts h.o0 (h.out ++ h.pend) :=
    ⟨by rw [(WalHS.split_rest0 hsplit hrest).1]; exact List.prefix_refl _,
      by simp only [List.length_append]; omega⟩
  ihave Htw := (show walTailW (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out TailMetaW ⊢
      walTailWS (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out by
    unfold walTailWS; rw [Nat.max_eq_left hoff]
    iintro H; iframe H; ipureintro; exact Nat.le_trans hoff (Nat.le_max_left _ _)) $$ Htw
  ihave Hws := wal.tailWriterW Mr R jr r f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz $$ Harea
  wp_apply (wp_flush e (wal.fileWi f)
      (walTailWS (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz) (fun _ _ => iprop(True))
      (tailOkW Mr h.H h.md h.cuts h.o0) h.out h.pend (h.crc Mr)
      (fun _ _ hp hy => tailOkW_prefix hp hy) hokW) $$ [Hws]
      [Henc Htw] as %err ⟨Henc, Hres⟩
  · iexact Hws
  · iframe; iframe #
  icases Hres with (⟨%Herr, Htw⟩ | ⟨%Herr, -⟩)
  rotate_left
  · -- the flush failed
    rcases err with ei | _
    rotate_left
    · exact absurd rfl Herr
    wp_auto
    iapply HΦ
    iright; iframe Hopen; ipureintro; exact Herr
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
  ihave Hopen2 := (walOpenW_cut (W := W) w dir).1 $$ Hopen
  icases Hopen2 with ⟨Hoc, Hpk, Hcf⟩
  have hwr := (WalHS.split_rest0 hsplit hrest).2
  ihave Htw := (show walTailW (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0
      (max h.sz (h.o0 + (h.out ++ h.pend).length)) (h.out ++ h.pend) TailMetaW ⊢
      walTailW (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0
      (max h.sz (h.o0 + h.out.length + h.pend.length)) (h.out ++ h.pend) TailMetaW by
    rw [List.length_append, Nat.add_assoc]) $$ Htw
  wp_apply (fileutil.Fdatasync.wp_tailW wp_Fd Mr R jr r f fd name dir h.γ h.ino h.H h.md h.cuts
      h.o0 (max h.sz (h.o0 + h.out.length + h.pend.length)) (h.out ++ h.pend) hwr) $$ [Htw Hcf]
      as %en ⟨Hcf, Hsy⟩
  · iframe; iexact Harea
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
    icases Hsy with (⟨%H0, Htw, #HS⟩ | ⟨%H0, -⟩)
    · ileft
      isplitr
      · ipureintro; subst H0; rfl
      ihave Hopen : WalFs.walOpenW (W := W) w dir $$ [Hoc Hpk Hcf]
      · iapply (walOpenW_cut (W := W) w dir).2; iframe
      iframe Hlg Hns He Henc Htw Hlocks Hls Hopen HS
      ipureintro; exact hbx'
    · iright
      isplitr
      · ipureintro; unfold errnoErr; simp; exact H0
      iapply (walOpenW_cut (W := W) w dir).2; iframe
  · try wp_auto
    wp_apply (wp_Seconds_ptr _ dur) $$ [took] as %fl took
    · iframe
    try wp_auto
    wp_apply Hhspec
    try wp_auto
    iapply HΦ
    icases Hsy with (⟨%H0, Htw, #HS⟩ | ⟨%H0, -⟩)
    · ileft
      isplitr
      · ipureintro; subst H0; rfl
      ihave Hopen : WalFs.walOpenW (W := W) w dir $$ [Hoc Hpk Hcf]
      · iapply (walOpenW_cut (W := W) w dir).2; iframe
      iframe Hlg Hns He Henc Htw Hlocks Hls Hopen HS
      ipureintro; exact hbx'
    · iright
      isplitr
      · ipureintro; unfold errnoErr; simp; exact H0
      iapply (walOpenW_cut (W := W) w dir).2; iframe

/-- See the file header: `wp_core` over the handle (`walHandleIn`), the tail's `TailMetaS` weakened to
`TailMeta`. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proof [os.file.FieldAssumptions]
    (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_flush : go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.specP (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr := by
  intro R jr r w dir h hrest
  wp_start_folded as ⟨#Harea, Hh⟩
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk, Hopen, %Hpure⟩
  obtain ⟨hsplit, hfd, hoff, hsz, hidx, hidx1⟩ := Hpure
  wp_apply (go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_core Mr wp_tail wp_flush wp_Fd wp_Now
      wp_Since wp_Seconds_ptr wp_Duration wp_Warn R jr r w dir h lg e lt f locks lfs fd name hrest
      hsplit hoff hsz Hen Hlt) $$ [Hlg Hns He Henc Htw Hlocks Hls Hopen] as %err Hr
  · iframe; iframe #
  iapply HΦ
  icases Hr with (⟨%H0, Hlg, Hns, He, Henc, Htw, Hlocks, Hls, Hopen, #HS, %hbx⟩ | ⟨%H0, Hopen⟩)
  · ileft
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
  · iright; ipureintro; exact H0

/-- **`WAL.sync.specC`**: `wp_core` over the handle after `Close` closed the pipeline (`walHandleC`),
the tail synced (`TailMetaS`). -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proofC [os.file.FieldAssumptions]
    (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_flush : go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.specP (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specC (W := W) P Mr := by
  intro R jr r w dir j h nmd hrest
  wp_start_folded as ⟨#Harea, Hh⟩
  iunfold walHandleC at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, #Henv, #Hcrc, #Hwpk, Hopen, %Hpure⟩
  obtain ⟨hsplit, hfd, hoff, hsz, hidx, hidx1⟩ := Hpure
  wp_apply (go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_core Mr wp_tail wp_flush wp_Fd wp_Now
      wp_Since wp_Seconds_ptr wp_Duration wp_Warn R jr r w dir h lg e lt f locks lfs fd name hrest
      hsplit hoff hsz Hen Hlt) $$ [Hlg Hns He Henc Htw Hlocks Hls Hopen] as %err Hr
  · iframe; iframe #
  iapply HΦ
  icases Hr with (⟨%H0, Hlg, Hns, He, Henc, Htw, Hlocks, Hls, Hopen, #HS, %hbx⟩ | ⟨%H0, Hopen⟩)
  · ileft
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
  · iright
    isplitr
    · ipureintro; exact H0
    iapply walOpenW_lockedTok $$ Hopen

/-- **`WAL.sync.specCut`**: `sync.spec` at a handle whose size is its write position
(`h.sz = o0 + |out|`, `cut`'s truncate), so the size after the flush is the stream's end
(`cutSynced`), the window closed: `walHandleIn`'s `TailMeta` weakened to `TailMetaW`. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proofCut [os.file.FieldAssumptions]
    (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_sync : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specCut (W := W) P Mr := by
  intro R jr r w dir h hrest hsz
  wp_start_folded as ⟨#Harea, Hh⟩
  wp_apply (wp_sync R jr r w dir h hrest) $$ [Hh] as %err Hr
  · iframe; iexact Harea
  iapply HΦ
  icases Hr with (⟨%H0, Hh, #HS⟩ | %H0)
  · ileft
    iframe HS
    isplitr
    · ipureintro; exact H0
    have hc : cutSynced h =
        { h with out := h.out ++ h.pend, pend := [], sz := max h.sz (h.o0 + h.out.length + h.pend.length) } := by
      unfold cutSynced; rw [hsz, Nat.max_eq_right (by omega)]
    rw [hc]
    iexact Hh
  · iright; ipureintro; exact H0


end proof

end EtcdGrove
end Perennial
