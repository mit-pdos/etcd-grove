/-
`(*WAL).sync`: the encoder's `flush` (over the tail's guarded writer, `wal.tailWriter`) and the tail's
`Fdatasync` (`fileutil.Fdatasync.wp_tail`, the crash-aware fdatasync), whose success raises the
invariant's synced mark (`walSyncedLb`). `wp_proofIn` proves `sync.specIn` (the pending bytes inside
the tail's preallocated size); `wp_proof` (`sync.spec`) waits for writes past the size (W6, after
`wal-zte2`). The leaf calls: `time.Now`/`Since` (Perennial's), `Duration.Seconds` (part copy), zap's
`Duration`/`Warn` (part copies), `walFsyncSec.Observe` (`wal.histSpec`, from `encEnv`). The lock
token's pending-cut flag (`walCutFrag none`, which the fdatasync's commit needs) comes out of the
sealed `walOpenW` by `walOpenW_cut`. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeG
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__flush
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailWriter
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

/-- See the file header (`sorry` until writes past the tail's size are covered). -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proof (P : WalPbIn GF) (Mr : WalMarshal) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr := by
  sorry

end proof

end EtcdGrove
end Perennial
