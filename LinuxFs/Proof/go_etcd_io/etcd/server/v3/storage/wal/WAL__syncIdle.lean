/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__syncIdle.lean`: no encoder (no
flush), `unsafeNoSync` false, then `time.Now`, `w.tail()`, `fileutil.Fdatasync` of its file over
`fileutil.Fdatasync.wp_idle` (`FdatasyncIdle.lean`), `time.Since`, the slow-sync warning, the
histogram's `Observe`, as `WAL__sync.lean`'s `wp_proofIn`. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncIdle
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.FdatasyncIdle
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
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proofIdle [os.file.FieldAssumptions]
    (Mr : WalMarshal)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specIdle (W := W) Mr := by
  intro R jr r w lg locks ls lt f fd name dir j X hj b fl m bs hb hi hlen
  wp_start as ⟨#Harea, He, Hns, Hlg, #Hzap, Hlocks, Hls, #Hltf, #Henv, Hf, Hfd, Hk, Hn, Htf,
    Hcf, Hm, Hb⟩
  ihave #Hzpk : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  try wp_auto
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
  wp_apply (fileutil.Fdatasync.wp_idle wp_Fd Mr R jr r f fd name dir j X hj b m bs (DFrac.own 1)
      (DFrac.own 1) fl hb hi hlen) $$ [Hf Hfd Hk Hn Htf Hcf Hm Hb]
      as %en ⟨Hf, Hfd, Hk, Hn, Htf, Hcf, Hsy⟩
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
    wp_apply (wp_Seconds_ptr _ dur) $$ [took] as %fl' took
    · iframe
    try wp_auto
    wp_apply Hhspec
    try wp_auto
    iapply HΦ
    iframe He Hns Hlg Hlocks Hls Hf Hfd Hk Hn Htf Hcf
    icases Hsy with (⟨%H0, Hm, Hb⟩ | ⟨%H0, Hm, Hb⟩)
    · ileft; iframe Hm Hb; ipureintro; subst H0; rfl
    · iright; iframe Hm Hb; ipureintro; unfold errnoErr; simp; exact H0
  · try wp_auto
    wp_apply (wp_Seconds_ptr _ dur) $$ [took] as %fl' took
    · iframe
    try wp_auto
    wp_apply Hhspec
    try wp_auto
    iapply HΦ
    iframe He Hns Hlg Hlocks Hls Hf Hfd Hk Hn Htf Hcf
    icases Hsy with (⟨%H0, Hm, Hb⟩ | ⟨%H0, Hm, Hb⟩)
    · ileft; iframe Hm Hb; ipureintro; subst H0; rfl
    · iright; iframe Hm Hb; ipureintro; unfold errnoErr; simp; exact H0

end proof

end EtcdGrove
end Perennial
