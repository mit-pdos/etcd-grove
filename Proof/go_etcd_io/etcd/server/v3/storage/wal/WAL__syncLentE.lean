/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__syncLentE.lean`: as `WAL__syncLent.lean`'s,
with the fdatasync of the tail a failed `ZeroToEnd` left (`Fdatasync.specWalLentE`: the token kept, the layout
`syncLay_anyE`'s) and, on success, the tail unregistered by the lent token at the next step
(`walInv_untailLent`, `TailSyncPendE.lean`). Unit `synclent`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncLentE
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.FdatasyncLentE
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSyncPendE
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.LockLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllReg
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Duration
public import Spec.time.Duration__Seconds_ptr
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
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proofLentE [os.file.FieldAssumptions]
    (Mr : WalMarshal)
    (wp_FdatasyncE : go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.specWalLentE (hG := hG) (W := W) Mr)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specLentE (W := W) Mr := by
  intro R jr r w lg locks ls lt f fd name dir γ i H md cuts o0 sz k ho0
  wp_start as ⟨#Harea, He, Hns, Hlg, #Hzap, Hlocks, Hls, #Hltf, #Henv, Htf, Hcf, Htw⟩
  ihave #Hzpk : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Harea2 := Harea
  iunfold WalFs.walAreaOk at Harea2
  icases Harea2 with ⟨#Hinv, -⟩
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
  wp_apply (wp_FdatasyncE R jr r f fd name dir γ i H md cuts o0 k ho0) $$ [Htw Hcf]
      as %en ⟨Hcf, Hr⟩
  · iframe; iexact Harea
  icases Hr with (⟨%he, Hf, ⟨%rd, %lo, %lk, Hfd, Hlkt⟩, Hoff, ⟨%k', Hk⟩, %m, %bs, Hm, Hb, %hTM, Hv⟩ |
    ⟨%he, Htw⟩)
  -- success: the tail unregistered by the lent token at the next step
  subst he
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod walInv_untailLent (L := hG.goose_localGS) Mr R jr r dir γ k' H md cuts o0 i m bs hTM
      ho0 $$ Hinv Hnc Htf Hk Hv Hm Hb with ⟨Hnc, Htf, Hm, Hb⟩
  iframe Hnc
  imodintro
  ihave Hres : iprop((⌜errnoErr 0 = GoInterface.nil⌝ ∗ walTailsFrag (W := W) ∅ ∗ os.ownFile f fd name (DFrac.own 1) ∗
        (∃ d : OsFd, osFd fd (DFrac.own 1) d ∗ fdLocks fd d ∗ ⌜d.ino = i⌝) ∗
        ∃ g : SegG, segRes g ∗ ⌜g.ino = i ∧ g.om.size = g.bs.length⌝) ∨
     (⌜errnoErr 0 ≠ GoInterface.nil⌝ ∗ walTailsFrag (W := W) (<[dir := γ]> (∅ : GMap GoString GName)) ∗
        walTailPE (W := W) Mr f fd name dir γ i H md cuts o0 k))
      $$ [Htf Hf Hfd Hlkt Hm Hb]
  · ileft
    iframe Htf Hf
    isplitr
    · ipureintro; exact WalFs.errnoErr_zero
    isplitl [Hfd Hlkt]
    · ihave Hlkt := fdLocksW_locks _ _ $$ Hlkt
      iexists _; iframe Hfd Hlkt; ipureintro; rfl
    iexists ⟨name, i, m, bs⟩
    unfold segRes
    iframe Hm Hb
    ipureintro; exact ⟨rfl, hTM.1.1.symm⟩
  iclear Hoff
  rotate_left
  ihave Hres : iprop((⌜errnoErr en = GoInterface.nil⌝ ∗ walTailsFrag (W := W) ∅ ∗ os.ownFile f fd name (DFrac.own 1) ∗
        (∃ d : OsFd, osFd fd (DFrac.own 1) d ∗ fdLocks fd d ∗ ⌜d.ino = i⌝) ∗
        ∃ g : SegG, segRes g ∗ ⌜g.ino = i ∧ g.om.size = g.bs.length⌝) ∨
     (⌜errnoErr en ≠ GoInterface.nil⌝ ∗ walTailsFrag (W := W) (<[dir := γ]> (∅ : GMap GoString GName)) ∗
        walTailPE (W := W) Mr f fd name dir γ i H md cuts o0 k)) $$ [Htf Htw]
  · iright
    iframe Htf Htw
    ipureintro; exact WalFs.errnoErr_ne en he
  all_goals (
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
      iframe He Hns Hlg Hlocks Hls Hcf
      iexact Hres
    · try wp_auto
      wp_apply (wp_Seconds_ptr _ dur) $$ [took] as %fl' took
      · iframe
      try wp_auto
      wp_apply Hhspec
      try wp_auto
      iapply HΦ
      iframe He Hns Hlg Hlocks Hls Hcf
      iexact Hres)

end proof

end EtcdGrove
end Perennial
