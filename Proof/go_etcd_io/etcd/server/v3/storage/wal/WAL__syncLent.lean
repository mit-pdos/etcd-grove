/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__syncLent.lean`: as `WAL__syncIdle.lean`'s,
with the fdatasync of the lent zeroed tail (`Fdatasync.specWalPend`) and, on success, the tail unregistered by
its key at the next step (`walInv_untailKey`, `ReadAllFail.lean`). Unit `closefailed`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncLent
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.ReadAllTailCallees
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllFail
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
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proofLent
    (Mr : WalMarshal)
    (wp_FdatasyncP : go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.specWalPend (hG := hG) (W := W) Mr)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specLent (W := W) Mr := by
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
  wp_apply (wp_FdatasyncP R jr r f fd name dir γ i H md cuts o0 sz k ho0) $$ [Htw Hcf]
      as %en ⟨Hcf, Hr⟩
  · iframe; iexact Harea
  icases Hr with (⟨%he, Htw, -⟩ | ⟨%he, Htw⟩)
  -- success: the tail unregistered by its key at the next step
  subst he
  unfold walTailW
  icases Htw with ⟨Hf, ⟨%rd, %lo, %lk, Hfd, Hlkt⟩, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  obtain ⟨hmsz, hTM, -, -, -⟩ := hp
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod walInv_untailKey (L := hG.goose_localGS) Mr R jr r dir γ H md cuts (o0 + ([] : List w8).length) i m bs hTM
      (by simpa using ho0) $$ Hinv Hnc Htf Hk [Hv] Hm Hb with ⟨Hnc, Htf, Hm, Hb⟩
  · unfold tailVar; iexact Hv
  iframe Hnc
  imodintro
  ihave Hres : iprop((⌜errnoErr 0 = GoInterface.nil⌝ ∗ walTailsFrag (W := W) ∅ ∗ os.ownFile f fd name (DFrac.own 1) ∗
        (∃ d : OsFd, osFd fd (DFrac.own 1) d ∗ fdLocks fd d ∗ ⌜d.ino = i⌝) ∗
        ∃ g : SegG, segRes g ∗ ⌜g.ino = i ∧ g.om.size = g.bs.length⌝) ∨
     (⌜errnoErr 0 ≠ GoInterface.nil⌝ ∗ walTailsFrag (W := W) (<[dir := γ]> (∅ : GMap GoString GName)) ∗
        walTailP (W := W) f fd name dir γ i H md cuts o0 sz [] k false
          (fun m bs => TailMetaZ m bs ∧ ∀ b x, o0 ≤ b → bs[b]? = some x → x.1 = 0)))
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
        walTailP (W := W) f fd name dir γ i H md cuts o0 sz [] k false
          (fun m bs => TailMetaZ m bs ∧ ∀ b x, o0 ≤ b → bs[b]? = some x → x.1 = 0))) $$ [Htf Htw]
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
