/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__SaveSnapshotPre.lean`'s `sync.specPre`:
`w.sync()` before `Create`'s rename, over its callees' specs (the fdatasync is the spec's hypothesis
triple). `w.SaveSnapshot(e)` before the rename is `WAL__SaveSnapshot.lean`'s `wp_pre`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshotPre
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutPre
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__flush
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encode
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.ValidateSnapshotForWrite
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessageWalSnap
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Duration
public import Spec.time.Duration__Seconds_ptr
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- `sync` before a rename, any locks (`walPreInL`, `WAL__cutPre.lean`). -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proofPreL
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_flush : go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.specPNE (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specPreL (GF := GF) := by
  intro w lg dir mds md e ls lt f snapi enti W B S lim out pend c hlim hsync
  iintro #Hw
  wp_start as ⟨#Henv, #Hzap, Hpre, He, Hout⟩
  iunfold walPreInL at Hpre
  icases Hpre with ⟨%locks, Hlg, #Hlgok, Hdir, Hmd, #Hmds, Hns, #Hmu, Henti, Hsnapi, Hfe, %Hen,
    Hlocks, Hls, Hcap, #Hlt⟩
  wp_auto
  simp only [decide_eq_false Hen]
  wp_auto
  wp_apply (wp_flush e (wal.fileWi f) W B (fun ys => ys.length ≤ lim) out pend c
      (fun _ _ hp hy => Nat.le_trans hp.length_le hy) (by simpa using hlim)) $$ [Hw] [He Hout]
    as %err ⟨He, Hres⟩
  · iexact Hw
  · iframe; iframe #
  icases Hres with (⟨%Herr, Hout⟩ | ⟨%Herr, -, Hbad⟩)
  rotate_left
  · -- the flush failed
    rcases err with ei | _
    rotate_left
    · exact absurd rfl Herr
    wp_auto
    iapply HΦ
    iframe He
    isplitl [Hlg Hdir Hmd Hns Henti Hsnapi Hfe Hlocks Hls Hcap]
    · iunfold walPreInL
      iexists locks
      iframe; iframe #; ipureintro; exact Hen
    iright
    isplitr
    · ipureintro; exact Herr
    ileft; iexact Hbad
  subst Herr
  wp_auto
  wp_apply wp_Now as %t -
  wp_apply (wp_tail w locks ls lt (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls] as ⟨Hlocks, Hls⟩
  · iframe
  ihave #Hlt0 := Hlt
  iunfold fileutil.lockedFile at Hlt
  iStructNamed Hlt
  wp_auto
  have hs : {{ W (out ++ pend) }}
      (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync)) (Val #f))
    {{ (en : w64), RET #(errnoErr en); (⌜en = 0⌝ ∗ S (out ++ pend)) ∨
        (⌜en ≠ 0 ∧ ¬ Fs.FsNoErrIno⌝ ∗ W (out ++ pend)) }} := hsync (out ++ pend)
  ihave Hfd := hs $$ [Hout]
  · iexact Hout
  wp_apply Hfd as %en Hsy
  wp_apply wp_Since as %dur -
  try wp_auto
  iunfold encEnv at Henv
  icases Henv with ⟨#Hproto, #Hbin, #Hsync, #Htime, #Hmet⟩
  iunfold wal.metricsInit at Hmet
  icases Hmet with ⟨⟨%hs, #Hhs, #Hhspec⟩, -, -⟩
  iunfold wal.histSpec at Hhspec
  wp_if_destruct
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
    iframe He
    isplitl [Hlg Hdir Hmd Hns Henti Hsnapi Hfe Hlocks Hls Hcap]
    · iunfold walPreInL
      iexists locks
      iframe; iframe #; ipureintro; exact Hen
    icases Hsy with (⟨%H0, HS⟩ | ⟨%H0, HW⟩)
    · ileft; iframe HS; ipureintro; subst H0; rfl
    · iright
      isplitr
      · ipureintro; unfold errnoErr; simp; exact H0.1
      iright; iframe HW; ipureintro; exact H0.2
  · try wp_auto
    wp_apply (wp_Seconds_ptr _ dur) $$ [took] as %fl took
    · iframe
    try wp_auto
    wp_apply Hhspec
    try wp_auto
    iapply HΦ
    iframe He
    isplitl [Hlg Hdir Hmd Hns Henti Hsnapi Hfe Hlocks Hls Hcap]
    · iunfold walPreInL
      iexists locks
      iframe; iframe #; ipureintro; exact Hen
    icases Hsy with (⟨%H0, HS⟩ | ⟨%H0, HW⟩)
    · ileft; iframe HS; ipureintro; subst H0; rfl
    · iright
      isplitr
      · ipureintro; unfold errnoErr; simp; exact H0.1
      iright; iframe HW; ipureintro; exact H0.2

/-- W4's `sync` before the rename, one lock: the corollary of `wp_proofPreL`. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proofPre
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_flush : go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.specPNE (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specPre (GF := GF) :=
  go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specPre_of_L
    (go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proofPreL wp_tail wp_flush wp_Now wp_Since wp_Seconds_ptr wp_Duration wp_Warn)

end proof

end EtcdGrove
end Perennial
