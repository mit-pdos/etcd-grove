/-
The proofs of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__SaveSnapshotPre.lean`:
`w.sync()` and `w.SaveSnapshot(e)` before `Create`'s rename, over their callees' specs (the
fdatasync is the spec's hypothesis triple; `MustMarshalMessage` the WAL's marshalling law,
`pbutil.MustMarshalMessage.specWalSnap`).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshotPre
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutPre
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__flush
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encode
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.ValidateSnapshotForWrite
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessageWalSnap
public import LinuxFs.Spec.go_uber_org.zap.Logger__Warn
public import LinuxFs.Spec.go_uber_org.zap.Duration
public import LinuxFs.Spec.time.Duration__Seconds_ptr
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
    (wp_flush : go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.spec (GF := GF) (hG := hG))
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
  wp_apply (wp_flush e (wal.fileWi f) W B lim out pend c hlim) $$ [Hw] [He Hout]
    as %err ⟨He, Hres⟩
  · iexact Hw
  · iframe; iframe #
  icases Hres with (⟨%Herr, Hout⟩ | ⟨%Herr, Hbad⟩)
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
        (⌜en ≠ 0⌝ ∗ W (out ++ pend)) }} := hsync (out ++ pend)
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
    · iright; iframe HW; ipureintro; unfold errnoErr; simp; exact H0
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
    · iright; iframe HW; ipureintro; unfold errnoErr; simp; exact H0

/-- W4's `sync` before the rename, one lock: the corollary of `wp_proofPreL`. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proofPre
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_flush : go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specPre (GF := GF) :=
  go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specPre_of_L
    (go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proofPreL wp_tail wp_flush wp_Now wp_Since wp_Seconds_ptr wp_Duration wp_Warn)

theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.wp_proofPre (Mr : WalMarshal)
    (wp_sync : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specPre (GF := GF))
    (wp_encode : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.spec (GF := GF) (hG := hG))
    (wp_Validate : go_etcd_io.etcd.server.v3.storage.wal.walpb.ValidateSnapshotForWrite.spec
      (GF := GF) (hG := hG))
    (wp_GetIndex : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF)
      (hG := hG))
    (wp_Marshal : go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage.specWalSnap (GF := GF) Mr)
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.specPre (GF := GF) Mr := by
  intro w lg dir mds md e lt f snapi enti W B S lim out pend c sp sm cs hcs hlim hlim47 hsync
  iintro #Hw
  wp_start as ⟨#Henv, #Hzap, #Hpb, Hpre, He, Hout, #Hs⟩
  ihave #Hs0 := Hs
  iunfold walSnapAt at Hs
  icases Hs with ⟨%sc, Hsr, -⟩
  ihave %Hspn := snapRoC_ne sp sc $$ Hsr
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  simp only [decide_eq_false Hspn]
  try wp_auto
  wp_apply (wp_Validate Mr sp sm cs hcs) $$ []
  · iexact Hs0
  try wp_auto
  have hsz48 : (Mr.encSnap sm).length < 2 ^ 48 := by
    have h1 := recEnc_length (recOf ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm), Mr.encSnap sm⟩)
    have h2 : (walRecEnc ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm), Mr.encSnap sm⟩).length ≤
        (snapFrame Mr c sm).length := by
      unfold snapFrame WalEnc.frame; simp only [List.length_append]; omega
    have h3 : (Mr.encSnap sm).length ≤
        recSize (recOf ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm), Mr.encSnap sm⟩) := by
      have hne : ¬ (snapshotType = crcType ∧ Mr.encSnap sm = []) := fun h => by
        exact absurd h.1 (by decide)
      unfold recSize recOf; simp only [if_neg hne]; omega
    unfold walRecEnc at h2
    simp only [List.length_append] at hlim; omega
  wp_apply (wp_Marshal sp sm cs hsz48) $$ [] as %d ⟨%Hdn, Hd, Hdc⟩
  · iframe #
  try wp_auto
  iunfold walPreIn at Hpre
  icases Hpre with ⟨%locks, Hlg, #Hlgok, Hdir, Hmd, #Hmds, Hns, #Hmu, Henti, Hsnapi, Hfe, %Hen,
    Hlocks, Hls, Hcap, #Hlt⟩
  wp_apply wp_Lock $$ [] as ⟨Hown, -⟩
  · iexact Hmu
  try wp_auto
  simp only [go_etcd_io.etcd.server.v3.storage.wal.SnapshotType]
  try wp_auto
  have hT : (W64 5) = snapshotType := rfl
  have hfl : out.length + pend.length +
      (WalEnc.frame (walRecEnc ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm), Mr.encSnap sm⟩)).length
      ≤ lim := by
    simp only [snapFrame, List.length_append] at hlim; omega
  have hsz : recSize (recOf ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm), Mr.encSnap sm⟩)
      < 2 ^ 47 := by
    have h1 : (walRecEnc ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm), Mr.encSnap sm⟩).length =
        recSize (recOf ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm), Mr.encSnap sm⟩) :=
      recEnc_length _
    have h2 : (walRecEnc ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm), Mr.encSnap sm⟩).length ≤
        (WalEnc.frame (walRecEnc ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm),
          Mr.encSnap sm⟩)).length := by
      unfold WalEnc.frame; simp only [List.length_append]; omega
    omega
  ipersist «$v0»
  ipersist Hd
  wp_apply (wp_encode e (wal.fileWi f) W B lim out pend c _ snapshotType (Mr.encSnap sm) hsz hfl)
    $$ [Hw] [He Hout «$r0»] as %err ⟨%pend', He, #Hrec, Hres⟩
  · iexact Hw
  · iframe; iframe #
    iunfold encRecIn
    iexists _
    iframe «$r0»
    rw [hT]
    iframe #
    have hro : (recOf ⟨snapshotType, 0#32, Mr.encSnap sm⟩).data = some (Mr.encSnap sm) := by
      simp [recOf, snapshotType, crcType]
    rw [hro]
    simp only [recBytes]
    isplitl []
    · isplitr
      · ipureintro; exact Hdn
      · iexact Hd
    · ipureintro; simp
  icases Hres with (⟨%ys, ⟨%Herr, %Hys⟩, Hout⟩ | ⟨%a, %b, ⟨%Herr, %Hpe, %Hab⟩, Hbad⟩)
  rotate_left
  · -- the encode failed
    rcases err with ei | _
    rotate_left
    · exact absurd rfl Herr
    try wp_auto
    wp_apply wp_Unlock $$ [Hown]
    · iframe
      isplitl []
      · iexact Hmu
      inext; itrivial
    try wp_auto
    iapply HΦ
    iexists snapi, enti
    iunfold walPreIn
    isplitl [Hlg Hdir Hmd Hns Henti Hsnapi Hfe Hlocks Hls Hcap]
    · iexists locks
      iframe; iframe #; ipureintro; exact Hen
    isplitr
    · ipureintro; exact ⟨Or.inl rfl, Or.inl rfl⟩
    iright
    isplitr
    · ipureintro; exact Herr
    iexists _, _
    iframe He
    ileft; iexists _, _; iexact Hbad
  subst Herr
  have hlen2 : (out ++ ys).length + pend'.length ≤ lim := by
    have := congrArg List.length Hys; simp only [List.length_append] at this ⊢; omega
  have heq : out ++ ys ++ pend' = out ++ pend ++ snapFrame Mr c sm := by
    rw [List.append_assoc, Hys, snapFrame, List.append_assoc]
  try wp_auto
  ihave #HsIT := walSnapAt_idTerm Mr sp sm cs $$ Hs0
  wp_apply (wp_GetIndex sp (sm.Index', sm.Term')) $$ []
  · iexact HsIT
  wp_if_destruct
  all_goals (try (wp_apply (wp_GetIndex sp (sm.Index', sm.Term')) $$ []; iexact HsIT))
  all_goals (try wp_auto)
  all_goals (try (wp_apply (wp_GetIndex sp (sm.Index', sm.Term')) $$ []; iexact HsIT))
  all_goals (try wp_auto)
  all_goals wp_if_destruct
  all_goals (try (wp_apply (wp_GetIndex sp (sm.Index', sm.Term')) $$ []; iexact HsIT))
  all_goals (try wp_auto)
  all_goals (
    wp_apply (wp_sync w lg dir mds md e lt f _ _ W B S lim (out ++ ys) pend'
      (hash.crc32.crc32c c (Mr.encSnap sm)) hlen2 hsync) $$ [Hw]
      [Hlg Hdir Hmd Hns Henti Hsnapi Hfe Hlocks Hls Hcap He Hout] as %err2 ⟨Hpre, He, Hres2⟩
    · iexact Hw
    · iframe; iframe #
      iunfold walPreIn; iexists locks; iframe; iframe #; ipureintro; exact Hen
    try wp_auto
    wp_apply wp_Unlock $$ [Hown]
    · iframe
      isplitl []
      · iexact Hmu
      inext; itrivial
    try wp_auto
    iapply HΦ
    iexists _, _
    iframe Hpre
    isplitr
    · ipureintro
      first
        | exact ⟨Or.inl rfl, Or.inl rfl⟩
        | exact ⟨Or.inl rfl, Or.inr rfl⟩
        | exact ⟨Or.inr rfl, Or.inl rfl⟩
        | exact ⟨Or.inr rfl, Or.inr rfl⟩
    icases Hres2 with (⟨%H0, HS⟩ | ⟨%H0, Hbad⟩)
    · ileft
      rw [heq]
      iframe; ipureintro; exact H0
    · iright
      isplitr
      · ipureintro; exact H0
      iexists _, _
      iframe He
      icases Hbad with (Hb | Hw')
      · ileft; iexists _, _; iexact Hb
      · iright; iexists _; iexact Hw')

end proof

end EtcdGrove
end Perennial
