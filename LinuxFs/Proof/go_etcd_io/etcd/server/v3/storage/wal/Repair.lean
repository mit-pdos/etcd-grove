/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Repair.lean` (W7 of
`notes/wal-fsext-plan.md`; the W7-W12 log, fourteenth session), in Go's order: `openLast` (the update
committed unchanged and the last segment pinned, law L1); the decoder over `fileutil.NewFileReader(f.File)`
(law L2: every stop at the end of the last segment's frames, `RepairDecode.lean`); on `io.EOF` the pin put
back unchanged (`walInv_unpinLast`); on `io.ErrUnexpectedEOF` the `.broken` file (law L3: `walInv_keyExcl`,
then `walBroken_osAUnc` or `walInv_lendOther`, `RepairBroken.lean`), `f.Seek(0, io.SeekStart)`, `io.Copy`
(`io.CopyFiles.spec`, a hypothesis), the file given back (`walInv_unlendOther`), the tail registered pending
(`walInvRegisterPendLaw_holds`, its write position the decoder's `LastOffset()`: `repairFile_unique`), the
truncate (`os.File.Truncate.specRepTail`) and the fsync (`fileutil.Fsync.specRepTail`), the put-back
(`walInv_repairPut`, L5), `walFsyncSec.Observe`; the deferred closes. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.Repair
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.openLast
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.RepairCallees
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.NewDecoder
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__Decode
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__LastOffset
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__LastCRC
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__UpdateCRC
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetType
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetCrc
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__Validate
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileReader
public import LinuxFs.Spec.go_uber_org.zap.String
public import LinuxFs.Spec.go_uber_org.zap.Error
public import LinuxFs.Spec.go_uber_org.zap.Logger__Info
public import LinuxFs.Spec.go_uber_org.zap.Logger__Warn
public import LinuxFs.Spec.os.File__Name
public import LinuxFs.Spec.os.File__Close
public import LinuxFs.Spec.os.OpenFileTruncSN
public import LinuxFs.Spec.io.CopyFiles
public import LinuxFs.Spec.time.Duration__Seconds
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since
public import LinuxFs.Proof.os.Off
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairBroken
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairLoop
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairPut
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllRegCommit
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadBridge
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecStreams
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.openAtIndex
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairLocked

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
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions]
variable [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- `openLast`'s read-write open gives a readable and writable fd. -/
theorem openFd_rdwr (i : Ino) : openFd i (W64 2 ||| W64 524288) = ⟨i, true, true⟩ := by
  unfold openFd; congr

set_option hygiene false in
/-- **A `false` exit** with the segment's file and fd (`Hf`, `Hfd`): the deferred `f.Close()`, then the
post with the token lost (`Repair.spec`'s `false` arm). Unhygienic: it names `Repair`'s hypotheses. -/
macro "repair_false" : tactic => `(tactic| (
    wp_apply wp_lockedClose wp_Close lf f fd _ _ $$ [Hf Hfd] as %cerr -
    · iframe; iframe #
    try wp_auto
    try imodintro
    try wp_auto
    iapply HΦ
    iframe Hp Hres Hperm
    isplitr [HQ]
    · iright; ipureintro; rfl
    iexists o; iexact HQ))

set_option hygiene false in
/-- **The segment's stream out of the decoder** (`HS : walFileS …`). Unhygienic. -/
macro "repair_stream" : tactic => `(tactic| (
    ihave Hs := ownDecoder_streams dec IoE eof [F] _ _ _ $$ Hdec
    ihave ⟨%q, HS⟩ := (BigSepL.bigSepL_singleton (PROP := IProp GF)
      (Φ := fun _ (F : DecFile GF) => iprop(∃ q, F.S q))).1 $$ Hs))

set_option hygiene false in
/-- **The segment's stream opened** (`HS : F.S q` to its file, fd, offset and halves). Unhygienic. -/
macro "repair_open" : tactic => `(tactic| (
    rw [← hF]
    simp only [walDecFile]
    iunfold walFileS at HS
    icases HS with ⟨⟨%hqp, -⟩, Hf, Hfd, Hoff, Hm, Hb⟩))

/-- See the file header. -/
theorem wal.Repair.wp_proof (Mr : WalMarshal)
    (hEnv : WalDecEnvSupply (GF := GF))
    (wp_IsEof : errors.IsPathErrnoEof.spec (GF := GF) (hG := hG))
    (wp_openLast : go_etcd_io.etcd.server.v3.storage.wal.openLast.spec (W := W) Mr)
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (wp_Name : os.File.Name.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_NFR : go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileReader.spec (GF := GF) (hG := hG))
    (wp_NewDecoder : go_etcd_io.etcd.server.v3.storage.wal.NewDecoder.spec (GF := GF) (hG := hG))
    (wp_Decode : go_etcd_io.etcd.server.v3.storage.wal.decoder.Decode.spec (GF := GF) (hG := hG))
    (wp_LastCRC : go_etcd_io.etcd.server.v3.storage.wal.decoder.LastCRC.spec (GF := GF) (hG := hG))
    (wp_UpdateCRC : go_etcd_io.etcd.server.v3.storage.wal.decoder.UpdateCRC.spec (GF := GF) (hG := hG))
    (wp_LastOffset : go_etcd_io.etcd.server.v3.storage.wal.decoder.LastOffset.spec (GF := GF) (hG := hG))
    (wp_GetType : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetType.spec (GF := GF) (hG := hG))
    (wp_GetCrc : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetCrc.spec (GF := GF) (hG := hG))
    (wp_Validate : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Validate.spec (GF := GF) (hG := hG))
    (wp_Stat : os.File.Stat.spec (GF := GF) (hG := hG))
    (wp_Size : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (wp_FName : os.fileStat.Name.spec (GF := GF) (hG := hG))
    (wp_cNWF : go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.specFile (GF := GF) (hG := hG))
    (wp_OpenN : os.OpenFile.specCreateTruncSncN (GF := GF) (hG := hG))
    (wp_Copy : io.CopyFiles.spec (GF := GF) (hG := hG))
    (wp_Trunc : os.File.Truncate.specRepTail (W := W) Mr)
    (wp_Fsync : go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.specRepTail (W := W) Mr)
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds : time.Duration.Seconds.spec (GF := GF) (hG := hG)) :
    wal.Repair.spec (W := W) Mr := by
  intro lg R jr r dir nm qp Q hin hnmO hr hdl
  wp_start as ⟨#Hzap, #Hok, Hp, Hres, Hperm, Hu, Hau⟩
  ihave #Hok' := Hok
  iunfold WalFs.walAreaOk at Hok'
  icases Hok' with ⟨#Hinv, #Hosi, #Hsi, %hrb⟩
  ihave %hlgn := zapLoggerOk_ne_null lg $$ Hzap
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  rw [decide_eq_false hlgn]
  try wp_auto
  wp_apply wp_openLast lg R jr r dir nm qp Q hin hnmO hr hdl $$ [Hp Hres Hperm Hu Hau]
    as %lf %err ⟨Hp, Hres, Hperm, %o, HQ, Hcase⟩
  · iframe; iframe #
  icases Hcase with (⟨%herr, Hu⟩ | ⟨⟨%herr, %ho⟩, Hlo⟩)
  · -- `openLast` failed: `false`, the token back
    cases err
    case nil => exact absurd rfl herr
    try wp_auto
    iapply HΦ
    iframe Hp Hres Hperm
    isplitl [Hu]
    · ileft; iexact Hu
    iexists o; iexact HQ
  subst herr
  iunfold walLastOpen at Hlo
  icases Hlo with ⟨%d, %lay, %X, %hj, %gL, %f, %fd, %qd, %hfacts, #Hkey, Hl, ⟨Htf, Hnf⟩, Ho, HS, Hj,
    Hpd, #Hlf, Hf, Hoff, Hfd⟩
  obtain ⟨hljr, hX, hcoh, habs, hidle, hnd, hsn, hgL, hfd⟩ := hfacts
  rw [openFd_rdwr]
  try wp_auto
  -- `lg.Info("repairing", zap.String("path", f.Name()))`
  wp_apply wp_lockedName wp_Name lf f fd _ _ $$ [Hf] as Hf
  · iframe Hf Hlf
  wp_apply wp_String as %f1 -
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  try wp_auto
  wp_apply wp_Info lg _ _ $$ []
  · iframe #
  try wp_auto
  -- `NewDecoder(fileutil.NewFileReader(f.File))`
  ihave #Hlf2 := Hlf
  iunfold fileutil.lockedFile at Hlf2
  iStructNamed Hlf2
  try wp_auto
  wp_apply wp_NFR f as %rl Hrl
  ihave Hrl2 := (dfractional_update_into_persistently
    (typedPointsto (GF := GF) rl
      (go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.mk f) (DFrac.own 1))
    (fun dq => typedPointsto (GF := GF) rl
      (go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.mk f) dq)
    (DFrac.own 1)).update_into_persistently $$ Hrl
  iapply wp_fupd
  imod Hrl2 with #Hrl
  try wp_auto
  ihave ⟨%IoE, %eof, %ueof, #Hde, %hIo⟩ := hEnv $$ Hpkg
  obtain ⟨hIo, hIoN⟩ := hIo
  ihave #Hde' := Hde
  iunfold decEnv at Hde'
  icases Hde' with ⟨-, -, -, -, #Hbufio, #Heof, #Hueof, #Heok, #Hcrc, -, -⟩
  ihave #Hosp := wal_osInit $$ Hpkg
  ihave ⟨#Heofa, %hIoEof⟩ := isEofOk_eof IoE eof ueof $$ Heok
  have hgLm : gL ∈ lay.segs := List.mem_of_getLast? hgL
  have hSz : gL.om.size = gL.bs.length := (habs.metas gL hgLm).1
  iunfold segRes at HS
  icases HS with ⟨Hm, Hb⟩
  iapply (Fs.wp_osMeta_size _ _ rfl gL.ino _ gL.om) $$ Hm
  iintro %hszl Hm
  have hlen : gL.bs.length + 2 ^ 12 < 2 ^ 62 := by
    have h2 : Fs.maxBytes = 0xffffffff000 := rfl; omega
  ihave #HdF := walDecFile_ok wp_Stat wp_Size wp_FName wp_IsEof IoE hIo eof hIoEof rl f fd
    (child dir gL.name) ⟨gL.ino, true, true⟩ gL hfd rfl rfl hSz hlen
    $$ []
  · iframe #
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.ty) #rl]
  isplitr
  · ipureintro; rfl
  iintro %rsl ⟨Hrsl, -⟩
  try wp_auto
  generalize hF : walDecFile (GF := GF) rl f fd (child dir gL.name) ⟨gL.ino, true, true⟩ gL = F at *
  wp_apply wp_NewDecoder _ [F] IoE eof $$ [Hrsl Hf Hfd Hoff Hm Hb] as %dI ⟨%dec, %hdI, Hrsl, Hdec⟩
  · iframe #
    isplitl [Hrsl]
    · have e : [F].map (fun F => GoInterface.ok F.fr) =
          [interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.ty) #rl] := by
        rw [← hF]; rfl
      rw [e]; iexact Hrsl
    isplitl
    · rw [← hF]
      simp only [walDecFile]
      iunfold walFileS
      iframe
      ipureintro; exact ⟨List.nil_prefix, hfd⟩
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  subst hdI
  try wp_auto
  -- the loop (law L2): the decoder at the end of a prefix of the segment's records
  obtain ⟨rs, hRF, hrsw⟩ := walRepairFile walCodec_ok habs hidle.1 hidle.2.1 gL hgL
  have hFbs : F.bs = segImg gL := by rw [← hF]; rfl
  ihave Hra : ownRecAny «$r0_ptr» $$ [«$r0»]
  · unfold ownRecAny; iexists _; iexact «$r0»
  ihave HI : (∃ (off : Nat) (c : w32), "Hdec" ∷ ownDecoder dec IoE eof [F] off c true ∗
      "Hra" ∷ ownRecAny «$r0_ptr» ∗ "%hat" ∷ ⌜RepairAt walCodec rs off c⌝) $$ [Hdec Hra]
  · iexists 0, 0#32
    iframe
    ipureintro; exact repairAt_start _ _
  irename «rec» => Hrec
  wp_for HI
  try wp_auto
  wp_apply wp_LastOffset dec IoE eof [F] off c true $$ Hdec as Hdec
  try wp_auto
  wp_apply (wp_Decode walCodec dec «$r0_ptr» IoE eof ueof [F] off c rfl) $$ [Hdec Hra] as %err Hpost
  · iframe Hdec Hra Hde
  iunfold decPost at Hpost
  icases Hpost with ⟨Hpost, #Hans⟩
  have hRF' : RepairFile walCodec F.bs rs := by rw [hFbs]; exact hRF
  ihave Hn := repair_decNorm dec «$r0_ptr» IoE eof ueof F rs off c err hRF' hat $$ [Hde Hpost]
  · iframe Hpost Hde
  icases Hn with (⟨%r, %off1, %c1x, ⟨%he, %hg⟩, Hr, Hdec⟩ | ⟨%he, %q, HS⟩ | ⟨%hne, ⟨%q, HS⟩, #Hue⟩)
  · -- a record: on a CRC record its check, then the next iteration
    subst he
    try wp_auto
    have hnext : ∀ c2, ¬ (r.typ = crcType ∧ crcRecBad c2 r) → c2 = c1x →
        RepairAt walCodec rs off1 (rdCrc c1x r) := fun c2 hok hc2 => by
      subst hc2; exact (repairAt_ok walCodec_ok hRF' hat hg hok).2
    wp_apply wp_GetType $$ Hr as Hr
    wp_if_destruct
    · -- `CrcType`
      have hT : r.typ = crcType := Hif
      wp_apply wp_LastCRC dec IoE eof [F] off1 c1x true $$ Hdec as Hdec
      wp_if_destruct
      · -- the chain's CRC is zero: not checked
        have hnc : ¬ (r.typ = crcType ∧ crcRecBad (W32 0) r) := fun h => h.2.1 rfl
        wp_apply wp_GetCrc $$ Hr as Hr
        wp_apply wp_UpdateCRC dec IoE eof [F] off1 _ r.crc true $$ [Hdec] as Hdec
        · iframe Hdec Hcrc
        wp_for_post
        iframe
        iexists off1, r.crc
        iframe
        isplitl [Hr]
        · iapply ownRec_any $$ Hr
        ipureintro
        have := hnext _ hnc rfl
        rwa [show rdCrc (W32 0) r = r.crc by simp [rdCrc, hT]] at this
      · ihave #Hde2 := Hde
        iunfold decEnv at Hde2
        icases Hde2 with ⟨-, -, #Hfmt, -, -, -, -, -, -, ⟨%ecm, #Hcm, #Hcmok, #Hcmnot⟩, -⟩
        wp_apply wp_Validate «$r0_ptr» r c1x ecm _ eof $$ [Hr] as %verr ⟨Hr, Hv⟩
        · iframe Hr; iframe #
        icases Hv with (⟨%hv1, %hv2⟩ | ⟨%hne, %ei, %hei, -, -⟩)
        · subst hv1
          have hnc : ¬ (r.typ = crcType ∧ crcRecBad c1x r) := fun h => h.2.2 hv2
          try wp_auto
          wp_apply wp_GetCrc $$ Hr as Hr
          wp_apply wp_UpdateCRC dec IoE eof [F] off1 _ r.crc true $$ [Hdec] as Hdec
          · iframe Hdec Hcrc
          wp_for_post
          iframe
          iexists off1, r.crc
          iframe
          isplitl [Hr]
          · iapply ownRec_any $$ Hr
          ipureintro
          have := hnext c1x hnc rfl
          rwa [show rdCrc c1x r = r.crc by simp [rdCrc, hT]] at this
        · -- a bad CRC: `false`
          subst hei
          try wp_auto
          wp_for_post
          repair_stream
          repair_open
          repair_false
    · -- not a CRC record
      have hnc : ¬ (r.typ = crcType ∧ crcRecBad c1x r) := fun h => Hif h.1
      wp_for_post
      iframe
      iexists off1, c1x
      iframe
      isplitl [Hr]
      · iapply ownRec_any $$ Hr
      ipureintro
      have := hnext c1x hnc rfl
      have hT : ¬ r.typ = crcType := Hif
      rwa [show rdCrc c1x r = c1x by simp [rdCrc, hT]] at this
  · -- `io.EOF`: the pin put back unchanged, `true`
    subst err
    ihave %hnn := decEnv_nonnil IoE eof ueof $$ Hde
    obtain ⟨ei, rfl⟩ : ∃ ei, eof = GoInterface.ok ei := by
      cases eof with
      | ok ei => exact ⟨ei, rfl⟩
      | nil => exact absurd rfl hnn.1
    repair_open
    try wp_auto
    ihave #Hea := Heofa
    iunfold isEofAns at Hea
    wp_apply Hea as %b %hb
    subst hb
    rw [decide_eq_true rfl]
    try wp_auto
    wp_apply wp_lockedName wp_Name lf f fd _ _ $$ [Hf] as Hf
    · iframe Hf Hlf
    wp_apply wp_String as %f1 -
    try wp_auto
    wp_apply wp_Error as %f2 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    try wp_auto
    wp_apply wp_Info lg _ _ $$ []
    · iframe #
    try wp_auto
    wp_for_post
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    ihave HS : segRes gL $$ [Hm Hb]
    · unfold segRes; iframe
    imod walInv_unpinLast walCodec Mr R jr r dir lay.j X hj gL hSz $$ Hinv Hnc Hl [Htf Hnf] Ho HS Hj Hkey
      with ⟨Hnc, Hu⟩
    · iframe
    imodintro
    iframe Hnc
    wp_apply wp_lockedClose wp_Close lf f fd _ _ $$ [Hf Hfd] as %cerr -
    · iframe; iframe #
    try wp_auto
    try imodintro
    try wp_auto
    iapply HΦ
    iframe Hp Hres Hperm
    isplitl [Hu]
    · ileft; iexact Hu
    iexists o; iexact HQ
  · -- any other error
    sorry

end proof

end EtcdGrove
end Perennial
