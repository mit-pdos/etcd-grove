/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/Repair.lean` (W7 of
`notes/wal-fsext-plan.md`; the W7-W12 log, fourteenth session), in Go's order: `openLast` (the update
committed unchanged and the last segment pinned, law L1); the decoder over `fileutil.NewFileReader(f.File)`
(law L2: every stop at the end of the last segment's frames, `RepairDecode.lean`); on `io.EOF` the pin put
back unchanged (`walInv_unpinLast`); on `io.ErrUnexpectedEOF` the `.broken` file (law L3: `walInv_keyExcl`,
then `walBroken_osAUnc` or `walInv_lendOther`, `RepairBroken.lean`), `f.Seek(0, io.SeekStart)`, `io.Copy`
(`io.CopyFiles.spec`, a hypothesis), the file given back (`walInv_unlendOther`), the tail registered pending
(`walInvRegisterPendLaw_holds`, at the stream's end `wr`: `repairFile_unique`), the truncate at the decoder's
`LastOffset()` (`wr`, or past it the end of a pending run, P6: `os.File.Truncate.specRepTail`) and the
fsync (`fileutil.Fsync.specRepTail`), the put-back by the pending token (`walInv_repairPut`, L5), `walFsyncSec.Observe`; the deferred closes. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLoans
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Repair
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.openLast
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.RepairCallees
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.NewDecoder
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__Decode
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__LastOffset
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__LastCRC
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__UpdateCRC
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetType
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetCrc
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__Validate
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileReader
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.os.File__Name
public import Spec.os.File__Close
public import Spec.os.OpenFileTruncSN
public import Spec.io.CopyFiles
public import Spec.time.Duration__Seconds
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since
public import Proof.os.Off
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairBroken
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairLoop
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.UnregLent
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllRegCommit
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadBridge
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DecStreams
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.openAtIndexLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairLocked
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairBrokenOpen
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairReg
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DecTerm

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
variable [os_sem : os.Assumptions]
variable [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- `openLast`'s read-write open gives a readable and writable fd. -/
theorem openFd_rdwr (i : Ino) : openFd i (W64 2 ||| W64 524288) = ⟨i, true, true, none, none⟩ := by
  unfold openFd; congr

/-- **`Truncate` of a `*LockedFile`**: its embedded `*os.File`'s, any triple of it. -/
theorem wp_lockedTrunc (lf f : Loc) (x : w64) (P : IProp GF) (Q : GoInterface → IProp GF)
    (h : {{ P }} (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate")) (Val #x))
      {{ (err : GoInterface), RET #err; Q err }}) :
    {{ fileutil.lockedFile (GF := GF) lf f ∗ P }}
      (App (Val (lf @!! go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty @!!
        go!"Truncate")) (Val #x))
    {{ (err : GoInterface), RET #err; Q err }} := by
  iintro %Φ ⟨#Hlf, HP⟩ HΦ
  iunfold fileutil.lockedFile at Hlf
  iStructNamed Hlf
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply h $$ HP as %err HQ
  iapply HΦ $$ HQ

/-- A `.wal` name's `.broken` name ends in `.wal.broken`. -/
theorem repBroken_suffix_of {b : GoString} (h : walNameP b = true) : go!".wal.broken" <:+ repBroken b := by
  unfold walNameP at h
  obtain ⟨t, ht⟩ := of_decide_eq_true h
  exact ⟨t, by rw [repBroken, ← ht, List.append_assoc]; rfl⟩

set_option hygiene false in
/-- **A `false` exit** with the segment's file and fd (`Hf`, `Hfd`): the deferred `f.Close()`, then the
post with the token lost (`Repair.spec`'s `false` arm). Unhygienic: it names `Repair`'s hypotheses. -/
macro "repair_false" : tactic => `(tactic| (
    wp_apply wp_lockedClose wp_Close lf f fd _ _ $$ [Hf Hfd Hlks] as %cerr -
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
/-- **A `false` exit after the `.broken` file's open** (`Hbf`, `Hbfd`): its deferred `bf.Close()` first,
then `repair_false`. Unhygienic. -/
macro "repair_false_bf" : tactic => `(tactic| (
    wp_apply (wp_Close bf bfd _ _) $$ [Hbf Hbfd Hblt] as %cerr2 -
    · iframe; iframe #
    try wp_auto
    repair_false))

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
    icases HS with ⟨⟨%hqp, -⟩, Hf, Hfd, Hlks, Hoff, Hm, Hb⟩
    ihave Hlks := fdLocksW_locks _ _ $$ Hlks))

/-- See the file header. -/
theorem wal.Repair.wp_proof (Mr : WalMarshal)
    (hEnv : WalDecEnvSupply (GF := GF))
    (wp_IsEof : errors.IsPathErrnoEof.spec (GF := GF) (hG := hG))
    (wp_Term : errors.IsPathErrnoTerm.spec (GF := GF) (hG := hG))
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
  intro lg R jr r dir nm qp Q ic hin hnmO hr hdl
  have hdl' : dir.length < 4096 := hdl.1
  wp_start as ⟨#Hzap, #Hok, Hp, Hres, Hperm, Hu, Hau⟩
  ihave #Hok' := Hok
  iunfold WalFs.walAreaOk at Hok'
  icases Hok' with ⟨#Hinv, #Hosi, #Hsi, %hrb0, %hrb1, -⟩
  have hrb := And.intro hrb0 hrb1
  icases osPathS_callKey R r _ jr $$ Hp with ⟨Hp, %hkc⟩
  have hkd : callKey R dir = callKey R r := by rw [show dir = child r nm by rw [hin.2]; simp [child]; rfl]; exact hkc nm
  rw [← hkd]
  ihave %hlgn := zapLoggerOk_ne_null lg $$ Hzap
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  rw [decide_eq_false hlgn]
  try wp_auto
  wp_apply wp_openLast lg R jr r dir nm qp Q ic hin hnmO hr hdl $$ [Hp Hres Hperm Hu Hau]
    as %lf %err ⟨Hp, Hres, Hperm, %o, HQ, Hcase⟩
  · (try rw [hkd]); iframe; iframe #
  (try rw [← hkd])
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
  icases Hlo with ⟨%d, %lay, %X, %hj, %gL, %f, %fd, %qd, %lo, %lk, %I, %hfacts, #Hkey, Hl, ⟨Htf, Hnf⟩, Ho, HS, Hj,
    Hpd, #Hlf, Hf, Hoff, Hfd, Hlks⟩
  obtain ⟨hljr, hX, hcoh, habs, hidle, hnd, hsn, hgL, hfd, hgLok⟩ := hfacts
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
  ihave #HdF := walDecFile_ok wp_Stat wp_Size wp_FName wp_IsEof wp_Term IoE hIo eof hIoEof rl f fd
    (child dir gL.name) ⟨gL.ino, true, true, lo, lk⟩ gL hfd rfl rfl hSz hlen
    $$ []
  · iframe #
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.ty) #rl]
  isplitr
  · ipureintro; rfl
  iintro %rsl ⟨Hrsl, -⟩
  try wp_auto
  generalize hF : walDecFile (GF := GF) rl f fd (child dir gL.name) ⟨gL.ino, true, true, lo, lk⟩ gL = F at *
  wp_apply wp_NewDecoder _ [F] IoE eof $$ [Hrsl Hf Hfd Hlks Hoff Hm Hb] as %dI ⟨%dec, %hdI, Hrsl, Hdec⟩
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
  obtain ⟨rs, -, hRF, -⟩ := walRepairFile walCodec_ok habs hidle.1 hidle.2.1 gL hgL
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
  icases Hpost with ⟨Hpost, #Hans, #Hue0⟩
  have hRF' : RepairFile walCodec F.bs rs := by rw [hFbs]; exact hRF
  ihave Hn := repair_decNorm dec «$r0_ptr» IoE eof ueof F rs off c err hRF' hat hIoN $$ [Hde Hpost]
  · iframe Hpost Hde Hue0
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
        ihave %heofT := decEnv_eof_target _ _ _ $$ Hde
        wp_apply wp_Validate «$r0_ptr» r c1x ecm eof heofT $$ [Hr] as %verr ⟨Hr, Hv⟩
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
    icases walLockedTokI_incQ (W := W) I $$ Hl with ⟨HI, Hl⟩
    imod walInv_returnHLoans1 walCodec Mr R jr r dir _ lay.j lay.j X qd I rfl $$ Hinv Hnc Hkey HI Hnf Hpd
      with ⟨Hnc, HI, Hnf⟩
    ihave Hl := Hl $$ HI
    imod walInv_unpinLast walCodec Mr R jr r dir lay.j X hj gL hSz I $$ Hinv Hnc Hl [Htf Hnf] Ho HS Hj Hkey
      with ⟨Hnc, Hu⟩
    · iframe
    imodintro
    iframe Hnc
    wp_apply wp_lockedClose wp_Close lf f fd _ _ $$ [Hf Hfd Hlks] as %cerr -
    · iframe; iframe #
    try wp_auto
    try imodintro
    try wp_auto
    iapply HΦ
    iframe Hp Hres Hperm
    isplitl [Hu]
    · ileft; iexact Hu
    iexists o; iexact HQ
  · -- any other error: `errors.Is(err, io.ErrUnexpectedEOF)` true only at the end of the frames
    obtain ⟨ei, rfl⟩ : ∃ ei, err = GoInterface.ok ei := by
      cases err with
      | ok ei => exact ⟨ei, rfl⟩
      | nil => exact absurd rfl hne.1
    repair_open
    try wp_auto
    iunfold decAns at Hans
    icases Hans with (%h | #Hea)
    · exact absurd h hne.1
    iunfold isEofAns at Hea
    wp_apply Hea as %b %hb
    subst hb
    rw [decide_eq_false hne.2]
    try wp_auto
    iunfold errUeAns at Hue
    wp_apply Hue as %bu %hbu
    try wp_auto
    cases bu
    · -- `default`: `false`
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
      wp_apply wp_Warn lg _ _ $$ []
      · iframe #
      try wp_auto
      wp_for_post
      repair_false
    · -- `io.ErrUnexpectedEOF`, at the end of the frames: the copy, the truncate, the fsync
      have hoff : off = (recFrames walCodec rs).length := hbu rfl
      rw [decide_eq_true rfl]
      try wp_auto
      wp_apply wp_lockedName wp_Name lf f fd _ _ $$ [Hf] as Hf
      · iframe Hf Hlf
      try wp_auto
      -- the ghost steps: the `.broken` name not left out of the key's claim; the tail registered pending
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod walInv_keyExcl walCodec Mr R jr r ⊤ CoPset.subseteq_top dir _ lay.j X $$ Hinv Hnc Hkey
        with ⟨Hnc, %hXb⟩
      imod repair_register Mr R jr r dir I d lay X hj gL rs habs hnd hsn hgL hSz hRF
        $$ Hinv Hnc Hkey Hl Hj Htf Hm Hb with ⟨Hnc, Hl, Hj, Hm, Hb, %γ, %H, %md, %cuts, %k, %wr, Htf, Hpt, Hv, ⟨%hwrS, %hwt, %hTM⟩⟩
      imodintro
      iframe Hnc
      rw [child_repBroken]
      -- `createNewWALFile[*os.File](brokenName, true)`
      have hbt : go!".wal.broken" <:+ repBroken gL.name := repBroken_suffix_of (hsn.1 gL hgLm).1
      wp_apply (repair_brokenOpen wp_cNWF wp_OpenN walCodec Mr R jr r dir I (DFrac.own qd) lay.j X hj
          ⟨[gL.ino], [(lay.j, .except X)], []⟩ (repBroken gL.name) (repBroken_nameOk hgLok) hbt hXb
          (by simp) (by simp [lendKey]))
        $$ [Hpd Hperm Hj Ho Hl] as %bf %bferr ⟨Hpd, Hperm, Hl, Hbo⟩
      · iframe; iframe #
      icases Hbo with (⟨%hbe, Hbo⟩ | %hbe)
      rotate_left
      · -- the open failed: `false`
        rcases bferr with ei' | _
        rotate_left
        · exact absurd rfl hbe
        try wp_auto
        wp_apply wp_String as %f1 -
        try wp_auto
        wp_apply wp_Error as %f2 -
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        try wp_auto
        wp_apply wp_Warn lg _ _ $$ []
        · iframe #
        try wp_auto
        wp_for_post
        repair_false
      subst hbe
      iunfold repBrokenOk at Hbo
      icases Hbo with ⟨%bfd, %bi, %hj', ⟨%hbfd, %hbi⟩, Hbf, Hboff, Hbfd, Htr, Hj, Ho⟩
      ihave Hblt : lockToks bfd (openFd bi (wal.walOpenFlag true ||| W64 0x80000)) $$ []
      · iapply lockToks_unlocked <;> rfl
      try wp_auto
      -- `f.Seek(0, io.SeekStart)`
      wp_apply wp_lockedSeekStart lf f fd _ _ _ (W64 0) hfd (by decide) (by decide) $$ [Hf Hoff]
        as ⟨Hf, Hoff⟩
      · iframe Hf Hoff Hlf
      try wp_auto
      -- `io.Copy(bf, f)`
      have hbw : (openFd bi (wal.walOpenFlag true ||| W64 0x80000)).writable = true := by
        unfold openFd wal.walOpenFlag; simp only [↓reduceIte]; decide
      have hm62 : gL.om.size < 2 ^ 61 := by
        have h2 : Fs.maxBytes = 0xffffffff000 := rfl; omega
      wp_apply (wp_Copy bf bfd (child dir (repBroken gL.name)) (openFd bi (wal.walOpenFlag true ||| W64 0x80000))
          lf f fd (child dir gL.name) ⟨gL.ino, true, true, lo, lk⟩ (W64 0) (DFrac.own (1 : Qp).half)
          (DFrac.own (1 : Qp).half) gL.om gL.bs hbw rfl hbfd hfd (by decide) (by simp) hSz.symm hm62)
        $$ [Hbf Hbfd Hboff Htr Hf Hfd Hoff Hm Hb] as %cn %cerr ⟨Hbf, Hbfd, Hf, Hfd, Hm, Hb, Hcd, %od, %os', Hboff, Hoff, %hcp⟩
      · iframe; iframe #
      rcases cerr with ei' | _
      · -- the copy failed: `false`
        try wp_auto
        wp_apply wp_lockedName wp_Name lf f fd _ _ $$ [Hf] as Hf
        · iframe Hf Hlf
        wp_apply wp_String as %f1 -
        try wp_auto
        wp_apply wp_String as %f2 -
        try wp_auto
        wp_apply wp_Error as %f3 -
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        try wp_auto
        wp_apply wp_Warn lg _ _ $$ []
        · iframe #
        try wp_auto
        wp_for_post
        repair_false_bf
      obtain ⟨hos, -⟩ := hcp rfl
      try wp_auto
      -- the `.broken` file given back
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      have hD : lendKey lay.j (repBroken gL.name) ∉
          (⟨[gL.ino], [(lay.j, .except X)], []⟩ : WalOut).D := by simp [lendKey]
      icases walLockedTokI_incQ I $$ Hl with ⟨HIq, HlB⟩
      imod walInv_unlendOther walCodec Mr R jr r ⊤ CoPset.subseteq_top dir I lay.j X hj' (DFrac.own (1 : Qp).half)
          _ (repBroken gL.name) (.file bi) (walNameP_broken hbt) (by simp [WalOut.addClaim]) hbi
        $$ Hinv Hnc Hkey HIq Hj Ho [Hcd] with ⟨Hnc, Hj, HIq, Ho⟩
      · simp only [tmpEnt]; iapply io.copyDst_trFile $$ Hcd
      ihave Hl := HlB $$ HIq
      rw [WalOut.delClaim_addClaim _ _ hD]
      imodintro
      iframe Hnc
      -- `f.Truncate(lastOffset)`, by the pending token
      subst hoff
      have hle : (recFrames walCodec rs).length ≤ gL.om.size := by
        have := hRF.pre.length_le; simp only [segImg, List.length_map] at this; omega
      wp_apply (wp_lockedTrunc lf f _ _ _
          (wp_Trunc R jr r f fd (child dir gL.name) dir γ gL.ino H md cuts wr _ gL.om.size k os' hwt hle hwrS))
        $$ [Hf Hfd Hlks Hoff Hpt Hm Hb Hv] as %terr Htr
      · iframe Hok Hlf
        iunfold walTailPO
        iframe Hf Hoff Hpt
        isplitl [Hfd Hlks]
        · iexists true, lo, lk; iframe
        iexists gL.om, gL.bs
        iframe Hm Hb
        isplitr
        · ipureintro; exact ⟨rfl, hTM, by omega, hfd⟩
        iunfold tailVar at Hv; iexact Hv
      icases Htr with (⟨%hte, Htw⟩ | ⟨%hte, Hf, ⟨%rd, %lo, %lk, Hfd, Hlks⟩, Hoff⟩)
      rotate_left
      · -- the truncate failed: `false`
        rcases terr with ei' | _
        rotate_left
        · exact absurd rfl hte
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
        wp_apply wp_Warn lg _ _ $$ []
        · iframe #
        try wp_auto
        wp_for_post
        repair_false_bf
      subst hte
      try wp_auto
      -- `fileutil.Fsync(f.File)`
      wp_apply wp_Now as %t0 -
      try wp_auto
      iunfold walLockedTokI at Hl
      icases Hl with ⟨Htk, Hpk, Hcf, HIl⟩
      wp_apply (wp_Fsync R jr r f fd (child dir gL.name) dir γ gL.ino H md cuts wr _ k os' hwrS)
        $$ [Htw Hcf] as %ferr ⟨Hcf, Hf, ⟨%rd, %lo, %lk, Hfd, Hlks⟩, Hoff, Hfr⟩
      · iframe Htw Hcf Hok
      icases Hfr with (⟨%hfe, ⟨%k2, Hkt⟩, %m2, %bs2, Hm2, Hb2, %hTM2, Hv⟩ | %hfe)
      rotate_left
      · -- the fsync failed: `false`
        rcases ferr with ei' | _
        rotate_left
        · exact absurd rfl hfe
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
        wp_apply wp_Warn lg _ _ $$ []
        · iframe #
        try wp_auto
        wp_for_post
        repair_false_bf
      subst hfe
      try wp_auto
      -- `walFsyncSec.Observe(time.Since(start).Seconds())`
      ihave #Henv := wal_encEnv $$ Hpkg
      iunfold encEnv at Henv
      icases Henv with ⟨-, -, -, #Htime, #Hmet⟩
      iunfold wal.metricsInit at Hmet
      icases Hmet with ⟨⟨%hs, #Hhs, #Hhspec⟩, -, -⟩
      iunfold wal.histSpec at Hhspec
      wp_apply wp_Since as %dur -
      try wp_auto
      haveI _hni : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
      wp_pures
      wp_apply (wp_Seconds dur) as %fl -
      try wp_auto
      wp_apply Hhspec
      try wp_auto
      -- `lg.Info("repaired", ...)`
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
      -- the put-back (L5's changed case), then the deferred closes
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      ihave Hv' : tailVar (W := W) γ ((H, md, cuts, wr, gL.ino, none) : TailG)
        $$ [Hv]
      · iunfold tailVar; iexact Hv
      imod walInv_returnHLoans1 walCodec Mr R jr r dir _ lay.j lay.j X qd I rfl $$ Hinv Hnc Hkey HIl Hnf Hpd
        with ⟨Hnc, HIl, Hnf⟩
      ihave Hl : walLockedTokI (W := W) I $$ [Htk Hpk Hcf HIl]
      · unfold walLockedTokI; iframe
      imod walInv_repairPut Mr R jr r dir γ k2 H md cuts _ m2 bs2 lay.j X hj' gL I hTM2.2 hwrS
        $$ Hinv Hnc Htf Hkt Hv' Hm2 Hb2 Hl Hnf Ho Hj Hkey with ⟨Hnc, Hu⟩
      imodintro
      iframe Hnc
      wp_apply (wp_Close bf bfd _ _) $$ [Hbf Hbfd Hblt] as %cerr2 -
      · iframe; iframe #
      try wp_auto
      wp_apply wp_lockedClose wp_Close lf f fd _ _ $$ [Hf Hfd Hlks] as %cerr -
      · iframe; iframe #
      try wp_auto
      try imodintro
      try wp_auto
      iapply HΦ
      iframe Hp Hres Hperm
      isplitl [Hu]
      · ileft; iexact Hu
      iexists o; iexact HQ

end proof

end EtcdGrove
end Perennial
