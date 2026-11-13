/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/decoder__decodeRecord.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__decodeRecord
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__isTornEntry
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.readInt64
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decodeFrameSize
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__Reset
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetType
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__Validate
public import LinuxFs.Spec.google_golang_org.protobuf.proto.UnmarshalWalRecord
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader__FileInfo
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader__Err
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader__Read
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.digest__Sum32
public import Spec.io.ReadFull
public import Spec.encoding.binary.ReadInt64LE
public import LinuxFs.Spec.fmt.ErrorfErrs
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.digest__Write
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.decoder.decodeRecord.wp_proof
    (HUnm : ∀ C, proto.UnmarshalWalRecord.spec (GF := GF) (hG := hG) C)
    (HReset : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Reset.spec (GF := GF) (hG := hG))
    (HGetType : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetType.spec (GF := GF) (hG := hG))
    (HValidate : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Validate.spec (GF := GF) (hG := hG))
    (HErrorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG))
    (HTorn : go_etcd_io.etcd.server.v3.storage.wal.decoder.isTornEntry.spec (GF := GF) (hG := hG))
    (HRI : go_etcd_io.etcd.server.v3.storage.wal.readInt64.spec (GF := GF) (hG := hG))
    (HDFS : go_etcd_io.etcd.server.v3.storage.wal.decodeFrameSize.spec (GF := GF) (hG := hG))
    (HRF : io.ReadFull.spec (GF := GF) (hG := hG))
    (HFI : go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.FileInfo.spec (GF := GF) (hG := hG))
    (HErr : go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.Err.spec (GF := GF) (hG := hG))
    (HRead : go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.Read.spec (GF := GF) (hG := hG))
    (HWrite : go_etcd_io.etcd.pkg.v3.crc.digest.Write.spec (GF := GF) (hG := hG))
    (HSum : go_etcd_io.etcd.pkg.v3.crc.digest.Sum32.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.decoder.decodeRecord.spec (GF := GF) (hG := hG) := by
  intro C d rp IoE eof ueof fs
  induction fs with
  | nil =>
    intro off c hC
    wp_start as ⟨#Henv, Hd, Hr⟩
    iunfold ownDecoder at Hd
    icases Hd with ⟨%sl, %fbrs, %h, %rs, #Hmu, Hbrs, #Hsl, Hoff, Hcrc, Hcont, Hdc, Hfbrs, %Hinv⟩
    wp_auto
    wp_apply wp_with_defer as %defer Hdefer
    ihave %Hl := ownFbrs_len IoE eof fbrs [] rs $$ Hfbrs
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    have hfbrs : fbrs = [] := List.length_eq_zero_iff.mp (by simpa using Hl.1)
    subst hfbrs
    have hsl : sl.len = W64 0 := by simp at Hsll; word
    iunfold decEnv at Henv
    icases Henv with ⟨#Hio, #Hbin, #Hfmt, #Hsync, #Hbufio, #Heof, #Hueof, #Heok, #Htab, #Hcm⟩
    wp_if_destruct
    · iapply HΦ
      iunfold decPost
      ileft
      iexists 0
      simp only [goDecode, List.drop_zero, List.map_nil, decide_true]
      isplitl []
      · ipureintro; simp [stopErr]
      isplitl [Hr]
      · iunfold ownRecAny; iexists _; iexact Hr
      iunfold ownDecoder
      iexists sl, [], h, rs
      iframe
      iframe Hmu Hsl
      ipureintro
      exact Hinv
    · exact absurd hsl (by assumption)
  | cons F fs IH =>
    intro off c hC
    wp_start as ⟨#Henv, Hd, Hr⟩
    iunfold ownDecoder at Hd
    icases Hd with ⟨%sl, %fbrs, %h, %rs, #Hmu, Hbrs, #Hsl, Hoff, Hcrc, Hcont, Hdc, Hfbrs, %Hinv⟩
    wp_auto
    wp_apply wp_with_defer as %defer Hdefer
    ihave %Hl := ownFbrs_len IoE eof fbrs (F :: fs) rs $$ Hfbrs
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    obtain ⟨hoff, hrs⟩ := Hinv
    have hrs := hrs rfl
    subst hrs
    rcases fbrs with _ | ⟨fbr, fbrs⟩
    · simp at Hl
    simp only [liveRs, ownFbrs]
    icases Hfbrs with ⟨Hfbr, Hfbrs⟩
    iunfold decEnv at Henv
    icases Henv with ⟨#Hio, #Hbin, #Hfmt, #Hsync, #Hbufio, #Heof, #Hueof, #Heok, #Htab, #Hcm⟩
    have hsl0 : 0 < sint.Z sl.len := by
      have h1 : (fbr :: fbrs).length = (sint.Z sl.len).toNat := Hsll.1
      simp only [List.length_cons] at h1
      omega
    have hz : sint.Z (W64 0) = 0 := rfl
    have hsl : sl.len ≠ W64 0 := by
      intro h0; rw [h0, hz] at hsl0; exact absurd hsl0 (by decide)
    wp_if_destruct
    · exact absurd (by assumption) hsl
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len from ⟨by rw [hz]; decide, by rw [hz]; exact hsl0⟩)]
    wp_apply wp_load_slice_index sl (sint.Z (W64 0)) (fbr :: fbrs) DFrac.discard fbr (by rw [hz]; decide) $$ [Hsl] as -
    · iframe Hsl; ipureintro; rfl
    iunfold ownFbr at Hfbr
    icases Hfbr with ⟨%b, %fi, %ferr, #Hf, #HF, Hb, %Hferr, Hfi⟩
    wp_apply HErr fbr b fi ferr DFrac.discard $$ [Hf] as -
    · iexact Hf
    rcases ferr with _ | fii
    · -- `Err()` failed: return its error
      wp_auto
      iapply HΦ
      iunfold decPost
      iright
      isplitl []
      · ipureintro; exact Hferr (by simp)
      isplitl [Hr]
      · iunfold ownRecAny; iexists _; iexact Hr
      iexists (F :: fs), off, c
      iunfold ownDecoder
      iexists sl, fbr :: fbrs, h, (F.bs.take off :: fs.map (fun _ => []))
      iframe
      iframe Hmu Hsl
      isplitl [Hb Hfi Hfbrs]
      · simp only [ownFbrs]
        isplitl [Hb Hfi]
        · iunfold ownFbr
          iexists b, fi, _
          iframe
          iframe Hf HF
          ipureintro; exact Hferr
        · iexact Hfbrs
      ipureintro
      simp [hoff]
    wp_auto
    ihave #Hfio := Hfi $$ []
    · ipureintro; rfl
    sorry

end proof

end EtcdGrove
end Perennial
