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
    ihave #HI := io.isInit_access $$ Hio
    icases HI with ⟨-, -, -, -, #HE1, #HU1, -⟩
    iunfold errors.newVar at HE1
    icases HE1 with ⟨%x1, #Hx1, -⟩
    ihave ⟨%x2, #Hx2, #HUerr⟩ := errOk_newVar _ _ $$ HU1
    icombine Heof Hx1 gives %he
    icombine Hueof Hx2 gives %hu
    have heofn : eof ≠ GoInterface.nil := by rw [he]; simp [interface.mkOk]
    have hueofn : ueof ≠ GoInterface.nil := by rw [hu]; simp [interface.mkOk]
    iunfold isEofOk at Heok
    icases Heok with ⟨%Hneq, #Heok⟩
    ihave #Hrs := fbr_readerStream HRead IoE eof F fbr b fi GoInterface.nil $$ [Hf HF]
    · iframe Hf HF
    wp_apply HRI ⟨go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.ty, #fbr⟩
      _ _ (F.bs.take off) eof ueof $$ Hrs [Hb] as %l %err ⟨%ys, %Hys, Hb⟩
    · iframe
      iframe Heof Hueof
    ihave ⟨%Hpre, Hb⟩ := ownReader_prefix IoE eof F b _ _ $$ [HF Hb]
    · iframe HF Hb
    rw [← he]
    ihave #HIs := Heok $$ %err %(readFull_err_cases Hys.1)
    wp_apply HIs as %bIs %HbIs
    subst HbIs
    have hnil8 : err = GoInterface.nil → ys.length = 8 := by
      intro hn
      rcases Hys.1 with ⟨h, _⟩ | ⟨_, e, he', _, h1, h2⟩
      · exact h
      · exfalso
        by_cases hc : e = eof ∧ ys ≠ []
        · exact hueofn (h1 hc ▸ hn)
        · exact he' (h2 hc ▸ hn)
    by_cases hdrop : err = eof ∨ (err = GoInterface.nil ∧ l = W64 0)
    · have hstep : decRecStep C fs.isEmpty F.bs off c = .eof := by
        rcases hdrop with hE | ⟨hN, hL⟩
        · obtain ⟨_, hr, hc⟩ := readFull_short Hys.1 Hneq.2 (hE ▸ heofn) (hE ▸ Hneq.2)
          rcases hc with ⟨_, rfl⟩ | ⟨h1, _⟩
          · apply decRecStep_end
            have := congrArg List.length hr
            simp only [List.append_nil, List.length_take] at this
            omega
          · exact absurd (hE.symm.trans h1) Hneq.1
        · have h8 := hnil8 hN
          obtain ⟨hle, ht⟩ := take_append_prefix Hpre (by intro h; rw [h] at h8; simp at h8)
          have htk : (F.bs.drop off).take 8 = ys := by
            obtain ⟨t, ht⟩ := ht; rw [← ht, ← h8]; simp
          apply decRecStep_zero (by simp; omega)
          rw [htk, ← Hys.2 hN, hL]; rfl
      rcases hdrop with hE | ⟨hN, hL⟩
      all_goals first
        | (rw [decide_eq_true hE]; wp_auto)
        | (subst hN hL; rw [decide_eq_false heofn.symm]; wp_auto)
      all_goals
        ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
        have h1z : sint.Z (W64 1) = 1 := rfl
        rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z sl.len ∧
          sint.Z sl.len ≤ sint.Z sl.cap from ⟨by rw [h1z]; decide, by rw [h1z]; omega, Hwf.2⟩)]
        ihave Hsl3 := (ownSlice_slice (W64 1) sl.len sl DFrac.discard (fbr :: fbrs)
          ⟨by rw [h1z]; decide, by rw [h1z]; omega, Int.le_refl _⟩).1 $$ Hsl
        icases Hsl3 with ⟨-, #Hsl', -⟩
        have hsub : subslice (sint.nat (W64 1)) (sint.nat sl.len) (fbr :: fbrs) = fbrs := by
          have h1 : (fbr :: fbrs).length = sint.nat sl.len := Hsll.1
          have h1n : sint.nat (W64 1) = 1 := rfl
          rw [← h1, h1n]; simp [subslice]
        rw [hsub]
        wp_auto
        wp_if_destruct
        · -- the last file: `io.EOF`
          have hfbrs0 : fbrs = [] := by
            have h1 : (fbr :: fbrs).length = (sint.Z sl.len).toNat := Hsll.1
            simp only [List.length_cons] at h1
            have : sint.Z sl.len = 1 := by
              have := congrArg sint.Z Hif; revert this; word
            rw [this] at h1
            exact List.length_eq_zero_iff.mp (by omega)
          subst hfbrs0
          have hfs0 : fs = [] := List.length_eq_zero_iff.mp (by simpa using Hl.1.symm)
          subst hfs0
          iapply HΦ
          iunfold decPost
          ileft
          iexists 1
          rw [show ([F] : List (DecFile GF)).map (·.bs) = [F.bs] from rfl,
            goDecode_eof_last (by simpa using hstep)]
          simp only [List.drop_succ_cons, List.drop_zero, List.map_nil]
          isplitl []
          · ipureintro; simp [stopErr]
          isplitl [Hr]
          · iunfold ownRecAny; iexists _; iexact Hr
          iunfold ownDecoder
          iexists _, [], h, []
          iframe
          iframe Hmu Hsl'
          ipureintro
          simp [hoff, liveRs]
        · -- the next file, from offset 0
          have hfs : fs ≠ [] := by
            intro hfs0; subst hfs0
            have h1 : (fbr :: fbrs).length = (sint.Z sl.len).toNat := Hsll.1
            have h2 : fbrs = [] := List.length_eq_zero_iff.mp (by simpa using Hl.1)
            subst h2
            simp only [List.length_cons, List.length_nil] at h1
            apply Hif
            have : sint.Z sl.len = 1 := by omega
            word
          wp_apply (IH 0 c hC) $$ [Hr Hbrs Hoff Hcrc Hcont Hdc Hfbrs] as %err' Hpost
          · iframe Hr
            isplitr
            · iunfold decEnv
              iframe
              iframe Hio Hbin Hfmt Hsync Hbufio Heof Hueof Htab Hcm
              iunfold isEofOk
              iframe Heok
              ipureintro; exact Hneq
            iunfold ownDecoder
            iexists _, fbrs, h, (fs.map (fun _ => []))
            iframe
            iframe Hmu Hsl'
            ipureintro
            refine ⟨by omega, fun _ => ?_⟩
            rcases fs with _ | ⟨G, gs⟩
            · exact absurd rfl hfs
            · simp [liveRs]
          iapply HΦ
          iapply decPost_cons_eof C d rp IoE eof ueof F fs off c err' hstep hfs
          iexact Hpost
    rw [decide_eq_false (fun h => hdrop (Or.inl h))]
    by_cases hn : err ≠ GoInterface.nil
    · -- a failed read of the length word
      obtain ⟨ei, rfl⟩ : ∃ ei, err = GoInterface.ok ei := by
        cases err with
        | ok ei => exact ⟨ei, rfl⟩
        | nil => exact absurd rfl hn
      wp_auto
      iapply HΦ
      iunfold decPost
      by_cases hI : IoE (GoInterface.ok ei)
      · iright
        isplitl []
        · ipureintro; exact hI
        isplitl [Hr]
        · iunfold ownRecAny; iexists _; iexact Hr
        iexists (F :: fs), off, c
        iunfold ownDecoder
        iexists sl, fbr :: fbrs, h, ((F.bs.take off ++ ys) :: fs.map (fun _ => []))
        iframe
        iframe Hmu Hsl
        isplitl [Hb Hfbrs]
        · simp only [ownFbrs]
          isplitl [Hb]
          · iunfold ownFbr
            iexists b, fi, _
            iframe
            iframe Hf HF Hfio
            ipureintro; simp
          · iexact Hfbrs
        ipureintro
        simp [hoff]
      · obtain ⟨hlt, hr, hc⟩ := readFull_short Hys.1 Hneq.2 hn hI
        rcases hc with ⟨h1, _⟩ | ⟨h1, hne⟩
        · exact absurd h1 (fun h => hdrop (Or.inl h))
        obtain ⟨hlen, hdrop'⟩ := take_append_eq hr hne
        have hstep : decRecStep C fs.isEmpty F.bs off c = .stop .shortLen c := by
          apply decRecStep_shortLen
          · rw [hdrop']; exact List.length_pos_iff.mpr hne
          · rw [hdrop']; exact hlt
        ileft
        iexists 0
        have hstep' : decRecStep C (fs.map (·.bs)).isEmpty F.bs off c = .stop .shortLen c := by
          simpa using hstep
        have hg : goDecode C ((F :: fs).map (·.bs)) off c =
            .stop .shortLen ((F :: fs).map (·.bs)) off c := by
          simp only [List.map_cons]; unfold goDecode; rw [hstep']
        rw [hg]
        simp only [List.drop_zero]
        isplitl []
        · ipureintro; exact ⟨h1, trivial⟩
        isplitl [Hr]
        · iunfold ownRecAny; iexists _; iexact Hr
        iunfold ownDecoder
        iexists sl, fbr :: fbrs, h, ((F.bs.take off ++ ys) :: fs.map (fun _ => []))
        iframe
        iframe Hmu Hsl
        isplitl [Hb Hfbrs]
        · simp only [ownFbrs]
          isplitl [Hb]
          · iunfold ownFbr
            iexists b, fi, _
            iframe
            iframe Hf HF Hfio
            ipureintro; simp
          · iexact Hfbrs
        ipureintro
        simp [hoff]
    have hn : err = GoInterface.nil := Classical.byContradiction hn
    subst hn
    have hl0 : l ≠ W64 0 := fun h => hdrop (Or.inr ⟨rfl, h⟩)
    have h8 := hnil8 rfl
    have hl := Hys.2 rfl
    wp_auto
    rw [decide_eq_false hl0]
    wp_auto
    ihave %HFp := decFile_pure IoE eof F $$ HF
    obtain ⟨hle, hpre8⟩ := take_append_prefix Hpre (by intro h; rw [h] at h8; simp at h8)
    have htk : (F.bs.drop off).take 8 = ys := by
      obtain ⟨t, ht⟩ := hpre8; rw [← ht, ← h8]; simp
    have hrest8 : 8 ≤ (F.bs.drop off).length := by simp; omega
    have hframe := decRecStep_frame (C := C) (last := fs.isEmpty) (c := c) hrest8
      (by rw [htk, ← hl]; exact hl0)
    rw [htk, ← hl] at hframe
    simp only at hframe
    have hrb := decodeFrameSize_fst_lt l
    have hpad := decodeFrameSize_snd_lt l
    wp_apply +noauto HDFS l
    generalize hrbd : (decodeFrameSize l).1 = rb at hframe hrb ⊢
    generalize hpadd : (decodeFrameSize l).2 = pad at hframe hpad ⊢
    wp_auto
    wp_apply HFI fbr b fi GoInterface.nil DFrac.discard $$ [Hf] as -
    · iexact Hf
    iunfold fileInfoOk at Hfio
    icases Hfio with ⟨%fii, %Hfii, #HSize, #HName⟩
    subst Hfii
    wp_auto
    wp_apply HSize
    have hcmp : sint.Z (W64 F.bs.length - W64 off - W64 pad) < sint.Z (W64 rb) ↔
        F.bs.length < off + pad + rb := by
      have := HFp.2
      constructor <;> intro h <;> word
    by_cases htl : F.bs.length < off + pad + rb
    · rw [decide_eq_true (hcmp.mpr htl)]
      wp_auto
      wp_apply HFI fbr b _ GoInterface.nil DFrac.discard $$ [Hf] as -
      · iexact Hf
      wp_auto
      wp_apply HName as %nm -
      wp_apply HFI fbr b _ GoInterface.nil DFrac.discard $$ [Hf] as -
      · iexact Hf
      wp_auto
      wp_apply HSize
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      wp_apply HErrorf _ _ [interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x2,
          interface.mkOk go.string #nm, interface.mkOk go.int64 #(W64 rb),
          interface.mkOk go.int64 #(W64 F.bs.length), interface.mkOk go.int64 #(W64 off),
          interface.mkOk go.int64 #(W64 pad),
          interface.mkOk go.int64 #(W64 F.bs.length - W64 off - W64 pad)]
          [⟨go.GoType.PointerType errors.errorString.ty, #x2⟩] (by
          intro ii hii
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hii
          rcases hii with h | h | h | h | h | h | h <;> rw [interface.mkOk] at h <;> cases h
          · exact Or.inr (by simp)
          · exact Or.inl (argWf_string _)
          all_goals exact Or.inl (argWf_int64 _)) $$ [Hasl] as %e1 -
      · iframe
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
        iexact HUerr
      have hstep : decRecStep C fs.isEmpty F.bs off c = .stop .tooLarge c := by
        rw [hframe, ite_eq_left htl]
      iapply HΦ
      iapply decPost_stop C d rp IoE eof ueof F fs off c c _ .tooLarge hstep (by simp [stopErr])
      isplitl [Hr]
      · iunfold ownRecAny; iexists _; iexact Hr
      iapply ownDecoder_intro d IoE eof sl fbr fbrs h F fs (F.bs.take off ++ ys) off c _ hoff
        (by simp)
      iframe
      iframe Hmu Hsl
      iapply ownFbr_intro
      iframe
      iframe Hf HF
      iunfold fileInfoOk
      iexists fii
      iframe HSize HName
      ipureintro; rfl
    rw [decide_eq_false (fun h => htl (hcmp.mp h))]
    wp_auto
    have hrp : sint.nat (W64 rb + W64 pad) = rb + pad := by word
    wp_apply (wp_slice_make2 (V := w8) (W64 rb + W64 pad)) as %dsl ⟨Hdat, -⟩
    · ipureintro; word
    rw [hrp]
    wp_apply HRF ⟨go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.ty, #fbr⟩
      _ _ (F.bs.take off ++ ys) dsl _ eof ueof $$ Hrs [Hb Hdat] as %n2 %err2 ⟨%ys2, %Hys2, Hdat, Hb⟩
    · iframe
      iframe Heof Hueof
    ihave ⟨%Hpre2, Hb⟩ := ownReader_prefix IoE eof F b _ _ $$ [HF Hb]
    · iframe HF Hb
    have Hok2 := Hys2.2.2
    simp only [List.length_replicate] at Hok2
    by_cases hn2 : err2 ≠ GoInterface.nil
    · -- a failed read of the frame
      obtain ⟨ei2, rfl⟩ : ∃ ei, err2 = GoInterface.ok ei := by
        cases err2 with
        | ok ei => exact ⟨ei, rfl⟩
        | nil => exact absurd rfl hn2
      wp_auto
      ihave #HIs2 := Heok $$ %(GoInterface.ok ei2) %(readFull_err_cases Hok2)
      wp_apply HIs2 as %b2 %Hb2
      subst Hb2
      by_cases hI : IoE (GoInterface.ok ei2)
      · rw [decide_eq_false (fun (h : GoInterface.ok ei2 = eof) => Hneq.2 (h ▸ hI))]
        wp_auto
        iapply HΦ
        iapply decPost_ioe C d rp IoE eof ueof (F :: fs) (F :: fs) off off c c _ hI
        isplitl [Hr]
        · iunfold ownRecAny; iexists _; iexact Hr
        iapply ownDecoder_intro d IoE eof sl fbr fbrs h F fs (F.bs.take off ++ ys ++ ys2) off c
          false hoff (by simp)
        iframe
        iframe Hmu Hsl
        iapply ownFbr_intro
        iframe
        iframe Hf HF
        iunfold fileInfoOk
        iexists fii
        iframe HSize HName
        ipureintro; rfl
      obtain ⟨hlt2, hr2, hc2⟩ := readFull_short Hok2 Hneq.2 hn2 hI
      have hsd : (F.bs.drop off).length < 8 + rb + pad := by
        have := congrArg List.length hr2
        simp only [List.length_append, List.length_take, List.length_drop] at this ⊢
        omega
      have hstep : decRecStep C fs.isEmpty F.bs off c = .stop .shortData c := by
        rw [hframe, ite_eq_right htl, ite_eq_left hsd]
      rcases hc2 with ⟨h1, _⟩ | ⟨h1, _⟩
      all_goals first
        | rw [decide_eq_true h1]
        | rw [decide_eq_false (fun h => Hneq.1 (h1.symm.trans h).symm)]
      all_goals
        wp_auto
        iapply HΦ
        iapply decPost_stop C d rp IoE eof ueof F fs off c c _ .shortData hstep
          (by simp only [stopErr]; first | exact hu.symm | exact h1)
        isplitl [Hr]
        · iunfold ownRecAny; iexists _; iexact Hr
        iapply ownDecoder_intro d IoE eof sl fbr fbrs h F fs (F.bs.take off ++ ys ++ ys2) off c
          _ hoff (by simp)
        iframe
        iframe Hmu Hsl
        iapply ownFbr_intro
        iframe
        iframe Hf HF
        iunfold fileInfoOk
        iexists fii
        iframe HSize HName
        ipureintro; rfl
    have hn2 : err2 = GoInterface.nil := Classical.byContradiction hn2
    subst hn2
    have hlen2 : ys2.length = rb + pad := by
      rcases Hok2 with ⟨h, _⟩ | ⟨_, e, he', _, h1, h2⟩
      · exact h
      · exfalso
        by_cases hc : e = eof ∧ ys2 ≠ []
        · exact hueofn (h1 hc).symm
        · exact he' (h2 hc).symm
    have hdat : ys2 ++ (List.replicate (rb + pad) (zero_val w8)).drop ys2.length = ys2 := by
      rw [hlen2]; simp
    rw [hdat]
    have hpre2' : ys ++ ys2 <+: F.bs.drop off := by
      have := take_append_prefix (ys := ys ++ ys2) (by simpa using Hpre2) (by simp; intro h; rw [h] at h8; simp at h8)
      exact this.2
    have hnsd : ¬ (F.bs.drop off).length < 8 + rb + pad := by
      have := hpre2'.length_le; simp at this ⊢; omega
    have hdata : ((F.bs.drop off).drop 8).take (rb + pad) = ys2 := by
      obtain ⟨t, ht⟩ := hpre2'; rw [← ht, ← h8, ← hlen2]; simp
    have hstep0 : decRecStep C fs.isEmpty F.bs off c = decRecData C fs.isEmpty off c rb pad ys2 := by
      rw [hframe, ite_eq_right htl, ite_eq_right hnsd, hdata]
    have hys2l : ys2.length < 2 ^ 62 := by
      have := hpre2'.length_le; simp at this; omega
    wp_auto
    ihave %Hdl := ownSlice_len _ _ _ $$ Hdat
    ihave %Hdwf := ownSlice_wf _ _ _ $$ Hdat
    have hz0 : sint.Z (W64 0) = 0 := rfl
    have hrbz : sint.Z (W64 rb) = rb := by word
    have hrbn : sint.nat (W64 rb) = rb := by word
    have hdl : sint.Z dsl.len = rb + pad := by
      have h1 : ys2.length = (sint.Z dsl.len).toNat := Hdl.1
      omega
    have hbd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 rb) ∧ sint.Z (W64 rb) ≤ sint.Z dsl.cap := by
      rw [hz0, hrbz]; omega
    rw [ite_eq_left hbd]
    ihave Hds := (ownSlice_slice (W64 0) (W64 rb) dsl (DFrac.own 1) ys2
      ⟨by rw [hz0]; decide, by rw [hz0, hrbz]; omega, by rw [hrbz]; omega⟩).1 $$ Hdat
    icases Hds with ⟨Hd0, Hdm, Hd2⟩
    have hsub2 : subslice (sint.nat (W64 0)) (sint.nat (W64 rb)) ys2 = ys2.take rb := by
      have h0n : sint.nat (W64 0) = 0 := rfl
      rw [hrbn, h0n]; simp [subslice]
    rw [hsub2]
    wp_auto
    wp_apply HUnm C _ _ (DFrac.own 1) rp $$ [Hdm Hr] as %err3 ⟨Hdm, Hres⟩
    · iframe
    ihave Hdat := (ownSlice_slice (W64 0) (W64 rb) dsl (DFrac.own 1) ys2
      ⟨by rw [hz0]; decide, by rw [hz0, hrbz]; omega, by rw [hrbz]; omega⟩).2 $$ [Hd0 Hdm Hd2]
    · rw [hsub2]; iframe
    have hlast : decide (sl.len = W64 1) = fs.isEmpty := by
      have h1 : (fbr :: fbrs).length = (sint.Z sl.len).toNat := Hsll.1
      have h2 := Hl.1
      simp only [List.length_cons] at h1 h2
      rcases fs with _ | ⟨G, gs⟩
      · simp only [List.length_nil] at h2
        have : sint.Z sl.len = 1 := by omega
        simp only [List.isEmpty_nil, decide_eq_true_eq]
        word
      · simp only [List.length_cons] at h2
        have : 2 ≤ sint.Z sl.len := by omega
        simp only [List.isEmpty_cons, decide_eq_false_iff_not]
        intro h; rw [h] at this; revert this; word
    have Hown : ∀ (c' : w32) (live : Bool), (live = true → F.bs.take off ++ ys ++ ys2 = F.bs.take off) →
        (sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.decoder go!"mu" d) (BI.pure True : IProp GF) ∗
         structFieldRef go_etcd_io.etcd.server.v3.storage.wal.decoder go!"brs" d ↦ sl ∗
         structFieldRef go_etcd_io.etcd.server.v3.storage.wal.decoder go!"lastValidOff" d ↦ W64 off ∗
         structFieldRef go_etcd_io.etcd.server.v3.storage.wal.decoder go!"crc" d ↦ h ∗
         structFieldRef go_etcd_io.etcd.server.v3.storage.wal.decoder go!"continueOnCrcError" d ↦ false ∗
         ownDecCrc h c' ∗ fbr ↦□ go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.mk b (GoInterface.ok fii) GoInterface.nil ∗
         decFile IoE eof F ∗ sl ↦*□ (fbr :: fbrs) ∗
         bufio.ownReader b F.fr F.S (decRdErr F.bs eof IoE) (F.bs.take off ++ ys ++ ys2) ∗
         ownFbrs IoE eof fbrs fs (fs.map (fun _ => [])) ∗ fileInfoOk (GoInterface.ok fii) F.bs.length) ⊢
        ownDecoder d IoE eof (F :: fs) off c' live := by
      intro c' live hlive
      iintro ⟨#Hmu, Hbrs, Hoff, Hcrc, Hcont, Hdc, #Hf, #HF, #Hsl, Hb, Hfbrs, #Hfi⟩
      iapply ownDecoder_intro d IoE eof sl fbr fbrs h F fs (F.bs.take off ++ ys ++ ys2) off c'
        live hoff hlive
      iframe
      iframe Hmu Hsl
      iapply ownFbr_intro
      iframe
      iframe Hf HF Hfi
    ihave #Hfio : fileInfoOk (GoInterface.ok fii) F.bs.length $$ []
    · iunfold fileInfoOk
      iexists fii
      iframe HSize HName
      ipureintro; rfl
    icases Hres with (⟨%r, ⟨%herr3, %hdec⟩, Hrec⟩ | ⟨⟨%herr3, %hdec⟩, Hrec⟩)
    rotate_left
    · -- `proto.Unmarshal` failed
      obtain ⟨ei3, rfl⟩ : ∃ ei, err3 = GoInterface.ok ei := by
        cases err3 with
        | ok ei => exact ⟨ei, rfl⟩
        | nil => exact absurd rfl herr3
      wp_auto
      wp_apply HTorn d sl off dsl ys2 (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) hoff hys2l
        $$ [Hbrs Hoff Hdat] as ⟨Hbrs, Hoff, Hdat⟩
      · iframe
      rw [hlast]
      have hstep : decRecStep C fs.isEmpty F.bs off c =
          .stop (.badRec (isTorn fs.isEmpty off ys2)) c := by
        rw [hstep0]; unfold decRecData; rw [hdec]
      cases ht : isTorn fs.isEmpty off ys2
      all_goals rw [ht] at hstep
      all_goals
        wp_auto
        iapply HΦ
        iapply decPost_stop C d rp IoE eof ueof F fs off c c _ _ hstep
          (by simp only [stopErr]; first | exact hu.symm | simp)
        iframe Hrec
        iapply Hown c _ (by simp)
        iframe
        iframe Hmu Hf HF Hsl Hfio
    subst herr3
    wp_auto
    wp_apply HGetType rp r $$ Hrec as Hrec
    have hct4 : (W64 4 : w64) = crcType := rfl
    rw [hct4]
    have hpre3 : F.bs.take off ++ ys ++ ys2 <+: F.bs := Hpre2
    have hlen3 : (F.bs.take off ++ ys ++ ys2).length = off + (8 + rb + pad) := by
      simp only [List.length_append, List.length_take, h8, hlen2]; omega
    have hacc_lt : off + (8 + rb + pad) < 2 ^ 62 := by
      have := hpre3.length_le; omega
    have hacc_rs : F.bs.take off ++ ys ++ ys2 = F.bs.take (off + (8 + rb + pad)) := by
      rw [← hlen3]; exact List.prefix_iff_eq_take.mp hpre3
    have hacc_off : W64 off + (W64 8 + W64 rb + W64 pad) = W64 (off + (8 + rb + pad) : Nat) := by
      push_cast; word
    by_cases hct : r.typ = crcType
    · -- a CRC record: accepted unchecked
      rw [decide_eq_true hct]
      wp_auto
      have hstep : decRecStep C fs.isEmpty F.bs off c = .accept r (8 + rb + pad) c := by
        rw [hstep0]; unfold decRecData; rw [hdec]; simp [hct]
      rw [hacc_off]
      iapply HΦ
      iapply decPost_accept C d rp IoE eof ueof F fs off c c r _ hstep
      iframe Hrec
      iapply ownDecoder_intro d IoE eof sl fbr fbrs h F fs (F.bs.take off ++ ys ++ ys2) _ c true
        hacc_lt (fun _ => hacc_rs)
      iframe
      iframe Hmu Hsl
      iapply ownFbr_intro
      iframe
      iframe Hf HF Hfio
    rw [decide_eq_false hct]
    iunfold ownRec at Hrec
    icases Hrec with ⟨%v, Hrv, #Ht, #Hc, Hrdata⟩
    iunfold ownDecCrc at Hdc
    icases Hdc with ⟨%lc, %tab, %Hh, Hlc, #Htab⟩
    subst Hh
    wp_auto
    wp_apply HWrite lc c tab v.Data' r.data (DFrac.own 1) $$ [Hlc Hrdata] as ⟨Hlc, Hrdata⟩
    · iframe
      iframe Htab
    wp_apply HSum lc _ tab (DFrac.own 1) $$ Hlc as Hlc
    icases Hcm with ⟨%ecm, #Hecm, #Hecmok⟩
    wp_apply HValidate rp r (hash.crc32.crc32c c r.data) ecm $$ [Hrv Hrdata] as %err4 ⟨Hrec, Hv⟩
    · iframe Hecm Hecmok
      iunfold ownRec
      iexists v
      iframe
      iframe Ht Hc
    have hCc : C.crc32c c r.data = hash.crc32.crc32c c r.data := by rw [hC]
    icases Hv with (%hv | ⟨%hne, %ei4, %he4, #Hei4⟩)
    · -- the CRC matches: the record is accepted
      obtain ⟨rfl, hcrc⟩ := hv
      wp_auto
      have hstep : decRecStep C fs.isEmpty F.bs off c =
          .accept r (8 + rb + pad) (hash.crc32.crc32c c r.data) := by
        rw [hstep0]; unfold decRecData; rw [hdec]; simp [hct, hCc, hcrc]
      rw [hacc_off]
      iapply HΦ
      iapply decPost_accept C d rp IoE eof ueof F fs off c _ r _ hstep
      iframe Hrec
      iapply ownDecoder_intro d IoE eof sl fbr fbrs _ F fs (F.bs.take off ++ ys ++ ys2) _ _ true
        hacc_lt (fun _ => hacc_rs)
      iframe
      iframe Hmu Hsl
      isplitl [Hlc]
      · iunfold ownDecCrc
        iexists lc, tab
        iframe
        iframe Htab
        ipureintro; rfl
      iapply ownFbr_intro
      iframe
      iframe Hf HF Hfio
    -- a CRC mismatch
    subst he4
    wp_auto
    wp_apply HReset rp $$ [Hrec] as Hr
    · iapply ownRec_any; iexact Hrec
    wp_apply HTorn d sl off dsl ys2 (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) hoff hys2l
      $$ [Hbrs Hoff Hdat] as ⟨Hbrs, Hoff, Hdat⟩
    · iframe
    rw [hlast]
    have hstep : decRecStep C fs.isEmpty F.bs off c =
        .stop (.crcErr (isTorn fs.isEmpty off ys2)) (hash.crc32.crc32c c r.data) := by
      rw [hstep0]; unfold decRecData; rw [hdec]; simp [hct, hCc, hne]
    cases ht : isTorn fs.isEmpty off ys2
    all_goals rw [ht] at hstep
    all_goals wp_pures
    all_goals
      wp_auto
      wp_apply HFI fbr b _ GoInterface.nil DFrac.discard $$ [Hf] as -
      · iexact Hf
      wp_auto
      wp_apply HName as %nm -
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
    all_goals first
      | (wp_apply HErrorf _ _ [GoInterface.ok ei4, interface.mkOk go.string #nm,
            interface.mkOk go.int64 #(W64 off)] [ei4] (by
            intro ii hii
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hii
            rcases hii with h | h | h
            · cases h; exact Or.inr (by simp)
            · rw [interface.mkOk] at h; cases h; exact Or.inl (argWf_string _)
            · rw [interface.mkOk] at h; cases h; exact Or.inl (argWf_int64 _)) $$ [Hasl] as %e5 -
         · iframe
           iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
           iexact Hei4)
      | (wp_apply HErrorf _ _ [interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x2,
            interface.mkOk go.string #nm, interface.mkOk go.int64 #(W64 off)]
            [⟨go.GoType.PointerType errors.errorString.ty, #x2⟩] (by
            intro ii hii
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hii
            rcases hii with h | h | h
            · rw [interface.mkOk] at h; cases h; exact Or.inr (by simp)
            · rw [interface.mkOk] at h; cases h; exact Or.inl (argWf_string _)
            · rw [interface.mkOk] at h; cases h; exact Or.inl (argWf_int64 _)) $$ [Hasl] as %e5 -
         · iframe
           iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
           iexact HUerr)
    all_goals
      iapply HΦ
      iapply decPost_stop C d rp IoE eof ueof F fs off c _ _ _ hstep (by simp [stopErr])
      isplitl [Hr]
      · iunfold ownRecAny; iexists _; iexact Hr
      iapply Hown _ _ (by simp)
      iframe
      iframe Hmu Hf HF Hsl Hfio
      iunfold ownDecCrc
      iexists lc, tab
      iframe
      iframe Htab
      ipureintro; rfl

end proof

end EtcdGrove
end Perennial
