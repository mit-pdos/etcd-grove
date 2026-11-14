/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__ReadAll.lean` (W3/W5 of
`notes/wal-fsext-plan.md`; `sorry`: the plan's W3/W5 log says what is missing).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__ReadAll
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.ReadAllCallees
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__Decode
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__LastCRC
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__UpdateCRC
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__LastOffset
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetType
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetCrc
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__Validate
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveEntry
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import LinuxFs.Spec.fmt.ErrorfErrs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllLoop
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadState
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllInv
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllExit
public import Perennial.Proof.sync.Results
public import Perennial.Proof.bytes.Equal
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs

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
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- No stop's error is `nil` (`io.EOF` and `io.ErrUnexpectedEOF` are not). -/
theorem stopErr_nil {eof ueof : GoInterface} (h1 : eof ≠ GoInterface.nil) (h2 : ueof ≠ GoInterface.nil)
    (s : WalStop) : ¬ stopErr eof ueof s GoInterface.nil := by
  have h1' : GoInterface.nil ≠ eof := fun h => h1 h.symm
  have h2' : GoInterface.nil ≠ ueof := fun h => h2 h.symm
  cases s
  all_goals try rename_i t; cases t
  all_goals (simp only [stopErr]; first | exact h1' | exact h2' | exact fun h => h.1 rfl)

/-- A record the reader does not reject is one of the reader's records. -/
theorem rdLoop_mem {C : WalCodec} {U : WalUnmarshal} {s : w64 × w64} {R0 : DecOut}
    {acc : List WalRec} {fs fs' : List (List w8)} {off off' : Nat} {c c' : w32} {st : RAState}
    {ix : w64 × w64} {r : WalRec} (hL : RdLoop C U s R0 acc fs off c st ix)
    (h : goDecode C fs off c = .ok r fs' off' c') (hok : ¬ (r.typ = crcType ∧ crcRecBad c' r)) :
    r ∈ R0.recs := by
  rw [hL.recs, rdRest_ok h hok]; simp

/-- The invariant at the decoder's next state (`rdLoop_ok` over the decoder's files). -/
theorem rdLoop_next {GF : BundledGFunctors} {C : WalCodec} {U : WalUnmarshal} {s : w64 × w64} {R0 : DecOut}
    {acc : List WalRec} {fsD : List (DecFile GF)} {fs' : List (List w8)} {k off off' : Nat} {c c' : w32}
    {st st' : RAState} {ix : w64 × w64} {r : WalRec}
    (hL : RdLoop C U s R0 acc (fsD.map (·.bs)) off c st ix)
    (h : goDecode C (fsD.map (·.bs)) off c = .ok r fs' off' c') (hfs : (fsD.drop k).map (·.bs) = fs')
    (hok : ¬ (r.typ = crcType ∧ crcRecBad c' r)) (hst : raStep U s st (r.typ, r.data) = .ok st') :
    RdLoop C U s R0 (acc ++ [r]) ((fsD.drop k).map (·.bs)) off' (rdCrc c' r) st' (raIdx U s ix r) := by
  subst hfs; exact (rdLoop_ok hL h hok hst).2

theorem raIdx_other {U : WalUnmarshal} {s ix : w64 × w64} {r : WalRec} (h1 : r.typ ≠ entryType)
    (h2 : r.typ ≠ snapshotType) : raIdx U s ix r = ix := by
  simp [raIdx, h1, h2]

theorem rdCrc_other {c : w32} {r : WalRec} (h : r.typ ≠ crcType) : rdCrc c r = c := by
  simp [rdCrc, h]

/-- The metadata arm's step: every metadata record carries the same data. -/
theorem raStep_md {U : WalUnmarshal} {s : w64 × w64} {st : RAState} {r : WalRec}
    (hT : r.typ = metadataType) (hmd : ∀ dd, st.md = some dd → dd = r.data) :
    raStep U s st (r.typ, r.data) = .ok { st with md := some r.data } := by
  obtain ⟨md, hs, ents, m⟩ := st
  cases md with
  | none => simp [raStep, hT, metadataType, entryType, stateType]
  | some dd =>
    have := hmd dd rfl
    subst this
    simp [raStep, hT, metadataType, entryType, stateType]

instance walEntsIn_persistent (P : WalPbIn GF) (esL : List Loc) (es : List EntryM) :
    Persistent (walEntsIn P esL es) := by
  unfold walEntsIn; infer_instance

theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.ReadAll.wp_proof [os.file.FieldAssumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
    (P : WalPbIn GF) (Mr : WalMarshal) (U : WalUnmarshal) (hU : U.Ok Mr)
    (HsO : Loc → HardStateM → IProp GF) (hHs : WalHsOwn P U HsO)
    (wp_Decode : go_etcd_io.etcd.server.v3.storage.wal.decoder.Decode.spec (GF := GF) (hG := hG))
    (wp_LastCRC : go_etcd_io.etcd.server.v3.storage.wal.decoder.LastCRC.spec (GF := GF) (hG := hG))
    (wp_UpdateCRC : go_etcd_io.etcd.server.v3.storage.wal.decoder.UpdateCRC.spec (GF := GF) (hG := hG))
    (wp_LastOffset : go_etcd_io.etcd.server.v3.storage.wal.decoder.LastOffset.spec (GF := GF) (hG := hG))
    (wp_GetType : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetType.spec (GF := GF) (hG := hG))
    (wp_GetCrc : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetCrc.spec (GF := GF) (hG := hG))
    (wp_Validate : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Validate.spec (GF := GF) (hG := hG))
    (wp_SnapIndex : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF) (hG := hG))
    (wp_SnapTerm : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetTerm.spec (GF := GF) (hG := hG))
    (wp_UnmarshalSnap : go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage.specWalSnap (GF := GF) (hG := hG) U)
    (wp_UnmarshalEnt : WalPbIn.UnmarshalEntLaw (GF := GF) (hG := hG) P U)
    (wp_EntIndex : WalPbIn.GetIndexLaw (GF := GF) (hG := hG) P)
    (wp_EntTerm : WalPbIn.GetTermLaw (GF := GF) (hG := hG) P)
    (wp_CloneHs : WalPbIn.CloneHsLaw (GF := GF) (hG := hG) P)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.ReadAll.spec (W := W) P Mr := by
  intro R jr r dir nm w s qp qc Q hin hcl
  wp_start as ⟨#Harea, Hp, Hperm, Hop, Hau⟩
  unfold walOpeningF
  icases Hop with ⟨Hgh, Hrh, Hph, %df, %dfd, %jd, Hdff, Hdf, Hdfs⟩
  unfold walReadH walOpenIn walReadTie
  simp only [↓reduceIte]
  icases Hrh with ⟨⟨%lg, %sp, Hlg, #Hzap, Hdir, Hstart, #Hsp⟩, %dec, %IoE, %eof, %ueof, %fs, %locks,
    %lfs, %fp, %rc, %j, Hdecf, Hdec, ⟨#Hdenv, %hIoN⟩, ⟨%X, %hj, %gs, %fls, Hn, Hout, ⟨Htf, Hnf⟩, #Hk, %Hgs,
    %Hfs, #Hlks⟩, Hlocks, Hls, Hcap, Hrc, Hfp, ⟨%hrc, Hpipe⟩, He, Hst, Hmd, Henti, Hsnapi, Hns,
    #Hmu, #Henv, #Hcrc⟩
  ihave #Henv0 := Henv
  iunfold encEnv at Henv0
  icases Henv0 with ⟨-, -, #Hsync, -, -⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync] as ⟨Hlocked, -⟩
  (try wp_auto)
  -- the look at the invariant before the loop: the records the decoder reads decode
  obtain ⟨hgne, hgnd, hgsz, hghd, hglast, hgdrop⟩ := Hgs
  obtain ⟨hfl, hll, hfll, hfk⟩ := Hfs
  iunfold WalFs.walAreaOk at Harea
  icases Harea with ⟨#Hinv, -⟩
  icases ownDecoder_halves dec IoE eof fs 0 0#32 true gs hfl (fun k F g h1 h2 => by
      obtain ⟨-, -, f, fd, -, hS⟩ := hfk k F g h1 h2
      exact ⟨f, fd, _, _, hS⟩) $$ Hdec with ⟨Hh, Hdbk⟩
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod walInv_readFiles walCodec Mr R jr r dir j X hj gs
      (decFiles_names hfl (fun k F g h1 h2 => (hfk k F g h1 h2).2.1)) hgdrop hgsz
      $$ Hinv Hnc Hk Hn Htf Hh with ⟨Hnc, Hn, Htf, Hh, %d0, %lay, %kk, %hlook⟩
  ihave Hdec := Hdbk $$ Hh
  iframe Hnc
  imodintro
  obtain ⟨-, hab, hex, hwr, hgs⟩ := hlook
  have hR0 := readFiles_ok' walCodec_ok hU hab hex hwr kk gs hgs hgne (fs.map (·.bs))
    (decFiles_bs hfl (fun k F g h1 h2 => (hfk k F g h1 h2).1))
  ihave %hnn := decEnv_nonnil IoE eof ueof $$ Hdenv
  wp_apply (wp_Decode walCodec dec «$r0_ptr» IoE eof ueof fs 0 0#32 rfl) $$ [Hdec «$r0»] as %err0 Hpost
  · iframe Hdec Hdenv
    unfold ownRecAny
    iexists _
    iexact «$r0»
  (try wp_auto)
  ihave Hhs := hHs.zero _ $$ «$r0»
  ihave Hmd0 := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave He0 := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
  ihave Hec0 := ownSliceCap_nil (V := Loc) (GF := GF)
  -- the loop's invariant (W3/W5 log, nineteenth session)
  ihave HI : (∃ (acc : List WalRec) (fsD : List (DecFile GF)) (off : Nat) (c : w32) (st : RAState)
      (ix : w64 × w64) (e : GoInterface) (mdv : GoSlice) (stp : Loc) (entsv : GoSlice) (esL : List Loc),
      "err" ∷ err_ptr ↦ e ∗
      "Hpost" ∷ decPost walCodec dec «$r0_ptr» IoE eof ueof fsD off c e ∗
      "metadata" ∷ metadata_ptr ↦ mdv ∗ "Hmdv" ∷ mdv ↦* st.md.getD [] ∗
      "state" ∷ state_ptr ↦ stp ∗ "Hhs" ∷ HsO stp st.hs ∗
      "ents" ∷ ents_ptr ↦ entsv ∗ "Hents" ∷ entsv ↦* esL ∗
      "Hecap" ∷ ownSliceCap Loc entsv (DFrac.own 1) ∗ "Hein" ∷ walEntsIn P esL st.ents ∗
      "Hmatch" ∷ match_ptr ↦ st.matched ∗
      "Henti" ∷ structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"enti" w ↦ ix.1 ∗
      "Hsnapi" ∷ structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"snapi" w ↦ ix.2 ∗
      "%hinv" ∷ ⌜RdLoop walCodec U s (rdRest walCodec (fs.map (·.bs)) 0 0#32) acc (fsD.map (·.bs)) off c
          st ix ∧ (∃ k, fsD = fs.drop k) ∧ (st.md = none → mdv = slice.nil) ∧
        (∀ dd, st.md = some dd → dd = d0.metadata)⌝ : IProp GF)
      $$ [err Hpost metadata Hmd0 state Hhs ents He0 Hec0 «match» Henti Hsnapi]
  · iexists [], fs, 0, 0#32, raInit, (W64 0, W64 0), err0, slice.nil, _, slice.nil, []
    simp only [raInit, Option.getD_none, walEntsIn]
    iframe
    iframe Hmd0 He0 Hec0
    isplitr
    · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro
    ipureintro
    exact ⟨rdLoop_start _ _ _ _, ⟨0, rfl⟩, fun _ => trivial, fun _ h => by simp at h⟩
  irename «rec» => Hrec
  wp_for HI
  obtain ⟨hL, ⟨kD, hkD⟩, hmdn, hmdd⟩ := hinv
  (try wp_auto)
  rcases e with ei | _
  · -- the loop's exit
    dsimp only
    (try wp_auto)
    sorry
  · -- the body: `err == nil`
    dsimp only
    (try wp_auto)
    iunfold decPost at Hpost
    iunfold decPostB at Hpost
    icases Hpost with ⟨⟨%k, Hm⟩ | ⟨%hio, -, -⟩ | ⟨%k, %sx, %offx, %cx, %hgf, -⟩, #Hans⟩
    · generalize hgd : goDecode walCodec (List.map (fun x => x.bs) fsD) off c = gd
      rcases gd with ⟨r, fs', off', c'⟩ | ⟨sx, fs', off', c'⟩
      · icases Hm with ⟨%hok, Hr, Hdec⟩
        simp only [decide_true, ↓reduceIte]
        wp_auto
        wp_apply wp_GetType $$ Hr as Hr
        have hdec0 : ¬ (r.typ = crcType ∧ crcRecBad c' r) → RecDec U r ∧ RecMd d0.metadata r :=
          fun hnc => hR0 r (rdLoop_mem hL hgd hnc)
        wp_if_destruct
        · -- EntryType
          sorry
        wp_if_destruct
        · -- StateType
          have hT : r.typ = stateType := Hif
          have hnc : ¬ (r.typ = crcType ∧ crcRecBad c' r) := by
            rw [hT]; simp [stateType, crcType]
          obtain ⟨h, hh⟩ := (hdec0 hnc).1.2.1 hT
          unfold ownRec
          icases Hr with ⟨%v, Hl, Ht, Hc, Hd⟩
          wp_auto
          wp_apply hHs.unmarshal v.Data' _ r.data h hh $$ Hd as %p ⟨Hd, Hhs'⟩
          have hst : raStep U s st (r.typ, r.data) = .ok { st with hs := h } := by
            simp [raStep, hT, hh, stateType, entryType]
          wp_for_post
          wp_apply (wp_Decode walCodec dec «$r0_ptr» IoE eof ueof (fsD.drop k) off' c' rfl)
            $$ [Hdec Hl] as %e' Hpost
          · iframe Hdec Hdenv; unfold ownRecAny; iexists v; iexact Hl
          iframe
          have hi1 : r.typ ≠ entryType := by rw [hT]; simp [stateType, entryType]
          have hi2 : r.typ ≠ snapshotType := by rw [hT]; simp [stateType, snapshotType]
          have hi3 : r.typ ≠ crcType := by rw [hT]; simp [stateType, crcType]
          have hL' := rdLoop_next hL hgd hok.2 hnc hst
          rw [raIdx_other hi1 hi2, rdCrc_other hi3] at hL'
          iexists acc ++ [r], fsD.drop k, off', c', { st with hs := h }, ix, e', mdv, p, entsv, esL
          iframe
          ipureintro
          exact ⟨hL', ⟨kD + k, by rw [hkD, List.drop_drop]⟩, hmdn, hmdd⟩
        wp_if_destruct
        · -- MetadataType
          have hT : r.typ = metadataType := Hif
          have hnc : ¬ (r.typ = crcType ∧ crcRecBad c' r) := by
            rw [hT]; simp [metadataType, crcType]
          have hmd : r.data = d0.metadata := (hdec0 hnc).2 hT
          have hi1 : r.typ ≠ entryType := by rw [hT]; simp [metadataType, entryType]
          have hi2 : r.typ ≠ snapshotType := by rw [hT]; simp [metadataType, snapshotType]
          have hi3 : r.typ ≠ crcType := by rw [hT]; simp [metadataType, crcType]
          have hst := raStep_md (U := U) (s := s) (st := st) hT (fun dd h => by rw [hmdd dd h, hmd])
          have hL' := rdLoop_next hL hgd hok.2 hnc hst
          rw [raIdx_other hi1 hi2, rdCrc_other hi3] at hL'
          unfold ownRec
          icases Hr with ⟨%v, Hl, Ht, Hc, Hd⟩
          ihave #Hdeps := isPkgInit_unfold_deps pkg_id.go_etcd_io.etcd.server.v3.storage.wal $$ Hpkg
          wp_if_destruct
          · -- `metadata == nil`
            wp_for_post
            wp_apply (wp_Decode walCodec dec «$r0_ptr» IoE eof ueof (fsD.drop k) off' c' rfl)
              $$ [Hdec Hl] as %e' Hpost
            · iframe Hdec Hdenv; unfold ownRecAny; iexists v; iexact Hl
            iframe
            iexists acc ++ [r], fsD.drop k, off', c', { st with md := some r.data }, ix, e', v.Data', stp,
              entsv, esL
            simp only [Option.getD_some]
            iframe
            ipureintro
            exact ⟨hL', ⟨kD + k, by rw [hkD, List.drop_drop]⟩, fun h => by simp at h,
              fun dd h => by simp only [Option.some.injEq] at h; rw [← h, hmd]⟩
          · -- `metadata != nil`: the same metadata
            obtain ⟨dd, hdd⟩ : ∃ dd, st.md = some dd := by
              rcases h : st.md with _ | dd
              · exact absurd (hmdn h) (by assumption)
              · exact ⟨dd, rfl⟩
            rw [hdd, Option.getD_some]
            wp_apply bytes.Equal.wp_proof $$ [Hmdv Hd] as ⟨Hmdv, Hd⟩
            · iframe
            simp only [hmdd dd hdd, ← hmd, eq_self_iff_true, _root_.decide_true]
            wp_auto
            wp_for_post
            wp_apply (wp_Decode walCodec dec «$r0_ptr» IoE eof ueof (fsD.drop k) off' c' rfl)
              $$ [Hdec Hl] as %e' Hpost
            · iframe Hdec Hdenv; unfold ownRecAny; iexists v; iexact Hl
            iframe
            iexists acc ++ [r], fsD.drop k, off', c', { st with md := some r.data }, ix, e', v.Data', stp,
              entsv, esL
            simp only [Option.getD_some]
            iframe
            ipureintro
            exact ⟨hL', ⟨kD + k, by rw [hkD, List.drop_drop]⟩, fun h => by simp at h,
              fun dd h => by simp only [Option.some.injEq] at h; rw [← h, hmd]⟩
        sorry
      · icases Hm with ⟨%hst, -, -⟩
        exact absurd hst.1 (stopErr_nil hnn.1 hnn.2 sx)
    · exact absurd hio hIoN
    · exact absurd hgf.2 (stopErr_nil hnn.1 hnn.2 sx)

end proof

end EtcdGrove
end Perennial
