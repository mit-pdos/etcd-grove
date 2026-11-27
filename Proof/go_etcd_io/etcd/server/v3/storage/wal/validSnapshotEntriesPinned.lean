/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/validSnapshotEntries.lean`'s `specPinned`
(W8 of `notes/wal-fsext-plan.md`): `readWALNames` over the claim's half (the names are the segments',
`walNamesOut_segs`), `openWALFiles` from 0 in read mode, the decoder over every segment (`walDecFiles_mk`,
`NewDecoder`), the decode loop (invariant `VsLoop ∧ FilesAt ∧ LaterOk`: every stop and failed `Unmarshal` is at
the end of what the reader reads, and drops no file), the filter in place, and the deferred closer, which gets
every file back from the decoder's streams (`walTie_files`, `wal.walClosable`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.readWALNames
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.openWALFiles
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.NewDecoder
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__Decode
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__LastCRC
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__UpdateCRC
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetType
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetCrc
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__Validate
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.ReadAllCallees
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.openAtIndexLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.VsePure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.VseAttemptPure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.VseErr
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DecTerm
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DecStreams
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllTail
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllInv
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllExit
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseOpeningFiles
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.VseAttemptLemmas

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
variable [errs_sem : _root_.Perennial.errors.Assumptions]

/-- See the spec file's header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries.wp_proofPinned
 [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
    (P : WalPbIn GF) (Mr : WalMarshal) (U : WalUnmarshal) (hU : U.Ok Mr) (hUs : U.SnapCoh)
    (HsO : Loc → HardStateM → IProp GF) (hHs : WalHsOwn P U HsO)
    (hEnv : WalDecEnvSupply (GF := GF))
    (wp_IsEof : errors.IsPathErrnoEof.spec (GF := GF) (hG := hG))
    (wp_Term : errors.IsPathErrnoTerm.spec (GF := GF) (hG := hG))
    (wp_names : go_etcd_io.etcd.server.v3.storage.wal.readWALNames.spec (GF := GF) (hG := hG))
    (wp_openFiles : go_etcd_io.etcd.server.v3.storage.wal.openWALFiles.spec (GF := GF) (hG := hG))
    (wp_NewDecoder : go_etcd_io.etcd.server.v3.storage.wal.NewDecoder.spec (GF := GF) (hG := hG))
    (wp_Decode : go_etcd_io.etcd.server.v3.storage.wal.decoder.Decode.spec (GF := GF) (hG := hG))
    (wp_LastCRC : go_etcd_io.etcd.server.v3.storage.wal.decoder.LastCRC.spec (GF := GF) (hG := hG))
    (wp_UpdateCRC : go_etcd_io.etcd.server.v3.storage.wal.decoder.UpdateCRC.spec (GF := GF) (hG := hG))
    (wp_GetType : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetType.spec (GF := GF) (hG := hG))
    (wp_GetCrc : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetCrc.spec (GF := GF) (hG := hG))
    (wp_Validate : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Validate.spec (GF := GF) (hG := hG))
    (wp_SnapIndex : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF) (hG := hG))
    (wp_UnmarshalSnap : go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage.specWalSnap (GF := GF) (hG := hG) U)
    (wp_Stat : os.File.Stat.spec (GF := GF) (hG := hG))
    (wp_Size : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (wp_FName : os.fileStat.Name.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries.specPinned (W := W) Mr := by
  intro lg R jr r dir qd d lay X hj hpin hdl
  have hdl' : dir.length < 4096 := hdl.1
  wp_start as ⟨#Hzap, #Hok, Hpd, Hperm, HS, Hj⟩
  obtain ⟨hljr, hX, hcoh, habs, hid, hnd, hsn⟩ := hpin
  ihave #Hok' := Hok
  iunfold WalFs.walAreaOk at Hok'
  icases Hok' with ⟨#Hinv, #Hosi, #Hsi, %hrb0, %hrb1, -⟩
  have hrb := And.intro hrb0 hrb1
  ihave #Hosp := wal_osInit $$ Hpkg
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_names lg dir R lay.j (DFrac.own qd) 1 (.except X) (DFrac.own (1 : Qp).half) hj
    $$ [Hpd Hperm Hj] as %rn %err ⟨Hpd, Hperm, Hj, Hnm⟩
  · iframe; iframe #
  icases Hnm with (⟨%ws, ⟨%herr, %hout⟩, Hws⟩ | ⟨%e, %herr, #He, #Ht⟩)
  rotate_left
  · -- `readWALNames` failed
    subst herr
    (try wp_auto)
    iapply HΦ
    iframe Hpd Hperm HS Hj
    ileft
    isplitr
    · ipureintro; nofun
    iapply wal.vseErrIs_of_term
    iframe Hosp Ht
  subst herr
  have hnmf := walLay_nameFmt habs
  have hws : ws = lay.segs.map (·.name) :=
    walNamesOut_segs hX hsn habs.names.1 hnd habs.names.2 hnmf hout
  have hwl : ws.length = lay.segs.length := by rw [hws, List.length_map]
  have hS : ∀ g ∈ lay.segs, g.om.size = g.bs.length := fun g hg => (habs.metas g hg).1
  (try wp_auto)
  ihave #Hw : (wal.walInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave #Hofn := wal.walInit_openWALFilesFn $$ Hw
  iapply wp_segs_size _ _ _ _ rfl _ $$ HS
  iintro %hsz0 HS
  have hsz : ∀ g ∈ lay.segs, g.bs.length + 2 ^ 12 < 2 ^ 62 := fun g hg => by
    have h1 := hsz0 g hg; rw [hS g hg] at h1; omega
  (try wp_auto)
  have hopen := walOpenNames_ok 0 hX hsn hnmf hout hws
  have hcbs : ∀ g ∈ lay.segs, os.closeErrMax (child dir g.name) ≤ wal.closeMsgMax := fun g hg => by
    obtain ⟨sq, ix, hn⟩ := hnmf g hg
    exact wal.closeBound_of hdl' (by rw [hn, walFileName_length]; decide)
  have h0 : sint.nat (W64 0) = 0 := rfl
  wp_apply wp_openFiles lg dir rn ws (DFrac.own 1) (W64 0) false (lay.segs.map (·.ino))
      R lay.j (DFrac.own qd) 1 (.except X) (DFrac.own (1 : Qp).half) hj (by decide) (by rw [h0]; omega)
      (by rw [h0]; simp [hwl]) hdl (by rw [h0]; exact hopen)
    $$ [Hpd Hperm Hj Hws] as %rsl %lsl %clo %err2 ⟨Hpd, Hperm, Hj, Hws, Hopen⟩
  · iframe; iframe #
  icases Hopen with (⟨%frs, %lfs, ⟨%herr2, %hfl, %hll⟩, Hrsl, Hrc, Hlsl, Hlc, Hfiles, Hcl⟩ |
    ⟨%e, %herr, #He, Hte⟩)
  rotate_left
  · -- `openWALFiles` failed
    subst herr
    icases Hte with (%hf | #Ht)
    · cases hf
    (try wp_auto)
    iapply HΦ
    iframe Hpd Hperm HS Hj
    ileft
    isplitr
    · ipureintro; nofun
    iapply wal.vseErrIs_of_term
    iframe Hosp Ht
  subst herr2
  iunfold wal.walCloser at Hcl
  icases Hcl with ⟨%hcl, #Hcl⟩
  (try wp_auto)
  -- the decoder over the opened files
  subst hws
  rw [List.drop_zero] at *
  rw [List.length_map] at hfl hll
  ihave ⟨%IoE, %eof, %ueof, #Hde, %hIo⟩ := hEnv $$ Hpkg
  obtain ⟨hIo, hIoN⟩ := hIo
  ihave #Hde' := Hde
  iunfold decEnv at Hde'
  icases Hde' with ⟨-, -, -, -, #Hbufio, #Heof, #Hueof, -, #Hcrc, -, -⟩
  ihave ⟨#Heofa, %hIoEof⟩ := isEofOk_eof IoE eof ueof $$ [Hde]
  · iunfold decEnv at Hde
    icases Hde with ⟨-, -, -, -, -, -, -, #Hok, -⟩
    iexact Hok
  have hsz' : ∀ g ∈ lay.segs, g.om.size = g.bs.length ∧ g.bs.length + 2 ^ 12 < 2 ^ 62 :=
    fun g hg => ⟨hS g hg, hsz g hg⟩
  ihave ⟨%fs, %fls, ⟨%htie, %hfr⟩, Hdf, Hlk, #Hfrf⟩ := walDecFiles_mk wp_Stat wp_Size wp_FName wp_IsEof
    wp_Term IoE hIo eof hIoEof false dir lay.segs frs lfs hfl hll hsz' $$ [Hfiles HS]
  · iframe Hfiles
    isplitl []
    · iexact Hosi
    isplitl []
    · iexact Heof
    isplitl []
    · iexact Hosp
    isplitl []
    · iexact Heofa
    unfold segHalves segRes
    iexact HS
  subst hfr
  rw [List.map_map] at *
  wp_apply wp_NewDecoder rsl fs IoE eof $$ [Hrsl Hdf] as %dI ⟨%dec, %hdI, Hrsl, Hdec⟩
  · iframe; iframe #
  subst hdI
  (try wp_auto)
  -- the pure facts of the files
  have hbs : fs.map (·.bs) = lay.segs.map segImg :=
    decFiles_bs htie.1 (fun k F g h1 h2 => (htie.2.2 k F g h1 h2).1)
  have hkk : 0 < lay.segs.length := List.length_pos_iff.2 habs.nonempty
  have hFA : FilesAt walCodec (fs.map (·.bs)) 0 0#32 := by
    have := walFilesAt walCodec_ok habs hid.1 hid.2.1 0 hkk
    rwa [List.drop_zero, ← hbs] at this
  have hLO : LaterOk walCodec (fs.map (·.bs)) := by
    have := walLaterOk habs hid.1 hid.2.1 0
    rwa [List.drop_zero, ← hbs] at this
  have hR0 := readFiles_ok' walCodec_ok hU habs hid.1 hid.2.1 0 lay.segs List.drop_zero
    habs.nonempty (fs.map (·.bs)) hbs
  have hres := vseOut_running walCodec_ok hU habs hid.1 hid.2.1
  ihave %hnn := decEnv_nonnil IoE eof ueof $$ Hde
  irename «$r0» => Hrec0
  irename «$r0» => Hhs0
  generalize «$r0_ptr» = rcp at *
  wp_apply (wp_Decode walCodec dec rcp IoE eof ueof fs 0 0#32 rfl) $$ [Hdec Hrec0] as %err0 Hpost
  · iframe Hdec Hde
    unfold ownRecAny
    iexists _
    iexact Hrec0
  (try wp_auto)
  ihave Hhs := hHs.zero _ $$ Hhs0
  ihave Hl0 : ([∗list] F ∈ ([] : List (DecFile GF)), ∃ q, F.S q) $$ []
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  ihave Hsl0 := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
  ihave Hslc0 := ownSliceCap_nil (V := Loc) (GF := GF)
  ihave Hps0 : walSnapsAt (GF := GF) [] [] $$ []
  · unfold walSnapsAt; iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro
  ihave HI : (∃ (acc : List WalRec) (fsD : List (DecFile GF)) (kD off : Nat) (c : w32) (e : GoInterface)
      (sv : GoSlice) (ps : List Loc) (stp : Loc),
      "err" ∷ err_ptr ↦ e ∗
      "Hpost" ∷ decPost walCodec dec rcp IoE eof ueof fsD off c e ∗
      "Hleft" ∷ ([∗list] F ∈ fs.take kD, ∃ q, F.S q) ∗
      "snaps" ∷ snaps_ptr ↦ sv ∗ "Hsv" ∷ sv ↦* ps ∗ "Hsvc" ∷ ownSliceCap Loc sv (DFrac.own 1) ∗
      "Hps" ∷ walSnapsAt ps (vseSnaps U (acc.map (fun r => (r.typ, r.data)))) ∗
      "state" ∷ state_ptr ↦ stp ∗ "Hhs" ∷ HsO stp (vseHs U hsZero (acc.map (fun r => (r.typ, r.data)))) ∗
      "%hinv" ∷ ⌜VsLoop walCodec (rdRest walCodec (fs.map (·.bs)) 0 0#32) acc (fsD.map (·.bs)) off c ∧
        FilesAt walCodec (fsD.map (·.bs)) off c ∧ LaterOk walCodec (fsD.map (·.bs)) ∧ fsD = fs.drop kD⌝ : IProp GF)
      $$ [err Hpost Hl0 snaps Hsl0 Hslc0 state Hhs Hps0]
  · iexists [], fs, 0, 0, 0#32, err0, slice.nil, [], _
    simp only [List.map_nil, List.take_zero, vseSnaps, vseHs, List.filterMap_nil, List.foldl_nil,
      List.drop_zero]
    iframe
    isplitr
    · iexact Hsl0
    isplitr
    · iexact Hslc0
    ipureintro
    exact ⟨vsLoop_start _ _, hFA, hLO, trivial⟩
  irename «rec» => Hrecp
  wp_for HI
  obtain ⟨hL, hFAi, hLOi, hkD⟩ := hinv
  (try wp_auto)
  rcases e with ei | _
  · -- the loop's exit
    dsimp only
    (try wp_auto)
    simp only [intoVal_eq_iff, Bool.false_eq_true, decide_false, _root_.decide_true, ↓reduceIte]
    (try wp_auto)
    iunfold decPost at Hpost
    icases Hpost with ⟨Hpb, #Hans, #Hue⟩
    ihave ⟨Hall, #Hcase⟩ := vse_exit_streams walCodec_ok dec rcp IoE eof ueof fs fsD kD off c
      (GoInterface.ok ei) _ acc hL hFAi hLOi hkD (by simp) $$ [Hpb Hleft]
    · iframe
    ihave ⟨HS, Hclo⟩ := vse_close dir lay.segs fs fls lfs htie hcbs $$ [Hall]
    · iframe Hall; iexact Hfrf
    iunfold decAns at Hans
    icases Hans with (%hn0 | #Hans)
    · exact absurd hn0 (by simp)
    ihave %hueofp := decEnv_ueof_ptr IoE eof ueof $$ Hde
    wp_join (Q := fun v => iprop(∃ b : Bool, ⌜v = #b⌝ ∗ err_ptr ↦ GoInterface.ok ei ∗
        (if b then wal.vseErrIs (GoInterface.ok ei)
        else ⌜(rdRest walCodec (fs.map (·.bs)) 0 0#32).recs = acc⌝))) at (If _ _ (Val #false)) with [err]
    · iunfold isEofAns at Hans
      wp_apply Hans as %b1 %hb1
      subst hb1
      by_cases heof : GoInterface.ok ei = eof
      · simp only [heof, _root_.decide_true]
        (try wp_auto)
        iexists false
        isplitr
        · ipureintro; rfl
        iframe err
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hcase with (%h | ⟨%hio, -⟩)
        · ipureintro; exact h
        · exact absurd (heof ▸ hio) hIoEof
      · simp only [heof, decide_false]
        (try wp_auto)
        -- `errors.Is(err, io.ErrUnexpectedEOF)`: `false` on an I/O error; it returns otherwise
        icases Hcase with (%hrec | ⟨%hio, #Hn⟩)
        · iunfold decUe at Hue
          icases Hue with (%hn | #Ht | #Hn)
          · cases hn
          · ihave #Ht' := Ht
            iunfold errIsTerm at Ht'
            ihave #Hq := Ht' $$ %ueof %hueofp
            wp_apply Hq $$ [] as %b2 -
            (try wp_auto)
            cases b2
            · iexists true
              isplitr
              · ipureintro; rfl
              iframe err
              simp only [↓reduceIte]
              iapply wal.vseErrIs_of_term
              iframe Hosp Ht
            · iexists false
              isplitr
              · ipureintro; rfl
              iframe err
              simp only [Bool.false_eq_true, ↓reduceIte]
              ipureintro; exact hrec
          · iunfold notUeof at Hn
            icases Hn with ⟨#Hn1, #Ht⟩
            ihave #Hq := Hn1 $$ %ueof Hueof
            wp_apply Hq $$ [] as %b2 %hb2
            subst hb2
            (try wp_auto)
            iexists true
            isplitr
            · ipureintro; rfl
            iframe err
            simp only [↓reduceIte]
            iapply wal.vseErrIs_of_term
            iframe Hosp Ht
        · iunfold notUeof at Hn
          icases Hn with ⟨#Hn1, #Ht⟩
          ihave #Hq := Hn1 $$ %ueof Hueof
          wp_apply Hq $$ [] as %b2 %hb2
          subst hb2
          (try wp_auto)
          iexists true
          isplitr
          · ipureintro; rfl
          iframe err
          simp only [↓reduceIte]
          iapply wal.vseErrIs_of_term
          iframe Hosp Ht
    iintro ⟨%b, %hv, err, Hb⟩
    subst hv
    cases b
    · -- the end of the WAL
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hb with %hrecs
      (try wp_auto)
      -- the filter in place
      iunfold walSnapsAt at Hps
      icases Hps with #Hps
      ihave %hlenS := BigSepL2.bigSepL2_length $$ Hps
      ihave %hsvl := ownSlice_len $$ Hsv
      ihave %hsvw := ownSlice_wf $$ Hsv
      generalize hS : vseSnaps U (acc.map (fun r => (r.typ, r.data))) = S at *
      generalize hH : vseHs U hsZero (acc.map (fun r => (r.typ, r.data))) = hs at *
      ihave Hk0 : walSnapsAt (GF := GF) [] [] $$ []
      · unfold walSnapsAt; iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro
      ihave HF : (∃ (i : w64) (sp0 : Loc),
          "i" ∷ i_ptr ↦ i ∗
          "n" ∷ n_ptr ↦ W64 (vseKeep hs.Commit' ((ps.zip S).take (sint.nat i))).length ∗
          "s" ∷ s_ptr ↦ sp0 ∗
          "Hsv" ∷ sv ↦* vseKeepL (vseKeep hs.Commit' ((ps.zip S).take (sint.nat i))) ps ∗
          "Hkp" ∷ walSnapsAt ((vseKeep hs.Commit' ((ps.zip S).take (sint.nat i))).map Prod.fst)
            ((vseKeep hs.Commit' ((ps.zip S).take (sint.nat i))).map Prod.snd) ∗
          "Hhs" ∷ HsO stp hs ∗
          "%hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sv.len⌝ : IProp GF) $$ [i n s Hsv Hk0 Hhs]
      · iexists W64 0, _
        have h0 : sint.nat (W64 0) = 0 := rfl
        simp only [h0, List.take_zero, vseKeep, List.filter_nil, List.map_nil, List.length_nil]
        iframe
        ipureintro; constructor <;> word
      wp_for HF
      generalize hK : vseKeep hs.Commit' ((ps.zip S).take (sint.nat i)) = K at *
      have hKl : K.length ≤ sint.nat i := hK ▸ vseKeep_length_le _ _ _
      by_cases Hlt : sint.Z i < sint.Z sv.len
      · -- an iteration
        rw [decide_eq_true Hlt]; simp only [↓reduceIte]
        have hk : sint.nat i < ps.length := by
          have : sint.nat i = (sint.Z i).toNat := rfl
          have : sint.nat sv.len = (sint.Z sv.len).toNat := rfl
          omega
        obtain ⟨x, hx⟩ : ∃ x, ps[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hk⟩
        obtain ⟨y, hy⟩ : ∃ y, S[sint.nat i]? = some y := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        (try wp_auto)
        have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sv.len := ⟨hi.1, Hlt⟩
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index sv (sint.Z i) (vseKeepL K ps) (DFrac.own 1) x hi.1 $$ [Hsv] as Hsv
        · iframe; ipureintro
          rw [show (sint.Z i).toNat = sint.nat i from rfl, vseKeepL_get K ps _ hKl]; exact hx
        (try wp_auto)
        ihave #Hpk := BigSepL2.bigSepL2_lookup (PROP := IProp GF) hx hy $$ Hps
        wp_apply wp_SnapIndex x y $$ Hpk
        wp_apply hHs.getCommit stp hs $$ Hhs as Hhs
        (try wp_auto)
        have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        have hKs : vseKeep hs.Commit' ((ps.zip S).take (sint.nat (i + W64 1))) =
            K ++ (if uint.nat y.1 ≤ uint.nat hs.Commit' then [(x, y)] else []) := by
          rw [hi1, vseKeep_take_succ _ ps S _ hk hlenS, hK]
          have e1 : ps[sint.nat i] = x := (List.getElem?_eq_some_iff.1 hx).2
          have e2 : S[sint.nat i]'(by omega) = y := (List.getElem?_eq_some_iff.1 hy).2
          simp only [e1, e2]
        have hKn : sint.Z (W64 K.length) = K.length := by
          have : sint.nat i = (sint.Z i).toNat := rfl
          word
        wp_if_destruct
        · -- kept
          have hkeep : uint.nat y.1 ≤ uint.nat hs.Commit' := by word
          simp only [hkeep, ↓reduceIte] at hKs
          have hb2 : 0 ≤ sint.Z (W64 K.length) ∧ sint.Z (W64 K.length) < sint.Z sv.len := by
            rw [hKn]
            have : sint.nat i = (sint.Z i).toNat := rfl
            omega
          simp only [hb2, _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index sv (sint.Z (W64 K.length)) (vseKeepL K ps) x $$ [Hsv] as Hsv
          · iframe; ipureintro
            rw [hKn, vseKeepL_length K ps (by omega)]
            constructor <;> omega
          rw [show (sint.Z (W64 K.length)).toNat = K.length by rw [hKn]; rfl,
            vseKeepL_set K ps x y (by omega)]
          (try wp_auto)
          wp_for_post
          iframe
          iexists i + W64 1, x
          rw [hKs]
          have hn1 : W64 ((K ++ [(x, y)]).length : Int) = W64 (K.length : Int) + W64 1 := by
            rw [List.length_append, List.length_singleton, Int.natCast_add]
            exact BitVec.ofInt_add _ _
          rw [hn1]
          iframe
          isplitl [Hkp]
          · unfold walSnapsAt
            simp only [List.map_append, List.map_cons, List.map_nil]
            iapply (BigSepL2.bigSepL2_snoc (PROP := IProp GF)).2
            iframe Hkp
            iexact Hpk
          ipureintro
          have : sint.nat i = (sint.Z i).toNat := rfl
          constructor <;> word
        · -- not kept
          have hkeep : ¬ uint.nat y.1 ≤ uint.nat hs.Commit' := by word
          simp only [hkeep, ↓reduceIte, List.append_nil] at hKs
          (try wp_auto)
          wp_for_post
          iframe
          iexists i + W64 1, x
          rw [hKs]
          iframe
          ipureintro
          constructor <;> word
      · -- the filter's end
        rw [decide_eq_false Hlt]
        simp only [Bool.false_eq_true, ↓reduceIte]
        (try wp_auto)
        have hieq : sint.nat i = ps.length := by
          have : sint.nat i = (sint.Z i).toNat := rfl
          have : sint.nat sv.len = (sint.Z sv.len).toNat := rfl
          omega
        have hKf : K = vseKeep hs.Commit' (ps.zip S) := by
          rw [← hK, hieq, List.take_of_length_le (by simp [List.length_zip]; omega)]
        have hKn : sint.Z (W64 K.length) = K.length := by
          have : sint.nat i = (sint.Z i).toNat := rfl
          word
        have hc : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 K.length) ∧
            sint.Z (W64 K.length) ≤ sint.Z (W64 K.length) ∧ sint.Z (W64 K.length) ≤ sint.Z sv.cap := by
          have hKl' : K.length ≤ ps.length := by omega
          refine ⟨by decide, ?_, Int.le_refl _, ?_⟩ <;> word
        simp only [hc, _root_.and_self, ↓reduceIte]
        ihave Hfs := ownSlice_fullSlice_take sv (DFrac.own 1) (vseKeepL K ps) (W64 K.length)
          ⟨by word, by have hKl' : K.length ≤ ps.length := (by omega); word⟩ $$ Hsv
        rw [show sint.nat (W64 K.length) = K.length by
          have : sint.nat (W64 K.length) = (sint.Z (W64 K.length)).toNat := rfl
          rw [this, hKn]; rfl, vseKeepL_take] at *
        imod (ownSlice_persist _ _ _) $$ Hfs with #Hfs
        (try wp_auto)
        simp only [decide_eq_false hcl, Bool.not_false]
        (try wp_auto)
        wp_apply Hcl $$ [Hclo] as %e3 -
        · iexact Hclo
        (try wp_auto)
        have h1 : (walDecodeFiles walCodec (lay.segs.map segImg) 0#32).recs = acc := by
          rw [← hbs, ← rdRest_start]; exact hrecs
        rw [h1] at hres
        unfold vseOut at hres
        rw [hS, hH] at hres
        have hfin : K.map Prod.snd = walValidSnaps (d.H.map WalOpG.toM) d.cut := by
          rw [hKf, vseKeep_snd _ ps S hlenS, ← walValidSnaps_normH]; exact hres
        iapply HΦ
        iframe Hpd Hperm HS Hj
        iright
        isplitr
        · ipureintro; rfl
        iexists K.map Prod.fst
        iframe Hfs
        rw [← hfin]
        iexact Hkp
    · -- the decoder's error
      simp only [↓reduceIte]
      (try wp_auto)
      simp only [decide_eq_false hcl, Bool.not_false]
      (try wp_auto)
      wp_apply Hcl $$ [Hclo] as %e3 -
      · iexact Hclo
      (try wp_auto)
      iapply HΦ
      iframe Hpd Hperm HS Hj
      ileft
      iframe Hb
      ipureintro; nofun
  · -- the body: `err == nil`
    dsimp only
    (try wp_auto)
    iunfold decPost at Hpost
    iunfold decPostB at Hpost
    icases Hpost with ⟨⟨%k, Hk, Hm⟩ | ⟨%hio, -, -⟩ | ⟨%k, %sx, %offx, %cx, %hgf, -⟩, #Hans, -⟩
    rotate_left
    · exact absurd hio hIoN
    · exact absurd hgf.2 (stopErr_ne_nil hnn.1 hnn.2 sx)
    generalize hgd : goDecode walCodec (List.map (fun x => x.bs) fsD) off c = gd
    rcases gd with ⟨r, fs', off', c'⟩ | ⟨sx, fs', off', c'⟩
    rotate_left
    · icases Hm with ⟨%hst, -, -⟩
      exact absurd hst.1 (stopErr_ne_nil hnn.1 hnn.2 sx)
    icases Hm with ⟨%hok, Hr, Hdec⟩
    simp only [_root_.decide_true, ↓reduceIte]
    (try wp_auto)
    wp_apply wp_GetType $$ Hr as Hr
    have hdec0 : ¬ (r.typ = crcType ∧ crcRecBad c' r) → RecDec U r := fun hnc =>
      (hR0 r (vse_step walCodec_ok hL hFAi hLOi hkD hgd hok.2 hnc).1).1
    wp_if_destruct
    · -- SnapshotType
      have hT : r.typ = snapshotType := Hif
      have hn3 : r.typ ≠ crcType := by rw [hT]; simp [snapshotType, crcType]
      have hn2 : r.typ ≠ stateType := by rw [hT]; simp [snapshotType, stateType]
      obtain ⟨p, hp⟩ := (hdec0 (fun h => hn3 h.1)).2.2 hT
      obtain ⟨-, hL', hFA', hLO', hkD'⟩ :=
        vse_step walCodec_ok hL hFAi hLOi hkD hgd hok.2 (fun h => hn3 h.1)
      ihave Hleft := leftS_merge fs fsD kD k hkD $$ [Hleft Hk]
      · iframe
      unfold ownRec
      icases Hr with ⟨%v, Hl, Ht, Hc, Hd⟩
      (try wp_auto)
      wp_apply wp_UnmarshalSnap hUs «$r0_ptr» v.Data' _ r.data p hp $$ [«$r0» Hd] as ⟨Hd, #Hsn⟩
      · iframe
      (try wp_auto)
      wp_apply wp_slice_literal (V := Loc) [«$r0_ptr»]
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hsv $Hsvc $Hosl] as %sv' ⟨Hsv, Hsvc, -⟩
      (try wp_auto)
      wp_for_post
      wp_apply (wp_Decode walCodec dec rcp IoE eof ueof (fsD.drop k) off' c' rfl)
        $$ [Hdec Hl] as %e' Hpost
      · iframe Hdec Hde; unfold ownRecAny; iexists v; iexact Hl
      iframe
      iexists acc ++ [r], fsD.drop k, kD + k, off', c', e', sv', ps ++ [«$r0_ptr»], stp
      rw [vseSnaps_snoc_snap acc hT hp, vseHs_snoc_other hsZero acc hn2]
      rw [rdCrc_ne hn3] at hL' hFA'
      iframe
      isplitl [Hps]
      · unfold walSnapsAt
        iapply (BigSepL2.bigSepL2_snoc (PROP := IProp GF)).2
        iframe Hps
        iexact Hsn
      ipureintro
      exact ⟨hL', hFA', hLO', hkD'⟩
    have hn1 : r.typ ≠ snapshotType := Hif
    wp_if_destruct
    · -- StateType
      have hT : r.typ = stateType := Hif
      have hn3 : r.typ ≠ crcType := by rw [hT]; simp [stateType, crcType]
      obtain ⟨h, hh⟩ := (hdec0 (fun h => hn3 h.1)).2.1 hT
      obtain ⟨-, hL', hFA', hLO', hkD'⟩ :=
        vse_step walCodec_ok hL hFAi hLOi hkD hgd hok.2 (fun h => hn3 h.1)
      ihave Hleft := leftS_merge fs fsD kD k hkD $$ [Hleft Hk]
      · iframe
      unfold ownRec
      icases Hr with ⟨%v, Hl, Ht, Hc, Hd⟩
      (try wp_auto)
      wp_apply hHs.unmarshal v.Data' _ r.data h hh $$ [Hd] as %p ⟨Hd, Hhs'⟩
      · iexact Hd
      (try wp_auto)
      wp_for_post
      wp_apply (wp_Decode walCodec dec rcp IoE eof ueof (fsD.drop k) off' c' rfl)
        $$ [Hdec Hl] as %e' Hpost
      · iframe Hdec Hde; unfold ownRecAny; iexists v; iexact Hl
      iframe
      iexists acc ++ [r], fsD.drop k, kD + k, off', c', e', sv, ps, p
      rw [vseSnaps_snoc_other acc hn1, vseHs_snoc_state hsZero acc hT hh]
      rw [rdCrc_ne hn3] at hL' hFA'
      iframe
      ipureintro
      exact ⟨hL', hFA', hLO', hkD'⟩
    have hn2 : r.typ ≠ stateType := Hif
    wp_if_destruct
    · -- CrcType
      have hT : r.typ = crcType := Hif
      have hrc : rdCrc c' r = r.crc := by simp [rdCrc, hT]
      have hstep : ∀ (cz : w32), cz = c' → ¬ crcRecBad cz r →
          VsLoop walCodec (rdRest walCodec (fs.map (·.bs)) 0 0#32) (acc ++ [r])
            ((fsD.drop k).map (·.bs)) off' r.crc ∧ FilesAt walCodec ((fsD.drop k).map (·.bs)) off' r.crc ∧
          LaterOk walCodec ((fsD.drop k).map (·.bs)) ∧ fsD.drop k = fs.drop (kD + k) := by
        intro cz hcz hb
        subst hcz
        obtain ⟨-, hL', hFA', hLO', hkD'⟩ :=
          vse_step walCodec_ok hL hFAi hLOi hkD hgd hok.2 (fun h => hb h.2)
        rw [hrc] at hL' hFA'
        exact ⟨hL', hFA', hLO', hkD'⟩
      wp_apply wp_LastCRC dec IoE eof (fsD.drop k) off' c' true $$ Hdec as Hdec
      wp_if_destruct
      · -- the chain's CRC is zero: not checked
        obtain ⟨hL', hFA', hLO', hkD'⟩ := hstep _ rfl (fun h => h.1 rfl)
        ihave Hleft := leftS_merge fs fsD kD k hkD $$ [Hleft Hk]
        · iframe
        wp_apply wp_GetCrc $$ Hr as Hr
        wp_apply wp_UpdateCRC dec IoE eof (fsD.drop k) off' _ r.crc true $$ [Hdec] as Hdec
        · iframe Hdec Hcrc
        wp_for_post
        wp_apply (wp_Decode walCodec dec rcp IoE eof ueof (fsD.drop k) off' r.crc rfl)
          $$ [Hdec Hr] as %e' Hpost
        · iframe Hdec Hde; iapply ownRec_any $$ Hr
        iframe
        iexists acc ++ [r], fsD.drop k, kD + k, off', r.crc, e', sv, ps, stp
        rw [vseSnaps_snoc_other acc hn1, vseHs_snoc_other hsZero acc hn2]
        iframe
        ipureintro
        exact ⟨hL', hFA', hLO', hkD'⟩
      · -- checked
        ihave #Hde2 := Hde
        iunfold decEnv at Hde2
        icases Hde2 with ⟨-, -, #Hfmt, -, -, #Heof2, -, -, -, ⟨%ecm, #Hcm, #Hcmok, #Hcmnot, #Hcmt⟩, -⟩
        ihave %heofT := decEnv_eof_target _ _ _ $$ Hde
        wp_apply wp_Validate rcp r c' ecm eof heofT $$ [Hr] as %verr ⟨Hr, Hv⟩
        · iframe Hr; iframe #
        icases Hv with (⟨%hv1, %hv2⟩ | ⟨%hne, %ei, %hei, -, -, -⟩)
        · subst hv1
          obtain ⟨hL', hFA', hLO', hkD'⟩ := hstep _ rfl (fun h => h.2 hv2)
          ihave Hleft := leftS_merge fs fsD kD k hkD $$ [Hleft Hk]
          · iframe
          (try wp_auto)
          wp_apply wp_GetCrc $$ Hr as Hr
          wp_apply wp_UpdateCRC dec IoE eof (fsD.drop k) off' _ r.crc true $$ [Hdec] as Hdec
          · iframe Hdec Hcrc
          wp_for_post
          wp_apply (wp_Decode walCodec dec rcp IoE eof ueof (fsD.drop k) off' r.crc rfl)
            $$ [Hdec Hr] as %e' Hpost
          · iframe Hdec Hde; iapply ownRec_any $$ Hr
          iframe
          iexists acc ++ [r], fsD.drop k, kD + k, off', r.crc, e', sv, ps, stp
          rw [vseSnaps_snoc_other acc hn1, vseHs_snoc_other hsZero acc hn2]
          iframe
          ipureintro
          exact ⟨hL', hFA', hLO', hkD'⟩
        · -- a CRC mismatch: `ErrCRCMismatch`, every file closed
          subst hei
          (try wp_auto)
          ihave #HeX := wal.walInit_ErrCRCMismatch $$ Hw
          iunfold wal.errVar at HeX
          icases HeX with ⟨%eX, #HeX, -, #HeXt⟩
          (try wp_auto)
          ihave Hall := vse_streams dec IoE eof fs fsD kD k off' c' true hkD $$ [Hleft Hk Hdec]
          · iframe
          ihave ⟨HS, Hclo⟩ := vse_close dir lay.segs fs fls lfs htie hcbs $$ [Hall]
          · iframe Hall; iexact Hfrf
          wp_for_post
          (try wp_auto)
          simp only [decide_eq_false hcl, Bool.not_false]
          (try wp_auto)
          wp_apply Hcl $$ [Hclo] as %e3 -
          · iexact Hclo
          (try wp_auto)
          iapply HΦ
          iframe Hpd Hperm HS Hj
          ileft
          isplitr
          · ipureintro; nofun
          iapply wal.vseErrIs_of_term
          iframe Hosp HeXt
    · -- another type
      have hn3 : r.typ ≠ crcType := Hif
      obtain ⟨-, hL', hFA', hLO', hkD'⟩ :=
        vse_step walCodec_ok hL hFAi hLOi hkD hgd hok.2 (fun h => hn3 h.1)
      ihave Hleft := leftS_merge fs fsD kD k hkD $$ [Hleft Hk]
      · iframe
      wp_for_post
      wp_apply (wp_Decode walCodec dec rcp IoE eof ueof (fsD.drop k) off' c' rfl)
        $$ [Hdec Hr] as %e' Hpost
      · iframe Hdec Hde; iapply ownRec_any $$ Hr
      iframe
      iexists acc ++ [r], fsD.drop k, kD + k, off', c', e', sv, ps, stp
      rw [vseSnaps_snoc_other acc hn1, vseHs_snoc_other hsZero acc hn2]
      rw [rdCrc_ne hn3] at hL' hFA'
      iframe
      ipureintro
      exact ⟨hL', hFA', hLO', hkD'⟩

end proof

end EtcdGrove
end Perennial

end
