/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/Unsaved.lean` (P6 of `notes/etcd-dist-d6.md` §10,
item 3): the update committed and every segment pinned at the step after the logger's check
(`walInv_openAll`, which also gives the WALs' step bound: the first segment's sequence number is below
`2^64`); with no WAL, `readWALNames` fails (`specAbsent`). With one: `readWALNames` over the claim's half,
`parseWALName` of the first name (sequence `first`, so `0` only when nothing was purged: `unsaved_blank`
reads from the WAL's start), `isValidSeq`, `openWALFiles` from 0 in read mode, the decoder over every
segment, and the decode loop as `validSnapshotEntries`' (`VsLoop`, `FilesAt`, `LaterOk`), its accepted
records `UnsAcc`; every return closes the files (the deferred closer) and puts the pin back
(`walInv_unpinAll`) at a step before it. Lean-first.
-/
module

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
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Unsaved
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.readWALNamesAbsent
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.parseWALName
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.isValidSeq
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.VsePin
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.NameLoans
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateArea
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CutName
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.UnsavedDefs

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

-- The put-back of the pin at a step before a return (`walInv_unpinAll`), in `wal.Unsaved.wp_proof`.
set_option hygiene false in
local macro "unsaved_putback" : tactic => `(tactic| (
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod walInv_unpinAll walCodec Mr R jr r dir lay X hj hS $$ Hinv Hnc [Hl Htf Hnf Ho HS Hj] with ⟨Hnc, Hu⟩
  · unfold walPinAllRes; iexists I; iframe; iframe #
  imodintro
  iframe Hnc))

-- `unsaved_putback` after the path was lent (`walInv_dirPath`): the path returned first.
set_option hygiene false in
local macro "unsaved_putbackP" : tactic => `(tactic| (
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod walInv_dirPathRetD walCodec Mr R jr r dir nmd qd lay.j hdn $$ Hinv Hnc Hnf Hpd with ⟨Hnc, Hnf⟩
  imod walInv_unpinAll walCodec Mr R jr r dir lay X hj hS $$ Hinv Hnc [Hl Htf Hnf Ho HS Hj] with ⟨Hnc, Hu⟩
  · unfold walPinAllRes; iexists I; iframe; iframe #
  imodintro
  iframe Hnc))

-- A return of `false`, the pin put back, in `wal.Unsaved.wp_proof`.
set_option hygiene false in
local macro "unsaved_false" : tactic => `(tactic| (
  iapply HΦ
  iframe Hp Hperm Hu
  isplitl [HN Hsf Hcl]
  · unfold walAreaRes; iexists N, h, cl, Wn; iframe
    ipureintro; exact ⟨hok.1, hok.2.1, hok.2.2.1, hok.2.2.2⟩
  iexists o
  iframe HQ
  ipureintro; intro hb; cases hb))

-- Every file closed and the pin put back at an early return of `false` inside the decode loop, in
-- `wal.Unsaved.wp_proof`.
set_option hygiene false in
local macro "unsaved_close" : tactic => `(tactic| (
  ihave Hall := vse_streams dec IoE eof fs fsD kD k off' c' true hkD $$ [Hleft Hk Hdec]
  · iframe
  ihave ⟨HS, Hclo⟩ := vse_close dir lay.segs fs fls lfs htie hcbs $$ [Hall]
  · iframe Hall; iexact Hfrf
  (try wp_auto)
  wp_for_post
  (try wp_auto)
  unsaved_putbackP
  (try wp_auto)
  wp_apply Hclz $$ [Hclo] as %e3 -
  · iexact Hclo
  (try wp_auto)
  unsaved_false))

/-- See the spec file's header. -/
theorem wal.Unsaved.wp_proof
    [os.file.FieldAssumptions] [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
    (Mr : WalMarshal) (U : WalUnmarshal) (hU : U.Ok Mr) (hUs : U.SnapCoh)
    (hEnv : WalDecEnvSupply (GF := GF))
    (wp_IsEof : errors.IsPathErrnoEof.spec (GF := GF) (hG := hG))
    (wp_Term : errors.IsPathErrnoTerm.spec (GF := GF) (hG := hG))
    (wp_names : go_etcd_io.etcd.server.v3.storage.wal.readWALNames.spec (GF := GF) (hG := hG))
    (wp_namesAbs : go_etcd_io.etcd.server.v3.storage.wal.readWALNames.specAbsent (GF := GF) (hG := hG))
    (wp_parse : go_etcd_io.etcd.server.v3.storage.wal.parseWALName.spec (GF := GF) (hG := hG))
    (wp_valid : go_etcd_io.etcd.server.v3.storage.wal.isValidSeq.spec (GF := GF) (hG := hG))
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
    wal.Unsaved.spec (W := W) Mr := by
  intro lg R jr r dir nm qp Q ic hin hnmO hr hdl
  have hdl' : dir.length < 4096 := hdl.1
  wp_start as ⟨#Hzap, #Hok, Hp, Hres, Hperm, Hu, Hau⟩
  ihave #Hok' := Hok
  iunfold WalFs.walAreaOk at Hok'
  icases Hok' with ⟨#Hinv, #Hosi, #Hsi, %hrb0, %hrb1, -⟩
  icases walAreaRes_open jr $$ Hres with ⟨%N, %h, %cl, %Wn, HN, Hsf, %hok, Hcl⟩
  have hnm := hin.1
  icases osPathS_callKey R r _ jr $$ Hp with ⟨Hp, %hkc⟩
  have hkd : callKey R dir = callKey R r := by rw [dir_child hin]; exact hkc nm
  have hdc := dir_child hin
  ihave %hlgn := zapLoggerOk_ne_null lg $$ Hzap
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  rw [decide_eq_false hlgn]
  (try wp_auto)
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod walInv_openAll walCodec Mr R jr r dir nm N _ h Wn Q ic hin (hok.1 nm hnm)
    $$ Hinv Hsi Hnc Hu Hau HN Hsf with ⟨Hnc, HN, Hsf, %o, HQ, Hcase⟩
  icases Hcase with (⟨⟨%ho, %hNnm, %hcn⟩, Hu⟩ | ⟨%d, %lay, %X, %hj, ⟨%hle, %hpin⟩, Hpin, #Hstp⟩)
  · -- no WAL: `readWALNames` fails
    subst ho
    imodintro
    iframe Hnc
    (try wp_auto)
    rw [hdc]
    wp_apply wp_namesAbs lg r nm R jr (DFrac.own qp) 1 N (DFrac.own (1 : Qp).half) h hnmO hNnm hcn $$ [Hp Hperm HN] as %rn %err
      ⟨Hp, Hperm, HN, %e, %herr, -, -⟩
    · iframe; iframe #
    subst herr
    (try wp_auto)
    iapply HΦ
    iframe Hp Hperm Hu
    isplitl [HN Hsf Hcl]
    · unfold walAreaRes; iexists N, h, cl, Wn; iframe
      ipureintro; exact ⟨hok.1, hok.2.1, hok.2.2.1, hok.2.2.2⟩
    iexists none
    iframe HQ
    ipureintro; intro hb; cases hb
  · -- a WAL: every segment pinned
    obtain ⟨hljr, hX, hcoh, habs, hid, hnd, hsn⟩ := hpin
    unfold walPinAllRes
    icases Hpin with ⟨%I, #Hkey, Hl, ⟨Htf, Hnf⟩, Ho, HS, Hj⟩
    icases walLockedTokI_incQ (W := W) I $$ Hl with ⟨HI, Hl⟩
    imod walInv_dirPath walCodec Mr R jr r dir I lay.j X [] $$ Hinv Hnc Hnf Hkey HI
      with ⟨Hnc, HI, %nmd, %qd, %hdn, Hnf, Hpd⟩
    ihave Hl := Hl $$ HI
    imodintro
    iframe Hnc
    ihave %hstl := preceipt_lt _ $$ Hstp
    have hHl : d.H.length < 2 ^ 62 := by have := hrb0.receiptBound_le; omega
    have hS : ∀ g ∈ lay.segs, g.om.size = g.bs.length := fun g hg => (habs.metas g hg).1
    rw [← hkd]
    wp_apply wp_names lg dir R lay.j (DFrac.own qd) 1 (.except X) (DFrac.own (1 : Qp).half) hj
      $$ [Hpd Hperm Hj] as %rn %err ⟨Hpd, Hperm, Hj, Hnm⟩
    · iframe; iframe #
    icases Hnm with (⟨%ws, ⟨%herr, %hout⟩, Hws⟩ | ⟨%e, %herr, #He, #Ht⟩)
    rotate_left
    · -- `readWALNames` failed
      subst herr
      unsaved_putbackP
      (try wp_auto)
      unsaved_false
    subst herr
    have hnmf := walLay_nameFmt habs
    have hws : ws = lay.segs.map (·.name) :=
      walNamesOut_segs hX hsn habs.names.1 hnd habs.names.2 hnmf hout
    (try wp_auto)
    -- `names[0]`: the first segment's, sequence `first`
    obtain ⟨g0, hg0⟩ : ∃ g0, lay.segs[0]? = some g0 := by
      cases hc : lay.segs with
      | nil => exact absurd hc habs.nonempty
      | cons g _ => exact ⟨g, rfl⟩
    obtain ⟨ix0, hix0⟩ := habs.seqName 0 g0 hg0
    have hws0 : ws[0]? = some g0.name := by rw [hws, List.getElem?_map, hg0]; rfl
    ihave %hwl := ownSlice_len $$ Hws
    have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rn.len := by
      have h1 : 0 < ws.length := by
        cases ws with
        | nil => simp at hws0
        | cons _ _ => simp
      have : sint.nat rn.len = (sint.Z rn.len).toNat := rfl
      have h0 : sint.Z (W64 0) = 0 := rfl
      omega
    simp only [hb0, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index rn (sint.Z (W64 0)) ws (DFrac.own 1) g0.name hb0.1 $$ [Hws] as Hws
    · iframe; ipureintro; exact hws0
    wp_apply wp_parse as %sq %ix %perr %hparse
    obtain ⟨hsuf, hscan⟩ := scanWalName_walFileName (lay.first + 0) ix0
    rw [← hix0] at hsuf hscan
    obtain ⟨hpe, hsq, hix⟩ := hparse.1 _ _ hsuf hscan
    subst hpe hsq hix
    (try wp_auto)
    have hfl : lay.first < 2 ^ 62 := by
      have h1 := habs.cuts.2.2
      have h2 := habs.cuts_le
      have h3 : 0 < lay.segs.length := List.length_pos_iff.2 habs.nonempty
      omega
    by_cases hf0 : lay.first = 0
    rotate_left
    · -- not sequence 0 (segments purged): `false`
      have e : decide (W64 ↑(lay.first + 0) = W64 0) = false := by
        rw [decide_eq_false_iff_not]; intro h0; apply hf0; word
      rw [e]
      unsaved_putbackP
      (try wp_auto)
      unsaved_false
    have e : (W64 ↑(lay.first + 0) = W64 0) := by rw [hf0]; rfl
    simp only [e, _root_.decide_true, Bool.not_true]
    (try wp_auto)
    by_cases hix : W64 ↑ix0 = W64 0
    rotate_left
    · -- index not 0: `false`
      simp only [hix, decide_false, Bool.not_false]
      unsaved_putbackP
      (try wp_auto)
      unsaved_false
    simp only [hix, _root_.decide_true, Bool.not_true]
    (try wp_auto)
    have hwsN : ∀ n ∈ ws, ∃ s i, n = fmt.walNameStr s i := by
      intro n hn
      rw [hws] at hn
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hn
      obtain ⟨sq, ix, hgn⟩ := hnmf g hg
      exact ⟨_, _, by rw [hgn, walFileName_walNameStr]⟩
    wp_apply wp_valid lg rn ws (DFrac.own 1) hwsN $$ [Hws] as Hws
    · iframe
    generalize walSeqOk 0 (ws.map walNameSeq) = vb
    cases vb
    · -- not consecutive: `false`
      simp only [Bool.not_false]
      unsaved_putbackP
      (try wp_auto)
      unsaved_false
    simp only [Bool.not_true]
    (try wp_auto)
    -- every segment opened read-only from the first
    have hwl : ws.length = lay.segs.length := by rw [hws, List.length_map]
    ihave #Hw : (wal.walInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    ihave #Hosp := wal_osInit $$ Hpkg
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
    icases Hopen with (⟨%frs, %lfs, ⟨%herr2, %hfl, %hll⟩, Hrsl, Hrc, Hlsl, Hlc, Hfiles, Hclz⟩ |
      ⟨%e, %herr, #He, Hte⟩)
    rotate_left
    · -- `openWALFiles` failed
      subst herr
      unsaved_putbackP
      (try wp_auto)
      unsaved_false
    subst herr2
    iunfold wal.walCloser at Hclz
    icases Hclz with ⟨%hcl, #Hclz⟩
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
    have hTy : ∀ r ∈ (rdRest walCodec (fs.map (·.bs)) 0 0#32).recs, WalTypKnown r.typ := by
      rw [rdRest_start, hbs]
      exact running_typ walCodec_ok habs hid.1 hid.2.1
    ihave %hnn := decEnv_nonnil IoE eof ueof $$ Hde
    irename «$r0» => Hrec0
    generalize «$r0_ptr» = rcp at *
    wp_apply (wp_Decode walCodec dec rcp IoE eof ueof fs 0 0#32 rfl) $$ [Hdec Hrec0] as %err0 Hpost
    · iframe Hdec Hde
      unfold ownRecAny
      iexists _
      iexact Hrec0
    (try wp_auto)
    ihave HI : (∃ (acc : List WalRec) (fsD : List (DecFile GF)) (kD off : Nat) (c : w32) (e : GoInterface)
        (ent : Bool),
        "err" ∷ err_ptr ↦ e ∗
        "Hpost" ∷ decPost walCodec dec rcp IoE eof ueof fsD off c e ∗
        "Hleft" ∷ ([∗list] F ∈ fs.take kD, ∃ q, F.S q) ∗
        "entries" ∷ entries_ptr ↦ ent ∗
        "%hinv" ∷ ⌜VsLoop walCodec (rdRest walCodec (fs.map (·.bs)) 0 0#32) acc (fsD.map (·.bs)) off c ∧
          FilesAt walCodec (fsD.map (·.bs)) off c ∧ LaterOk walCodec (fsD.map (·.bs)) ∧ fsD = fs.drop kD ∧
          UnsAcc U (acc.map (fun r => (r.typ, r.data)))⌝ : IProp GF)
        $$ [err Hpost entries]
    · iexists [], fs, 0, 0, 0#32, err0, false
      simp only [List.map_nil, List.take_zero, List.drop_zero]
      iframe
      isplitl []
      · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
      ipureintro
      exact ⟨vsLoop_start _ _, hFA, hLO, trivial, UnsAcc.nil U⟩
    irename «rec» => Hrecp
    wp_for HI
    obtain ⟨hL, hFAi, hLOi, hkD, hacc⟩ := hinv
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
          (if b then True else ⌜(rdRest walCodec (fs.map (·.bs)) 0 0#32).recs = acc⌝)))
        at (If _ _ (Val #false)) with [err]
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
                ipureintro; trivial
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
              ipureintro; trivial
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
            ipureintro; trivial
      iintro ⟨%b, %hv, err, Hb⟩
      subst hv
      cases b
      · -- the end of the WAL: `true`
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hb with %hrecs
        (try wp_auto)
        unsaved_putbackP
        (try wp_auto)
        wp_apply Hclz $$ [Hclo] as %e3 -
        · iexact Hclo
        (try wp_auto)
        have h1 : (walDecodeFiles walCodec (lay.segs.map segImg) 0#32).recs = acc := by
          rw [← hbs, ← rdRest_start]; exact hrecs
        have hbl := unsaved_blank walCodec_ok hU habs hid.1 hid.2.1 hf0 (by rw [h1]; exact hacc)
        iapply HΦ
        iframe Hp Hperm Hu
        isplitl [HN Hsf Hcl]
        · unfold walAreaRes; iexists N, h, cl, Wn; iframe
          ipureintro; exact ⟨hok.1, hok.2.1, hok.2.2.1, hok.2.2.2⟩
        iexists o
        iframe HQ
        ipureintro
        intro _
        refine ⟨rfl, ?_⟩
        obtain ⟨dc, rfl, hdc'⟩ : ∃ dc, o = some dc ∧ walDurLe dc d := by
          cases o with
          | none => exact absurd hle (by simp [walOptLe])
          | some dc => exact ⟨dc, rfl, hle⟩
        exact ⟨dc, rfl, by rw [hdc'.1]; exact hbl⟩
      · -- the decoder's error: `false`
        simp only [↓reduceIte]
        (try wp_auto)
        unsaved_putbackP
        (try wp_auto)
        wp_apply Hclz $$ [Hclo] as %e3 -
        · iexact Hclo
        (try wp_auto)
        unsaved_false
    -- the body: `err == nil`
    dsimp only
    (try wp_auto)
    iunfold decPost at Hpost
    iunfold decPostB at Hpost
    icases Hpost with ⟨⟨%k, Hk, Hm⟩ | ⟨%hio, -, -⟩ | ⟨%k, %sx, %offx, %cx, %hgf, -⟩, #Hans, -⟩
    rotate_left
    · exact absurd hio hIoN
    · exact absurd hgf.2 (stopErr_ne_nil hnn.1 hnn.2 sx)
    generalize hgd : goDecode walCodec (List.map (fun x => x.bs) fsD) off c = gd
    rcases gd with ⟨rd, fs', off', c'⟩ | ⟨sx, fs', off', c'⟩
    rotate_left
    · icases Hm with ⟨%hst, -, -⟩
      exact absurd hst.1 (stopErr_ne_nil hnn.1 hnn.2 sx)
    icases Hm with ⟨%hokd, Hr, Hdec⟩
    simp only [_root_.decide_true, ↓reduceIte]
    (try wp_auto)
    have hdec0 : ¬ (rd.typ = crcType ∧ crcRecBad c' rd) → RecDec U rd := fun hnc =>
      (hR0 rd (vse_step walCodec_ok hL hFAi hLOi hkD hgd hokd.2 hnc).1).1
    -- `entries && rec.GetType() != EntryType`: a record after an entry record
    wp_join (Q := fun v => iprop(∃ b : Bool, ⌜v = #b⌝ ∗ ownRec rcp rd ∗ rec_ptr ↦ rcp))
      at (If _ _ (Val #false)) with [Hr Hrecp]
    · cases ent
      · (try wp_auto)
        iexists false
        iframe
        ipureintro; rfl
      · (try wp_auto)
        wp_apply wp_GetType $$ Hr as Hr
        (try wp_auto)
        iexists _
        iframe
        ipureintro; rfl
    iintro ⟨%b, %hv, Hr, Hrecp⟩
    subst hv
    cases b
    rotate_left
    · -- `false`
      ihave Hall := vse_streams dec IoE eof fs fsD kD k off' c' true hkD $$ [Hleft Hk Hdec]
      · iframe
      ihave ⟨HS, Hclo⟩ := vse_close dir lay.segs fs fls lfs htie hcbs $$ [Hall]
      · iframe Hall; iexact Hfrf
      (try wp_auto)
      wp_for_post
      (try wp_auto)
      unsaved_putbackP
      (try wp_auto)
      wp_apply Hclz $$ [Hclo] as %e3 -
      · iexact Hclo
      (try wp_auto)
      unsaved_false
    (try wp_auto)
    wp_apply wp_GetType $$ Hr as Hr
    wp_if_destruct
    · -- EntryType
      have hT : rd.typ = entryType := Hif
      have hn3 : rd.typ ≠ crcType := by rw [hT]; simp [entryType, crcType]
      obtain ⟨-, hL', hFA', hLO', hkD'⟩ :=
        vse_step walCodec_ok hL hFAi hLOi hkD hgd hokd.2 (fun h => hn3 h.1)
      ihave Hleft := leftS_merge fs fsD kD k hkD $$ [Hleft Hk]
      · iframe
      (try wp_auto)
      wp_for_post
      wp_apply (wp_Decode walCodec dec rcp IoE eof ueof (fsD.drop k) off' c' rfl)
        $$ [Hdec Hr] as %e' Hpost
      · iframe Hdec Hde; iapply ownRec_any $$ Hr
      iframe
      iexists acc ++ [rd], fsD.drop k, kD + k, off', c', e', true
      rw [rdCrc_ne hn3] at hL' hFA'
      iframe
      ipureintro
      refine ⟨hL', hFA', hLO', hkD', ?_⟩
      rw [List.map_append]
      refine hacc.snoc ?_ ?_ <;> simp [hT, entryType, stateType, snapshotType]
    have hn0 : rd.typ ≠ entryType := Hif
    wp_if_destruct
    · -- StateType: `false`
      unsaved_close
    have hn2 : rd.typ ≠ stateType := Hif
    wp_if_destruct
    · -- SnapshotType
      have hT : rd.typ = snapshotType := Hif
      have hn3 : rd.typ ≠ crcType := by rw [hT]; simp [snapshotType, crcType]
      obtain ⟨p, hp⟩ := (hdec0 (fun h => hn3 h.1)).2.2 hT
      unfold ownRec
      icases Hr with ⟨%v, Hlv, Htv, Hcv, Hdv⟩
      (try wp_auto)
      wp_apply wp_UnmarshalSnap hUs snap_ptr v.Data' _ rd.data p hp $$ [snap Hdv] as ⟨Hdv, #Hsn⟩
      · iframe
      wp_apply wp_SnapIndex snap_ptr p $$ Hsn
      (try wp_auto)
      wp_if_destruct
      rotate_left
      · -- a snapshot above index 0: `false`
        unsaved_close
      have hp0 : p.1 = W64 0 := Hif
      obtain ⟨-, hL', hFA', hLO', hkD'⟩ :=
        vse_step walCodec_ok hL hFAi hLOi hkD hgd hokd.2 (fun h => hn3 h.1)
      ihave Hleft := leftS_merge fs fsD kD k hkD $$ [Hleft Hk]
      · iframe
      (try wp_auto)
      wp_for_post
      wp_apply (wp_Decode walCodec dec rcp IoE eof ueof (fsD.drop k) off' c' rfl)
        $$ [Hdec Hlv] as %e' Hpost
      · iframe Hdec Hde; unfold ownRecAny; iexists v; iexact Hlv
      iframe
      iexists acc ++ [rd], fsD.drop k, kD + k, off', c', e', ent
      rw [rdCrc_ne hn3] at hL' hFA'
      iframe
      ipureintro
      refine ⟨hL', hFA', hLO', hkD', ?_⟩
      rw [List.map_append]
      refine hacc.snoc hn2 (fun _ p' hp' => ?_)
      rw [hp] at hp'
      cases hp'
      exact hp0
    have hn1 : rd.typ ≠ snapshotType := Hif
    wp_if_destruct
    · -- MetadataType
      have hT : rd.typ = metadataType := Hif
      have hn3 : rd.typ ≠ crcType := by rw [hT]; simp [metadataType, crcType]
      obtain ⟨-, hL', hFA', hLO', hkD'⟩ :=
        vse_step walCodec_ok hL hFAi hLOi hkD hgd hokd.2 (fun h => hn3 h.1)
      ihave Hleft := leftS_merge fs fsD kD k hkD $$ [Hleft Hk]
      · iframe
      (try wp_auto)
      wp_for_post
      wp_apply (wp_Decode walCodec dec rcp IoE eof ueof (fsD.drop k) off' c' rfl)
        $$ [Hdec Hr] as %e' Hpost
      · iframe Hdec Hde; iapply ownRec_any $$ Hr
      iframe
      iexists acc ++ [rd], fsD.drop k, kD + k, off', c', e', ent
      rw [rdCrc_ne hn3] at hL' hFA'
      iframe
      ipureintro
      refine ⟨hL', hFA', hLO', hkD', ?_⟩
      rw [List.map_append]
      exact hacc.snoc hn2 (fun h => absurd h hn1)
    have hnm : rd.typ ≠ metadataType := Hif
    wp_if_destruct
    · -- CrcType
      have hT : rd.typ = crcType := Hif
      have hrc : rdCrc c' rd = rd.crc := by simp [rdCrc, hT]
      have hstep : ∀ (cz : w32), cz = c' → ¬ crcRecBad cz rd →
          VsLoop walCodec (rdRest walCodec (fs.map (·.bs)) 0 0#32) (acc ++ [rd])
            ((fsD.drop k).map (·.bs)) off' rd.crc ∧ FilesAt walCodec ((fsD.drop k).map (·.bs)) off' rd.crc ∧
          LaterOk walCodec ((fsD.drop k).map (·.bs)) ∧ fsD.drop k = fs.drop (kD + k) := by
        intro cz hcz hb
        subst hcz
        obtain ⟨-, hL', hFA', hLO', hkD'⟩ :=
          vse_step walCodec_ok hL hFAi hLOi hkD hgd hokd.2 (fun h => hb h.2)
        rw [hrc] at hL' hFA'
        exact ⟨hL', hFA', hLO', hkD'⟩
      have hacc' : UnsAcc U ((acc ++ [rd]).map (fun r => (r.typ, r.data))) := by
        rw [List.map_append]
        exact hacc.snoc hn2 (fun h => absurd h hn1)
      wp_apply wp_LastCRC dec IoE eof (fsD.drop k) off' c' true $$ Hdec as Hdec
      wp_if_destruct
      · -- the chain's CRC is zero: not checked
        obtain ⟨hL', hFA', hLO', hkD'⟩ := hstep _ rfl (fun h => h.1 rfl)
        ihave Hleft := leftS_merge fs fsD kD k hkD $$ [Hleft Hk]
        · iframe
        wp_apply wp_GetCrc $$ Hr as Hr
        wp_apply wp_UpdateCRC dec IoE eof (fsD.drop k) off' _ rd.crc true $$ [Hdec] as Hdec
        · iframe Hdec Hcrc
        wp_for_post
        wp_apply (wp_Decode walCodec dec rcp IoE eof ueof (fsD.drop k) off' rd.crc rfl)
          $$ [Hdec Hr] as %e' Hpost
        · iframe Hdec Hde; iapply ownRec_any $$ Hr
        iframe
        iexists acc ++ [rd], fsD.drop k, kD + k, off', rd.crc, e', ent
        iframe
        ipureintro
        exact ⟨hL', hFA', hLO', hkD', hacc'⟩
      · -- checked
        ihave #Hde2 := Hde
        iunfold decEnv at Hde2
        icases Hde2 with ⟨-, -, #Hfmt, -, -, #Heof2, -, -, -, ⟨%ecm, #Hcm, #Hcmok, #Hcmnot, #Hcmt⟩, -⟩
        ihave %heofT := decEnv_eof_target _ _ _ $$ Hde
        wp_apply wp_Validate rcp rd c' ecm eof heofT $$ [Hr] as %verr ⟨Hr, Hv⟩
        · iframe Hr; iframe #
        icases Hv with (⟨%hv1, %hv2⟩ | ⟨%hne, %ei, %hei, -, -, -⟩)
        · subst hv1
          obtain ⟨hL', hFA', hLO', hkD'⟩ := hstep _ rfl (fun h => h.2 hv2)
          ihave Hleft := leftS_merge fs fsD kD k hkD $$ [Hleft Hk]
          · iframe
          (try wp_auto)
          wp_apply wp_GetCrc $$ Hr as Hr
          wp_apply wp_UpdateCRC dec IoE eof (fsD.drop k) off' _ rd.crc true $$ [Hdec] as Hdec
          · iframe Hdec Hcrc
          wp_for_post
          wp_apply (wp_Decode walCodec dec rcp IoE eof ueof (fsD.drop k) off' rd.crc rfl)
            $$ [Hdec Hr] as %e' Hpost
          · iframe Hdec Hde; iapply ownRec_any $$ Hr
          iframe
          iexists acc ++ [rd], fsD.drop k, kD + k, off', rd.crc, e', ent
          iframe
          ipureintro
          exact ⟨hL', hFA', hLO', hkD', hacc'⟩
        · -- a CRC mismatch: `ErrCRCMismatch`, every file closed
          subst hei
          (try wp_auto)
          ihave #HeX := wal.walInit_ErrCRCMismatch $$ Hw
          iunfold wal.errVar at HeX
          icases HeX with ⟨%eX, #HeX, -, #HeXt⟩
          unsaved_close
    · -- another type: none
      have hn3 : rd.typ ≠ crcType := Hif
      exfalso
      have hm := (vse_step walCodec_ok hL hFAi hLOi hkD hgd hokd.2 (fun h => hn3 h.1)).1
      rcases hTy rd hm with h | h | h | h | h
      · exact hn0 h
      · exact hn2 h
      · exact hn1 h
      · exact hnm h
      · exact hn3 h

end proof

end EtcdGrove
end Perennial

end
