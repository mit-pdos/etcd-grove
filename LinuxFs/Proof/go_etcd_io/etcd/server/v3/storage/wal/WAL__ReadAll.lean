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
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllTail
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllEnd
public import LinuxFs.Proof.os.Off
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

/-- The only stop whose error is `io.EOF` is `.eof` (`io.ErrUnexpectedEOF` is not `io.EOF`). -/
theorem stopErr_eof {eof ueof : GoInterface} (h : eof ≠ ueof) (s : WalStop)
    (hs : stopErr eof ueof s eof) : s = .eof := by
  cases s
  all_goals try rename_i t; cases t
  all_goals simp_all [stopErr]

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

theorem walEntsIn_len (P : WalPbIn GF) (esL : List Loc) (es : List EntryM) :
    walEntsIn P esL es ⊢ ⌜esL.length = es.length⌝ := by
  unfold walEntsIn; exact BigSepL2.bigSepL2_length

theorem walEntsIn_take (P : WalPbIn GF) (esL : List Loc) (es : List EntryM) (n : Nat) :
    walEntsIn P esL es ⊢ walEntsIn P (esL.take n) (es.take n) := by
  iintro H
  ihave %hl := walEntsIn_len P esL es $$ H
  unfold walEntsIn
  rw [← List.take_append_drop n esL, ← List.take_append_drop n es]
  icases (BigSepL2.bigSepL2_append (Φ := fun _ l e => P.entIn l e)
    (Or.inl (by simp [List.length_take, hl]))).1 $$ H with ⟨H, -⟩
  simp only [List.take_append_drop]
  iexact H

theorem walEntsIn_snoc (P : WalPbIn GF) (esL : List Loc) (es : List EntryM) (l : Loc) (e : EntryM) :
    walEntsIn P esL es ∗ P.entIn l e ⊢ walEntsIn P (esL ++ [l]) (es ++ [e]) := by
  unfold walEntsIn; exact BigSepL2.bigSepL2_snoc.2

theorem raArgWf_uint64 (v : w64) :
    fmt.ArgWf (interface.mk go.uint64 #v) :=
  ⟨fun h => by simp [go.uint64, go.string] at h, fun _ => ⟨_, .uint64 v⟩,
    Or.inl (Or.inr (Or.inr (Or.inl (by simp [fmt.IsIntType]))))⟩

theorem raArgWf_int (v : w64) :
    fmt.ArgWf (interface.mk go.int #v) :=
  ⟨fun h => by simp [go.int, go.string] at h, fun _ => ⟨_, .int v⟩,
    Or.inl (Or.inr (Or.inr (Or.inl (by simp [fmt.IsIntType]))))⟩

/-- The entry arm's offset: `e.GetIndex() - start - 1`, no wrap above the start. -/
theorem entOff_nat (ei si : w64) (h : uint.nat si < uint.nat ei) :
    uint.nat (ei - si - W64 1) = uint.nat ei - uint.nat si - 1 := by
  word

/-- At `io.EOF` the decoder holds no file (`goDecode`'s `.eof` stops are at the end of the last file). -/
theorem decRecStep_ne_eof (C : WalCodec) (last : Bool) (f : List w8) (off : Nat) (c c' : w32) :
    decRecStep C last f off c ≠ .stop .eof c' := by
  unfold decRecStep
  simp only
  intro h
  repeat' (first | (split at h) | (cases h))

theorem goDecode_eof_nil {C : WalCodec} :
    ∀ {fs fs' : List (List w8)} {off off' : Nat} {c c' : w32},
    goDecode C fs off c = .stop .eof fs' off' c' → fs' = []
  | [], _, _, _, _, _, h => by unfold goDecode at h; cases h; rfl
  | f :: fs, fs', off, off', c, c', h => by
    unfold goDecode at h
    generalize hs : decRecStep C fs.isEmpty f off c = st at h
    cases st with
    | eof =>
      cases fs with
      | nil => cases h; rfl
      | cons g gs => exact goDecode_eof_nil h
    | stop s c'' =>
      cases h
      exact absurd hs (decRecStep_ne_eof C _ f off c _)
    | accept r len c'' => cases h

/-- The tail's offset for `Seek`: below ext4's maximum. -/
theorem seekOff_ok (n : Nat) (h : n ≤ 0xffffffff000) :
    0 ≤ (W64 (n : Int)).toInt ∧ (W64 (n : Int)).toInt ≤ 0xffffffff000 := by
  have : (W64 (n : Int)).toInt = n := by word
  omega

set_option maxHeartbeats 2000000 in
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.ReadAll.wp_proof [os.file.FieldAssumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
    (P : WalPbIn GF) (Mr : WalMarshal) (U : WalUnmarshal) (hU : U.Ok Mr)
    (HsO : Loc → HardStateM → IProp GF) (hHs : WalHsOwn P U HsO)
    (wp_Decode : go_etcd_io.etcd.server.v3.storage.wal.decoder.Decode.spec (GF := GF) (hG := hG))
    (wp_LastCRC : go_etcd_io.etcd.server.v3.storage.wal.decoder.LastCRC.spec (GF := GF) (hG := hG))
    (wp_UpdateCRC : go_etcd_io.etcd.server.v3.storage.wal.decoder.UpdateCRC.spec (GF := GF) (hG := hG))
    (wp_LastOffset : go_etcd_io.etcd.server.v3.storage.wal.decoder.LastOffset.spec (GF := GF) (hG := hG))
    (wp_Sum32 : go_etcd_io.etcd.pkg.v3.crc.digest.Sum32.spec (GF := GF) (hG := hG))
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
  intro R jr rt dir nm w s qp qc Q hin hcl
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
  imod walInv_readFiles walCodec Mr R jr rt dir j X hj gs
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
  ihave Hl0 : ([∗list] F ∈ ([] : List (DecFile GF)), ∃ q, F.S q) $$ []
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  ihave HI : (∃ (acc : List WalRec) (fsD : List (DecFile GF)) (kD : Nat) (off : Nat) (c : w32) (st : RAState)
      (ix : w64 × w64) (e : GoInterface) (mdv : GoSlice) (stp : Loc) (entsv : GoSlice) (esL : List Loc),
      "err" ∷ err_ptr ↦ e ∗
      "Hpost" ∷ decPost walCodec dec «$r0_ptr» IoE eof ueof fsD off c e ∗
      "Hleft" ∷ ([∗list] F ∈ fs.take kD, ∃ q, F.S q) ∗
      "metadata" ∷ metadata_ptr ↦ mdv ∗ "Hmdv" ∷ mdv ↦* st.md.getD [] ∗
      "state" ∷ state_ptr ↦ stp ∗ "Hhs" ∷ HsO stp st.hs ∗
      "ents" ∷ ents_ptr ↦ entsv ∗ "Hents" ∷ entsv ↦* esL ∗
      "Hecap" ∷ ownSliceCap Loc entsv (DFrac.own 1) ∗ "Hein" ∷ walEntsIn P esL st.ents ∗
      "Hmatch" ∷ match_ptr ↦ st.matched ∗
      "Henti" ∷ structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"enti" w ↦ ix.1 ∗
      "Hsnapi" ∷ structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"snapi" w ↦ ix.2 ∗
      "%hinv" ∷ ⌜RdLoop walCodec U s (rdRest walCodec (fs.map (·.bs)) 0 0#32) acc (fsD.map (·.bs)) off c
          st ix ∧ fsD = fs.drop kD ∧ (st.md = none → mdv = slice.nil) ∧
        (∀ dd, st.md = some dd → dd = d0.metadata)⌝ : IProp GF)
      $$ [err Hpost Hl0 metadata Hmd0 state Hhs ents He0 Hec0 «match» Henti Hsnapi]
  · iexists [], fs, 0, 0, 0#32, raInit, (W64 0, W64 0), err0, slice.nil, _, slice.nil, []
    simp only [raInit, Option.getD_none, walEntsIn, List.take_zero]
    iframe
    iframe Hmd0 He0 Hec0
    isplitr
    · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro
    ipureintro
    exact ⟨rdLoop_start _ _ _ _, rfl, fun _ => trivial, fun _ h => by simp at h⟩
  irename «rec» => Hrec
  wp_for HI
  obtain ⟨hL, hkD, hmdn, hmdd⟩ := hinv
  (try wp_auto)
  rcases e with ei | _
  · -- the loop's exit
    dsimp only
    (try wp_auto)
    simp only [intoVal_eq_iff, Bool.false_eq_true, decide_false, decide_true, ↓reduceIte]
    -- `w.tail() != nil` (write mode)
    obtain ⟨ls, lt, rfl⟩ : ∃ ls lt, lfs = ls ++ [lt] := by
      rcases List.eq_nil_or_concat lfs with h | ⟨L, b, h⟩
      · subst h
        have h0 : gs.length = 0 := by simpa using hll.symm
        exact absurd (List.eq_nil_of_length_eq_zero h0) hgne
      · exact ⟨L, b, by simpa using h⟩
    (try wp_auto)
    wp_apply (wp_tail w locks ls lt (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls] as ⟨Hlocks, Hls⟩
    · iframe
    ihave #HltL := (BigSepL.bigSepL_snoc (PROP := IProp GF)).1 $$ Hlks
    icases HltL with ⟨-, #HltL⟩
    ihave #Hlt0 := HltL
    iunfold fileutil.lockedFile at Hlt0
    ihave %hltn := typedPointsto_not_null lt _ _ $$ Hlt0
    simp only [decide_eq_false hltn]
    (try wp_auto)
    -- the mode check: only `io.EOF`
    iunfold decPost at Hpost
    icases Hpost with ⟨Hpb, #Hans⟩
    iunfold decAns at Hans
    icases Hans with (%hn0 | #Hans)
    · exact absurd hn0 (by simp)
    ihave #Hde := Hdenv
    iunfold decEnv at Hde
    icases Hde with ⟨-, -, -, -, -, #Heofp, -⟩
    (try wp_auto)
    iunfold isEofAns at Hans
    wp_apply Hans as %b %hb
    subst hb
    by_cases heof : GoInterface.ok ei = eof
    · simp only [heof, decide_true]
      (try wp_auto)
      -- the stop is `io.EOF`: the reader read every record (`rdLoop_stop`)
      ihave #Hde2 := Hdenv
      iunfold decEnv at Hde2
      icases Hde2 with ⟨-, -, -, -, -, -, -, #Hiseof, -⟩
      iunfold isEofOk at Hiseof
      icases Hiseof with ⟨%hEu, -⟩
      iunfold decPostB at Hpb
      icases Hpb with (⟨%k, Hk, Hm⟩ | ⟨%hio, -, -⟩ | ⟨%k, %sx, %offx, %cx, %hgf, -⟩)
      · ihave Hleft := leftS_merge fs fsD kD k hkD $$ [Hleft Hk]
        · iframe
        generalize hgd : goDecode walCodec (List.map (fun x => x.bs) fsD) off c = gd
        rcases gd with ⟨r, fs', off', c'⟩ | ⟨sx, fs', off', c'⟩
        · icases Hm with ⟨%hst, -, -⟩
          exact absurd hst.1 hnn.1
        · icases Hm with ⟨%hst, Hrec0, Hdec⟩
          have hsx : sx = .eof := stopErr_eof hEu.1 sx hst.1
          subst hsx
          obtain ⟨hR0r, hR0s⟩ := rdLoop_stop hL hgd
          obtain ⟨hR0o, hR0c⟩ := rdLoop_stop_end hL hgd (fun t h => by cases h)
          simp only [decide_true]
          (try wp_auto)
          -- the decoder holds no file: every file's stream is in `Hleft`
          have hnil : fsD.drop k = [] := by
            have h2 := hst.2
            rw [goDecode_eof_nil hgd] at h2
            exact List.map_eq_nil_iff.1 h2
          have htk : fs.take (kD + k) = fs := by
            apply List.take_of_length_le
            have := List.drop_eq_nil_iff.1 hnil
            have h3 : fsD.length = fs.length - kD := by rw [hkD, List.length_drop]
            omega
          rw [htk]
          -- where the reader ended: the tail's write position, the chain's CRC (`ReadAllEnd`)
          have hkk : kk < lay.segs.length := by
            refine Nat.lt_of_not_le fun h => hgne ?_
            rw [← hgs]; exact List.drop_eq_nil_of_le h
          have hendP := walReadFiles_running_end walCodec_ok hab hex hwr kk hkk
          have hR0eq : rdRest walCodec (fs.map (·.bs)) 0 0#32 =
              walDecodeFiles walCodec ((lay.segs.drop kk).map segImg) 0#32 := by
            rw [rdRest_start, decFiles_bs hfl (fun k F g h1 h2 => (hfk k F g h1 h2).1), hgs]
          have hoffw : off' = lay.wr := by rw [← hR0o, hR0eq, hendP.1]
          have hcrcw : c' = chainEnd walCodec 0#32
              (recsOfSegs walCodec Mr d0.metadata (segsOf (histM d0) lay.cuts)) := by
            rw [← hR0c, hR0eq, hendP.2]
          -- the last file: the tail
          obtain ⟨fsI, Fl, hfsI⟩ : ∃ fsI Fl, fs = fsI ++ [Fl] := by
            rcases List.eq_nil_or_concat fs with h | ⟨L, b, h⟩
            · subst h
              exact absurd (List.eq_nil_of_length_eq_zero (by simpa using hfl.symm)) hgne
            · exact ⟨L, b, by simpa using h⟩
          have hnI : fsI.length + 1 = gs.length := by rw [← hfl, hfsI]; simp
          obtain ⟨gl, hgl⟩ : ∃ gl, gs[fsI.length]? = some gl :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          have hglast : gs.getLast? = some gl := by
            rw [List.getLast?_eq_getElem?, show gs.length - 1 = fsI.length by omega, hgl]
          have hglm : gl ∈ gs := List.mem_of_getElem? hgl
          obtain ⟨-, -, fl, fdl, hflk, hFS⟩ := hfk fsI.length Fl gl (by rw [hfsI]; simp) hgl
          have hwrle := walReadFiles_wr_le hab hex hwr kk gs hgs gl hglast
          have hlsl : ls.length = fsI.length := by
            have := hll; simp only [List.length_append, List.length_singleton] at this; omega
          have hgetD : fls.getD ls.length null = fl := by
            rw [List.getD_eq_getElem?_getD, hlsl, hflk]; rfl
          obtain ⟨frl, bsl, Sl⟩ := Fl
          simp only at hFS
          subst hFS
          rw [hfsI]
          icases (BigSepL.bigSepL_snoc (PROP := IProp GF)).1 $$ Hleft with ⟨Hleft, ⟨%ql, Hsl⟩⟩
          iunfold walFileS at Hsl
          icases Hsl with ⟨⟨%hql, %hfdl⟩, Hfl, Hfdl, Hoffl, Hml, Hbyl⟩
          -- `w.tail().Seek(w.decoder.LastOffset(), io.SeekStart)`
          wp_apply (wp_LastOffset dec IoE eof _ off' c' _) $$ [$Hdec] as Hdec
          (try wp_auto)
          wp_apply (wp_tail w locks ls lt (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls] as ⟨Hlocks, Hls⟩
          · iframe
          rw [hgetD]
          ihave #Hlt1 := HltL
          iunfold fileutil.lockedFile at Hlt1
          iStructNamed Hlt1
          rw [MethodUnfold.method_unfold
            (t := go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty) (m := go!"Seek")]
          wp_call
          (try wp_auto)
          iapply (Fs.wp_osMeta_size _ _ rfl gl.ino _ gl.om) $$ Hml
          iintro %hszl Hml
          have hoffb : off' ≤ 0xffffffff000 := by
            have h1 := hgsz gl hglm; have h2 : Fs.maxBytes = 0xffffffff000 := rfl; rw [hoffw]; omega
          obtain ⟨hso1, hso2⟩ := seekOff_ok off' hoffb
          wp_apply (os.File.Seek.wp_start fl fdl _ (DFrac.own 1) _ (W64 (off' : Int)) hfdl hso1 hso2)
            $$ [$Hfl $Hoffl] as ⟨Hfl, Hoffl⟩
          (try wp_auto)
          sorry
      · exact absurd hio hEu.2
      · exfalso
        obtain ⟨t, rfl⟩ := goFail_badRec hgf.1
        have h2 := hgf.2
        cases t
        · exact h2.2 rfl
        · exact hEu.1 h2
    · -- not `io.EOF`: the decoder's error
      simp only [heof, decide_false]
      (try wp_auto)
      wp_apply hHs.reset stp st.hs $$ Hhs as Hhs
      (try wp_auto)
      iapply readAll_failWp walCodec Mr R jr rt w dir s _ Q _ _ rfl $$ Hinv Hgh Hau
      iintro %dq HQ Hfail
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hlocked]
      · ipureintro; trivial
      iapply HΦ
      iframe Hp Hperm
      iexists dq
      iframe HQ
      ileft
      isplitr
      · ipureintro; simp
      unfold walReadFailedF
      iframe Hfail
      iexists lg
      iframe Hlg Hdir Hzap
  · -- the body: `err == nil`
    dsimp only
    (try wp_auto)
    iunfold decPost at Hpost
    iunfold decPostB at Hpost
    icases Hpost with ⟨⟨%k, Hk, Hm⟩ | ⟨%hio, -, -⟩ | ⟨%k, %sx, %offx, %cx, %hgf, -⟩, #Hans⟩
    · ihave Hleft := leftS_merge fs fsD kD k hkD $$ [Hleft Hk]
      · iframe
      generalize hgd : goDecode walCodec (List.map (fun x => x.bs) fsD) off c = gd
      rcases gd with ⟨r, fs', off', c'⟩ | ⟨sx, fs', off', c'⟩
      · icases Hm with ⟨%hok, Hr, Hdec⟩
        simp only [decide_true, ↓reduceIte]
        wp_auto
        wp_apply wp_GetType $$ Hr as Hr
        have hdec0 : ¬ (r.typ = crcType ∧ crcRecBad c' r) → RecDec U r ∧ RecMd d0.metadata r :=
          fun hnc => hR0 r (rdLoop_mem hL hgd hnc)
        wp_if_destruct
        · -- EntryType
          have hT : r.typ = entryType := Hif
          have hnc : ¬ (r.typ = crcType ∧ crcRecBad c' r) := by
            rw [hT]; simp [entryType, crcType]
          obtain ⟨e, he⟩ := (hdec0 hnc).1.1 hT
          unfold ownRec
          icases Hr with ⟨%v, Hl, Ht, Hc, Hd⟩
          wp_auto
          wp_apply wp_UnmarshalEnt v.Data' _ r.data e he $$ Hd as %el ⟨Hd, #Hel⟩
          ihave %hlE := walEntsIn_len P esL st.ents $$ Hein
          ihave %hlS := ownSlice_len (GF := GF) entsv _ esL $$ Hents
          ihave %hcS := ownSliceCap_wf (GF := GF) (V := Loc) entsv _ $$ Hecap
          wp_apply wp_EntIndex el e $$ Hel
          wp_apply wp_SnapIndex sp s $$ Hsp
          by_cases hle : uint.nat e.Index' ≤ uint.nat s.1
          · -- at or below the start: `ents = ents[:0]`
            have hre : readEnt (uint.nat s.1) st.ents e = some [] := by simp [readEnt, hle]
            have hst : raStep U s st (r.typ, r.data) = .ok { st with ents := [] } := by
              simp [raStep, hT, he, hre]
            have hix : raIdx U s ix r = (e.Index', ix.2) := by simp [raIdx, hT, he]
            have hL' := rdLoop_next hL hgd hok.2 hnc hst
            rw [hix, rdCrc_other (by rw [hT]; simp [entryType, crcType])] at hL'
            wp_if_destruct
            · have hb : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧
                  sint.Z (W64 0) ≤ sint.Z entsv.cap) := by
                refine ⟨by decide, Int.le_refl _, ?_⟩
                have : sint.Z (W64 0) = 0 := rfl
                omega
              simp only [hb]
              icases ownSlice_slice_with_cap (W64 0) (W64 0) entsv esL ⟨by decide, Int.le_refl _, by
                  have : sint.Z (W64 0) = 0 := rfl
                  omega⟩ $$ [Hents Hecap] with ⟨-, Hents, Hecap⟩
              · iframe
              rw [show subslice (sint.nat (W64 0)) (sint.nat (W64 0)) esL = [] by simp [subslice]]
              wp_auto
              wp_apply wp_EntIndex el e $$ Hel
              wp_apply wp_SnapIndex sp s $$ Hsp
              wp_if_destruct
              · exfalso; word
              wp_apply wp_EntIndex el e $$ Hel
              (try wp_auto)
              wp_for_post
              wp_apply (wp_Decode walCodec dec «$r0_ptr» IoE eof ueof (fsD.drop k) off' c' rfl)
                $$ [Hdec Hl] as %e' Hpost
              · iframe Hdec Hdenv; unfold ownRecAny; iexists v; iexact Hl
              iframe
              iexists acc ++ [r], fsD.drop k, kD + k, off', c', { st with ents := [] }, (e.Index', ix.2), e',
                mdv, stp, _, []
              iframe
              isplitr
              · simp only [walEntsIn]; iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro
              ipureintro
              exact ⟨hL', by rw [hkD, List.drop_drop], hmdn, hmdd⟩
            · exfalso; apply Hif; word
          · -- above the start: the offset
            have hlt : uint.nat s.1 < uint.nat e.Index' := by omega
            wp_if_destruct
            · exfalso; word
            wp_apply wp_EntIndex el e $$ Hel
            wp_apply wp_SnapIndex sp s $$ Hsp
            wp_if_destruct
            · wp_apply wp_EntIndex el e $$ Hel
              wp_apply wp_SnapIndex sp s $$ Hsp
              (try wp_auto)
              have hoff := entOff_nat e.Index' s.1 hlt
              wp_if_destruct
              · -- `offset > len(ents)`: `ErrSliceOutOfRange`
                ihave #Hwi : (wal.walInit : IProp GF) $$ []
                · iapply isPkgInit_access $$ Hpkg
                iunfold wal.walInit at Hwi
                icases Hwi with ⟨-, -, -, -, -, -, -, -, -, #HeX, -⟩
                iunfold wal.errVar at HeX
                icases HeX with ⟨%eX, #HeX, #HeXok⟩
                (try wp_auto)
                wp_apply wp_SnapIndex sp s $$ Hsp
                wp_apply wp_SnapTerm sp s $$ Hsp
                wp_apply wp_EntIndex el e $$ Hel
                wp_apply wp_EntTerm el e $$ Hel
                (try wp_auto)
                wp_apply wp_slice_literal
                isplitr
                · ipureintro; rfl
                iintro %asl ⟨Hasl, -⟩
                wp_apply wp_Errorf _ _ [GoInterface.ok eX, interface.mkOk go.uint64 #s.1,
                    interface.mkOk go.uint64 #s.2, interface.mkOk go.uint64 #e.Index',
                    interface.mkOk go.uint64 #e.Term', interface.mkOk go.int #entsv.len] [eX] (by
                    intro ii hii
                    simp only [List.mem_cons, List.not_mem_nil, or_false, interface.mkOk] at hii
                    rcases hii with h | h | h | h | h | h
                    · right; cases h; simp
                    all_goals (left; cases h; first | exact raArgWf_uint64 _ | exact raArgWf_int _))
                  $$ [Hasl] as %e1 #He1
                · iframe
                  iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
                  iexact HeXok
                (try wp_auto)
                wp_for_post
                iapply readAll_failWp walCodec Mr R jr rt w dir s _ Q _ _ rfl $$ Hinv Hgh Hau
                iintro %dq HQ Hfail
                wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hlocked]
                · ipureintro; trivial
                iapply HΦ
                iframe Hp Hperm
                iexists dq
                iframe HQ
                ileft
                isplitr
                · ipureintro; simp
                unfold walReadFailedF
                iframe Hfail
                iexists lg
                iframe Hlg Hdir Hzap
              · -- `ents = append(ents[:offset], e)`
                have hoL : uint.nat (e.Index' - s.1 - W64 1) ≤ esL.length := by
                  have h1 : ¬ uint.Z entsv.len < uint.Z (e.Index' - s.1 - W64 1) := Hif
                  word
                have hon : uint.nat (e.Index' - s.1 - W64 1) = uint.nat e.Index' - uint.nat s.1 - 1 := hoff
                have hre : readEnt (uint.nat s.1) st.ents e =
                    some (st.ents.take (uint.nat e.Index' - uint.nat s.1 - 1) ++ [e]) := by
                  have h2 : uint.nat e.Index' - uint.nat s.1 - 1 ≤ st.ents.length := by omega
                  simp only [readEnt, hle, h2, ↓reduceIte]
                have hst : raStep U s st (r.typ, r.data) =
                    .ok { st with ents := st.ents.take (uint.nat e.Index' - uint.nat s.1 - 1) ++ [e] } := by
                  simp [raStep, hT, he, hre]
                have hix : raIdx U s ix r = (e.Index', ix.2) := by simp [raIdx, hT, he]
                have hL' := rdLoop_next hL hgd hok.2 hnc hst
                rw [hix, rdCrc_other (by rw [hT]; simp [entryType, crcType])] at hL'
                have hsZ : sint.Z (e.Index' - s.1 - W64 1) ≤ sint.Z entsv.len := by word
                have hb : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (e.Index' - s.1 - W64 1) ∧
                    sint.Z (e.Index' - s.1 - W64 1) ≤ sint.Z entsv.cap) := by
                  have : sint.Z (W64 0) = 0 := rfl
                  refine ⟨by decide, ?_, by omega⟩
                  rw [this]; word
                simp only [hb]
                icases ownSlice_slice_with_cap (W64 0) (e.Index' - s.1 - W64 1) entsv esL
                    ⟨hb.1, hb.2.1, hsZ⟩ $$ [Hents Hecap] with ⟨-, Hents, Hecap⟩
                · iframe
                have hsub : subslice (sint.nat (W64 0)) (sint.nat (e.Index' - s.1 - W64 1)) esL =
                    esL.take (uint.nat e.Index' - uint.nat s.1 - 1) := by
                  have h0 : sint.nat (W64 0) = 0 := rfl
                  have h1 : sint.nat (e.Index' - s.1 - W64 1) = uint.nat e.Index' - uint.nat s.1 - 1 := by
                    rw [← hon]; word
                  rw [h0, h1]; simp [subslice]
                rw [hsub]
                ihave #Hein' := walEntsIn_take P esL st.ents (uint.nat e.Index' - uint.nat s.1 - 1) $$ Hein
                (try wp_auto)
                wp_apply wp_slice_literal (V := Loc) [el]
                isplitr
                · ipureintro; rfl
                iintro %asl ⟨Hasl, Hcl⟩
                wp_apply wp_slice_append $$ [Hents Hecap Hasl] as %sl' ⟨Hents, Hecap, -⟩
                · iframe
                (try wp_auto)
                wp_apply wp_EntIndex el e $$ Hel
                (try wp_auto)
                wp_for_post
                wp_apply (wp_Decode walCodec dec «$r0_ptr» IoE eof ueof (fsD.drop k) off' c' rfl)
                  $$ [Hdec Hl] as %e' Hpost
                · iframe Hdec Hdenv; unfold ownRecAny; iexists v; iexact Hl
                ihave Hein2 := walEntsIn_snoc P (esL.take (uint.nat e.Index' - uint.nat s.1 - 1))
                  (st.ents.take (uint.nat e.Index' - uint.nat s.1 - 1)) el e $$ []
                · isplitr
                  · iexact Hein'
                  · iexact Hel
                iframe
                iexists acc ++ [r], fsD.drop k, kD + k, off', c',
                  { st with ents := st.ents.take (uint.nat e.Index' - uint.nat s.1 - 1) ++ [e] },
                  (e.Index', ix.2), e', mdv, stp, sl', _
                iframe
                ipureintro
                exact ⟨hL', by rw [hkD, List.drop_drop], hmdn, hmdd⟩
            · exfalso; apply Hif; word
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
          iexists acc ++ [r], fsD.drop k, kD + k, off', c', { st with hs := h }, ix, e', mdv, p, entsv, esL
          iframe
          ipureintro
          exact ⟨hL', by rw [hkD, List.drop_drop], hmdn, hmdd⟩
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
            iexists acc ++ [r], fsD.drop k, kD + k, off', c', { st with md := some r.data }, ix, e', v.Data', stp,
              entsv, esL
            simp only [Option.getD_some]
            iframe
            ipureintro
            exact ⟨hL', by rw [hkD, List.drop_drop], fun h => by simp at h,
              fun dd h => by simp only [Option.some.injEq] at h; rw [← h, hmd]⟩
          · -- `metadata != nil`: the same metadata
            obtain ⟨dd, hdd⟩ : ∃ dd, st.md = some dd := by
              rcases h : st.md with _ | dd
              · exact absurd (hmdn h) (by assumption)
              · exact ⟨dd, rfl⟩
            rw [hdd, Option.getD_some]
            wp_apply bytes.Equal.wp_proof $$ [Hmdv Hd] as ⟨Hmdv, Hd⟩
            · iframe
            simp only [hmdd dd hdd, ← hmd, _root_.decide_true]
            wp_auto
            wp_for_post
            wp_apply (wp_Decode walCodec dec «$r0_ptr» IoE eof ueof (fsD.drop k) off' c' rfl)
              $$ [Hdec Hl] as %e' Hpost
            · iframe Hdec Hdenv; unfold ownRecAny; iexists v; iexact Hl
            iframe
            iexists acc ++ [r], fsD.drop k, kD + k, off', c', { st with md := some r.data }, ix, e', v.Data', stp,
              entsv, esL
            simp only [Option.getD_some]
            iframe
            ipureintro
            exact ⟨hL', by rw [hkD, List.drop_drop], fun h => by simp at h,
              fun dd h => by simp only [Option.some.injEq] at h; rw [← h, hmd]⟩
        wp_if_destruct
        · -- CrcType
          have hT : r.typ = crcType := Hif
          have hi1 : r.typ ≠ entryType := by rw [hT]; simp [crcType, entryType]
          have hi2 : r.typ ≠ snapshotType := by rw [hT]; simp [crcType, snapshotType]
          have hst : raStep U s st (r.typ, r.data) = .ok st := by
            simp [raStep, hT, crcType, entryType, stateType, metadataType]
          have hL' : ¬ (r.typ = crcType ∧ crcRecBad c' r) →
              RdLoop walCodec U s (rdRest walCodec (fs.map (·.bs)) 0 0#32) (acc ++ [r])
                ((fsD.drop k).map (·.bs)) off' r.crc st ix := by
            intro hnc
            have := rdLoop_next hL hgd hok.2 hnc hst
            rwa [raIdx_other hi1 hi2, show rdCrc c' r = r.crc by simp [rdCrc, hT]] at this
          wp_apply wp_LastCRC dec IoE eof (fsD.drop k) off' c' true $$ Hdec as Hdec
          wp_if_destruct
          · -- the chain's CRC is zero: not checked
            have hnc : ¬ (r.typ = crcType ∧ crcRecBad (W32 0) r) := fun h => h.2.1 rfl
            wp_apply wp_GetCrc $$ Hr as Hr
            wp_apply wp_UpdateCRC dec IoE eof (fsD.drop k) off' _ r.crc true $$ [Hdec] as Hdec
            · iframe Hdec Hcrc
            wp_for_post
            wp_apply (wp_Decode walCodec dec «$r0_ptr» IoE eof ueof (fsD.drop k) off' r.crc rfl)
              $$ [Hdec Hr] as %e' Hpost
            · iframe Hdec Hdenv; iapply ownRec_any $$ Hr
            iframe
            iexists acc ++ [r], fsD.drop k, kD + k, off', r.crc, st, ix, e', mdv, stp, entsv, esL
            iframe
            ipureintro
            exact ⟨hL' hnc, by rw [hkD, List.drop_drop], hmdn, hmdd⟩
          · -- checked
            ihave #Hde := Hdenv
            iunfold decEnv at Hde
            icases Hde with ⟨-, -, #Hfmt, -, -, #Heof, -, -, -, ⟨%ecm, #Hcm, #Hcmok, #Hcmnot⟩, -⟩
            wp_apply wp_Validate «$r0_ptr» r c' ecm _ eof $$ [Hr] as %verr ⟨Hr, Hv⟩
            · iframe Hr; iframe #
            icases Hv with (⟨%hv1, %hv2⟩ | ⟨%hne, %ei, %hei, -, -⟩)
            · subst hv1
              have hnc : ¬ (r.typ = crcType ∧ crcRecBad c' r) := fun h => h.2.2 hv2
              wp_auto
              wp_apply wp_GetCrc $$ Hr as Hr
              wp_apply wp_UpdateCRC dec IoE eof (fsD.drop k) off' _ r.crc true $$ [Hdec] as Hdec
              · iframe Hdec Hcrc
              wp_for_post
              wp_apply (wp_Decode walCodec dec «$r0_ptr» IoE eof ueof (fsD.drop k) off' r.crc rfl)
                $$ [Hdec Hr] as %e' Hpost
              · iframe Hdec Hdenv; iapply ownRec_any $$ Hr
              iframe
              iexists acc ++ [r], fsD.drop k, kD + k, off', r.crc, st, ix, e', mdv, stp, entsv, esL
              iframe
              ipureintro
              exact ⟨hL' hnc, by rw [hkD, List.drop_drop], hmdn, hmdd⟩
            · subst hei
              wp_auto
              wp_apply hHs.reset stp st.hs $$ Hhs as Hhs
              ihave #Hwi : (wal.walInit : IProp GF) $$ []
              · iapply isPkgInit_access $$ Hpkg
              iunfold wal.walInit at Hwi
              icases Hwi with ⟨-, -, -, -, -, -, #HeX, -⟩
              iunfold wal.errVar at HeX
              icases HeX with ⟨%eX, #HeX, -⟩
              wp_auto
              wp_for_post
              iapply readAll_failWp walCodec Mr R jr rt w dir s _ Q _ _ rfl $$ Hinv Hgh Hau
              iintro %dq HQ Hfail
              wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hlocked]
              · ipureintro; trivial
              iapply HΦ
              iframe Hp Hperm
              iexists dq
              iframe HQ
              ileft
              isplitr
              · ipureintro; simp
              unfold walReadFailedF
              iframe Hfail
              iexists lg
              iframe Hlg Hdir Hzap
        wp_if_destruct
        · -- SnapshotType
          have hT : r.typ = snapshotType := Hif
          have hnc : ¬ (r.typ = crcType ∧ crcRecBad c' r) := by
            rw [hT]; simp [snapshotType, crcType]
          obtain ⟨p, hp⟩ := (hdec0 hnc).1.2.2 hT
          unfold ownRec
          icases Hr with ⟨%v, Hl, Ht, Hc, Hd⟩
          wp_auto
          wp_apply wp_UnmarshalSnap snap_ptr v.Data' _ r.data p hp $$ [snap Hd] as ⟨Hd, #Hsn⟩
          · iframe
          wp_apply wp_SnapIndex snap_ptr p $$ Hsn
          wp_join iprop(w_ptr ↦ w ∗ structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"snapi" w ↦
              (if uint.nat ix.2 < uint.nat p.1 then p.1 else ix.2)) with [w Hsnapi] as ⟨w, Hsnapi⟩
          · wp_apply wp_SnapIndex snap_ptr p $$ Hsn
            (try wp_auto)
            have hc : uint.nat ix.2 < uint.nat p.1 := by word
            simp only [hc, ↓reduceIte]
            wp_join_done
          · have hc : ¬ uint.nat ix.2 < uint.nat p.1 := by word
            simp only [hc, ↓reduceIte]
            iframe
          have hi1 : r.typ ≠ entryType := by rw [hT]; simp [snapshotType, entryType]
          have hi3 : r.typ ≠ crcType := by rw [hT]; simp [snapshotType, crcType]
          wp_apply wp_SnapIndex snap_ptr p $$ Hsn
          wp_apply wp_SnapIndex sp s $$ Hsp
          wp_if_destruct
          · -- the start's snapshot
            have hps : p.1 = s.1 := Hif
            wp_apply wp_SnapTerm snap_ptr p $$ Hsn
            wp_apply wp_SnapTerm sp s $$ Hsp
            wp_if_destruct
            · -- matched
              have hpt : p.2 = s.2 := Hif
              (try wp_auto)
              wp_join iprop(∃ (ev : GoSlice) (eL : List Loc), ents_ptr ↦ ev ∗ ev ↦* eL ∗
                  ownSliceCap Loc ev (DFrac.own 1) ∗
                  walEntsIn P eL (if uint.nat st.hs.Commit' < uint.nat p.1 then [] else st.ents) ∗
                  HsO stp st.hs ∗ state_ptr ↦ stp)
                at next with [ents Hents Hecap Hein Hhs state]
                as ⟨%ev, %eL, ents, Hents, Hecap, Hein, Hhs, state⟩
              · (try wp_auto)
                wp_apply wp_SnapIndex snap_ptr p $$ Hsn
                wp_apply hHs.getCommit stp st.hs $$ Hhs as Hhs
                ihave %hcS := ownSliceCap_wf (GF := GF) (V := Loc) entsv _ $$ Hecap
                wp_if_destruct
                · have hc : uint.nat st.hs.Commit' < uint.nat p.1 := by word
                  have hb : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧
                      sint.Z (W64 0) ≤ sint.Z entsv.cap) := by
                    refine ⟨by decide, Int.le_refl _, ?_⟩
                    have : sint.Z (W64 0) = 0 := rfl
                    omega
                  simp only [hb]
                  icases ownSlice_slice_with_cap (W64 0) (W64 0) entsv esL ⟨by decide, Int.le_refl _, by
                      have : sint.Z (W64 0) = 0 := rfl
                      omega⟩ $$ [Hents Hecap] with ⟨-, Hents, Hecap⟩
                  · iframe
                  rw [show subslice (sint.nat (W64 0)) (sint.nat (W64 0)) esL = [] by simp [subslice]]
                  (try wp_auto)
                  wp_join_done
                  iexists _, []
                  simp only [hc, ↓reduceIte]
                  iframe
                  simp only [walEntsIn]; iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro
                · have hc : ¬ uint.nat st.hs.Commit' < uint.nat p.1 := by word
                  (try wp_auto)
                  wp_join_done
                  iexists entsv, esL
                  simp only [hc, ↓reduceIte]
                  iframe
              wp_apply wp_SnapIndex snap_ptr p $$ Hsn
              wp_join iprop(w_ptr ↦ w ∗ structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"enti" w ↦
                  (if uint.nat ix.1 < uint.nat p.1 then p.1 else ix.1)) with [w Henti] as ⟨w, Henti⟩
              · wp_apply wp_SnapIndex snap_ptr p $$ Hsn
                (try wp_auto)
                have hc : uint.nat ix.1 < uint.nat p.1 := by word
                simp only [hc, ↓reduceIte]
                wp_join_done
              · have hc : ¬ uint.nat ix.1 < uint.nat p.1 := by word
                simp only [hc, ↓reduceIte]
                iframe
              have hst : raStep U s st (r.typ, r.data) =
                  .ok { st with matched := true,
                                ents := if uint.nat st.hs.Commit' < uint.nat p.1 then [] else st.ents } := by
                simp [raStep, hT, hp, hps, hpt, snapshotType, entryType, stateType, metadataType, crcType]
              have hix : raIdx U s ix r = ((if uint.nat ix.1 < uint.nat p.1 then p.1 else ix.1),
                  if uint.nat ix.2 < uint.nat p.1 then p.1 else ix.2) := by
                simp [raIdx, hT, hp, hps, snapshotType, entryType]
              have hL' := rdLoop_next hL hgd hok.2 hnc hst
              rw [hix, rdCrc_other hi3] at hL'
              (try wp_auto)
              wp_for_post
              wp_apply (wp_Decode walCodec dec «$r0_ptr» IoE eof ueof (fsD.drop k) off' c' rfl)
                $$ [Hdec Hl] as %e' Hpost
              · iframe Hdec Hdenv; unfold ownRecAny; iexists v; iexact Hl
              iframe
              iexists acc ++ [r], fsD.drop k, kD + k, off', c',
                { st with matched := true,
                          ents := if uint.nat st.hs.Commit' < uint.nat p.1 then [] else st.ents },
                ((if uint.nat ix.1 < uint.nat p.1 then p.1 else ix.1),
                  if uint.nat ix.2 < uint.nat p.1 then p.1 else ix.2), e', mdv, stp, ev, eL
              iframe
              ipureintro
              exact ⟨hL', by rw [hkD, List.drop_drop], hmdn, hmdd⟩
            · -- `ErrSnapshotMismatch`
              (try wp_auto)
              wp_apply hHs.reset stp st.hs $$ Hhs as Hhs
              ihave #Hwi : (wal.walInit : IProp GF) $$ []
              · iapply isPkgInit_access $$ Hpkg
              iunfold wal.walInit at Hwi
              icases Hwi with ⟨-, -, -, -, -, -, -, #HeX, -⟩
              iunfold wal.errVar at HeX
              icases HeX with ⟨%eX, #HeX, -⟩
              (try wp_auto)
              wp_for_post
              iapply readAll_failWp walCodec Mr R jr rt w dir s _ Q _ _ rfl $$ Hinv Hgh Hau
              iintro %dq HQ Hfail
              wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hlocked]
              · ipureintro; trivial
              iapply HΦ
              iframe Hp Hperm
              iexists dq
              iframe HQ
              ileft
              isplitr
              · ipureintro; simp
              unfold walReadFailedF
              iframe Hfail
              iexists lg
              iframe Hlg Hdir Hzap
          · -- another snapshot: nothing but `w.snapi`
            have hps : p.1 ≠ s.1 := Hif
            have hst : raStep U s st (r.typ, r.data) = .ok st := by
              simp [raStep, hT, hp, hps, snapshotType, entryType, stateType, metadataType, crcType]
            have hix : raIdx U s ix r = (ix.1, if uint.nat ix.2 < uint.nat p.1 then p.1 else ix.2) := by
              simp [raIdx, hT, hp, hps, snapshotType, entryType]
            have hL' := rdLoop_next hL hgd hok.2 hnc hst
            rw [hix, rdCrc_other hi3] at hL'
            (try wp_auto)
            wp_for_post
            wp_apply (wp_Decode walCodec dec «$r0_ptr» IoE eof ueof (fsD.drop k) off' c' rfl)
              $$ [Hdec Hl] as %e' Hpost
            · iframe Hdec Hdenv; unfold ownRecAny; iexists v; iexact Hl
            iframe
            iexists acc ++ [r], fsD.drop k, kD + k, off', c', st, (ix.1, if uint.nat ix.2 < uint.nat p.1 then p.1 else ix.2),
              e', mdv, stp, entsv, esL
            iframe
            ipureintro
            exact ⟨hL', by rw [hkD, List.drop_drop], hmdn, hmdd⟩
        · -- the default arm: `unexpected block type`
          (try wp_auto)
          wp_apply hHs.reset stp st.hs $$ Hhs as Hhs
          (try wp_auto)
          wp_apply wp_GetType $$ Hr as Hr
          (try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %asl ⟨Hasl, -⟩
          wp_apply wp_Errorf _ _ [interface.mkOk go.int64 #r.typ] [] (by
              intro ii hii
              left
              simp only [List.mem_cons, List.not_mem_nil, or_false, interface.mkOk] at hii
              cases hii
              exact argWf_int64 _) $$ [Hasl] as %e1 #He1
          · iframe
            try simp only [BigSepL.bigSepL_nil]
            iempintro
          (try wp_auto)
          wp_for_post
          iapply readAll_failWp walCodec Mr R jr rt w dir s _ Q _ _ rfl $$ Hinv Hgh Hau
          iintro %dq HQ Hfail
          wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hlocked]
          · ipureintro; trivial
          iapply HΦ
          iframe Hp Hperm
          iexists dq
          iframe HQ
          ileft
          isplitr
          · ipureintro; simp
          unfold walReadFailedF
          iframe Hfail
          iexists lg
          iframe Hlg Hdir Hzap
      · icases Hm with ⟨%hst, -, -⟩
        exact absurd hst.1 (stopErr_nil hnn.1 hnn.2 sx)
    · exact absurd hio hIoN
    · exact absurd hgf.2 (stopErr_nil hnn.1 hnn.2 sx)

end proof

end EtcdGrove
end Perennial
