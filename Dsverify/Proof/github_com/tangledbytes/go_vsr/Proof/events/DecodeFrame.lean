/-
`dec.Decode(&f)` into a `vsrwire.Frame` on a decoder of `γ`'s stream (`events.rstream`), at the
model's decoder representation (`encoding.json.decRepModel`): the model's `Decode`
(`models/encoding/json/v2_stream.go`) returns a sticky error again; else `readValue` reads the
next value with the registered codec's `Scan` (`jsoncodec.Scan`, `scanOk JsonScan.scanF`): the
framing (`jsonstream.scan_next`, `Frame.lean`) says the unread bytes are a line's value or ask for
more, which `fetch` reads from the connection (`Decoder.fetch_conn.spec`); a read error is kept;
the value, `encEvent m` after whitespace, is decoded by the frame's `JSONModelUnmarshal`
(`unmarshalAt`, valid by `vsrnet.encEvent_valid`, into `Frame{typeOf m, data}` by
`vsrnet.dec_frame`). Lean-first (the lab's `jsonstream.wp_Decode_frame` was over its own model).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.events.Frame
public import Spec.encoding.json.Codec.Decoder__fetch_conn
public import Spec.encoding.json.Codec.getCodec
public import Spec.encoding.json.Codec.skipSpace
public import Spec.encoding.json.Codec.endsInNumber
public import Spec.encoding.json.Codec.NewDecoder
public import Proof.encoding.json.DecoderModel
public import Proof.encoding.json.NetInit

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

set_option warn.classDefReducibility false in
attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : events.Assumptions] [log.Assumptions] [examples.vsrwire.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.Assumptions] [models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true

/-- `slice.slice s lo hi` holding a non-empty list, as the full slice `s[lo:hi:hi]` (the
ownership is the same: same pointer and length). -/
theorem jsonstream.ownSlice_fullSlice_iff {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s : GoSlice) (dq : DFrac) (vs : List V) (lo hi : w64) (hne : vs ≠ [])
    (hb : 0 ≤ sint.Z lo ∧ sint.Z lo ≤ sint.Z hi ∧ sint.Z hi ≤ sint.Z s.cap) :
    (slice.slice s V lo hi ↦*{dq} vs : IProp GF) ⊣⊢ slice.fullSlice s V lo hi hi ↦*{dq} vs := by
  have hp : (slice.fullSlice s V lo hi hi).ptr = (slice.slice s V lo hi).ptr := rfl
  have hl : (slice.fullSlice s V lo hi hi).len = (slice.slice s V lo hi).len := rfl
  rw [ownSlice_unseal]; unfold ownSliceDef
  constructor
  · iintro (%H | ⟨H, %_⟩)
    · exact absurd H.2 hne
    · iright
      rw [hp, hl]
      iframe H
      ipureintro
      simp only [slice.slice, slice.fullSlice]
      exact Int.le_refl _
  · iintro (%H | ⟨H, %_⟩)
    · exact absurd H.2 hne
    · iright
      rw [← hp, ← hl]
      iframe H
      ipureintro
      simp only [slice.slice, slice.fullSlice]
      word

/-- `io.EOF` and `io.ErrUnexpectedEOF`, from `net`'s initialization. -/
theorem jsonstream.ioErrs_of_net :
    isPkgInit (PROP := IProp GF) pkg_id.net ⊢
      _root_.Perennial.errors.newVar (GF := GF) _root_.Perennial.io.EOF go!"EOF" ∗
      _root_.Perennial.errors.newVar (GF := GF) _root_.Perennial.io.ErrUnexpectedEOF
        go!"unexpected EOF" := by
  iintro #Hnet
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, #HEOF, #HUE, -⟩
  isplitl []
  · iexact HEOF
  · iexact HUE

/-- An `errors.New` variable: its value, an `*errorString` (not nil), and an error with a
message (`errOrNil`). -/
theorem jsonstream.newVar_errOrNil (X msg : GoString) :
    _root_.Perennial.errors.newVar (GF := GF) X msg ⊢
      ∃ x : Loc, globalAddr X ↦□
          interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x ∗
        bufio.errOrNil (interface.mkOk
          (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) := by
  unfold _root_.Perennial.errors.newVar
  iintro ⟨%x, #Hx, -, #HE⟩
  iexists x
  iframe Hx
  unfold bufio.errOrNil models_lab.errAny
  iright
  isplitl []
  · iexists ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; go_type_set
    imodintro
    iintro %Φ HΦ
    iapply HE
    inext
    iapply HΦ
  · ipureintro
    intro e he T hT
    cases he
    exact ⟨x, rfl⟩

open examples in
/-- `dec.readValue(c)` on a healthy decoder of `γ`'s stream (see the file header): the next
line's value `encEvent m` in a slice of the buffer, with the way back to a healthy decoder past
it; or an error, the decoder's sticky error still nil. -/
theorem jsonstream.wp_readValue
    (wp_skipSpace : encoding.json.skipSpace.spec (GF := GF) (hG := hG))
    (wp_endsInNumber : encoding.json.endsInNumber.spec (GF := GF) (hG := hG))
    (wp_fetch : encoding.json.Decoder.fetch_conn.spec (GF := GF) (hG := hG))
    (γ : VsrGhost.Names) (dec cd : Loc) (fm fu : GoFunc) (d : encoding.json.Decoder)
    (bs pre R : List w8) (cn : Nat) (s : Bool) (a : GoString) (ms : List Msg) (pend : Option Msg)
    (hd : d.err' = interface.nil) (hok : encoding.json.decBufOk d bs) (hR : R = pre ++ bs)
    (hst : events.rstreamAt ms pend (bs.drop (sint.nat d.prevEnd')) R) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ isPkgInit (PROP := IProp GF) pkg_id.net ∗
      net.isConn d.r' cn s a ∗ encoding.json.codecFnsWith fm fu cd ∗
      models_lab.jsoncodec.scanOk JsonScan.scanF models_lab.jsoncodec.scanFn ∗
      dec ↦ d ∗ d.buf' ↦* bs ∗ ownSliceCap w8 d.buf' (DFrac.own 1) ∗
      recvTok (Gg := hG.goose_globalGS) cn s (VsrWire.protoOf γ) R }}
    (App (Val (dec @!! go.GoType.PointerType encoding.json.Decoder.ty @!! go!"readValue"))
      (Val #cd))
  {{ (b : GoSlice) (err : GoInterface), RET (PairV #b #err);
      (⌜err = interface.nil⌝ ∗ ∃ (m : Msg) (R' z : List w8) (ms' : List Msg) (pend' : Option Msg),
        b ↦* VsrWire.encEvent m ∗
        (b ↦* VsrWire.encEvent m -∗ encoding.json.decOkModel dec d.r'
          (recvTok (Gg := hG.goose_globalGS) cn s (VsrWire.protoOf γ)) R' z) ∗
        ⌜events.rstreamAt ms' pend' z R' ∧ PlainMsg m ∧ MsgBound m⌝ ∗ VsrGhost.fact γ (.msg m)) ∨
      (⌜err ≠ interface.nil⌝ ∗ bufio.errOrNil err ∗ ∃ d' : encoding.json.Decoder, dec ↦ d' ∗
        ⌜d'.r' = d.r' ∧ d'.err' = interface.nil⌝) }} := by
  wp_start as ⟨#Hc, #Hfns, #Hscan, Hd, Hb, Hcap, Htok⟩
  wp_auto
  unfold encoding.json.codecFnsWith
  icases Hfns with ⟨-, -, #HfS⟩
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  obtain ⟨hps0, hpse, hpel, hcap3⟩ := hok
  -- `prevStart = prevEnd`
  wp_join iprop(dec_ptr ↦ dec ∗ dec ↦ { d with prevStart' := d.prevEnd' }) with [dec Hd]
    as ⟨dec, Hd⟩
  · have he : d.prevStart' = d.prevEnd' := by
      have : ¬ sint.Z d.prevStart' < sint.Z d.prevEnd' := Hif
      word
    have hdd : ({ d with prevStart' := d.prevEnd' } : encoding.json.Decoder) = d := by
      cases d; simp only at he ⊢; rw [he]
    rw [hdd]
    iframe
  unfold models_lab.jsoncodec.scanOk
  icases Hscan with ⟨%HscanLen, #HscanW⟩
  ihave HI : (∃ (d1 : encoding.json.Decoder) (bs1 pre1 R1 : List w8) (eof : Bool) (ms1 : List Msg)
      (pend1 : Option Msg),
      "Hd" ∷ dec ↦ d1 ∗ "Hb" ∷ d1.buf' ↦* bs1 ∗ "Hcap" ∷ ownSliceCap w8 d1.buf' (DFrac.own 1) ∗
      "Htok" ∷ recvTok (Gg := hG.goose_globalGS) cn s (VsrWire.protoOf γ) R1 ∗
      "pos" ∷ pos_ptr ↦ d1.prevEnd' ∗ "eof" ∷ eof_ptr ↦ eof ∗
      "Hdead" ∷ (if eof then readDead (Gg := hG.goose_globalGS) cn s else True) ∗
      "%Hinv" ∷ ⌜d1.r' = d.r' ∧ d1.err' = interface.nil ∧ R1 = pre1 ++ bs1 ∧
        encoding.json.decBufOk d1 bs1 ∧ d1.prevStart' = d1.prevEnd' ∧
        events.rstreamAt ms1 pend1 (bs1.drop (sint.nat d1.prevEnd')) R1⌝ : IProp GF)
    $$ [Hd Hb Hcap Htok pos eof]
  · iexists { d with prevStart' := d.prevEnd' }, bs, pre, R, false, ms, pend
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
    isplitl []
    · itrivial
    ipureintro
    exact ⟨trivial, hd, hR, ⟨Int.le_trans hps0 hpse, Int.le_refl _, hpel, hcap3⟩, trivial, hst⟩
  wp_for HI
  ihave %Hbl1 := ownSlice_len _ _ _ $$ Hb
  ihave %Hcw1 := ownSliceCap_wf _ _ $$ Hcap
  obtain ⟨Hr1, Herr1, HR1, ⟨hq0, hq1, hq2, hq3⟩, Hse, Hst1⟩ := Hinv
  have hpl : sint.Z d1.prevEnd' ≤ sint.Z d1.buf'.len := by
    have : (bs1.length : Int) = sint.Z d1.buf'.len := by rw [Hbl1.1]; word
    omega
  have hp0 : 0 ≤ sint.Z d1.prevEnd' := Int.le_trans hq0 hq1
  ihave ⟨Htok, #Hpp⟩ := recvTok_proto _ _ _ _ $$ Htok
  ihave Hsn := jsonstream.scan_next γ cn R1 _ ms1 pend1 eof Hst1 $$ Hpp
  have hsb : 0 ≤ sint.Z d1.prevEnd' ∧ sint.Z d1.prevEnd' ≤ sint.Z d1.buf'.len ∧
      sint.Z d1.buf'.len ≤ sint.Z d1.buf'.cap := ⟨hp0, hpl, Hcw1.2⟩
  rw [ite_eq_left hsb]
  icases (ownSlice_split_all d1.prevEnd' d1.buf' _ bs1 ⟨hp0, hpl⟩).1 $$ Hb with ⟨Hb0, Hrest⟩
  wp_auto
  wp_apply HscanW $$ Hrest
  iintro Hrest
  wp_auto
  icases Hsn with (⟨%hmore, %hUl⟩ | ⟨%m, %ws, %z, %ms', %pend', %hfacts, #Hfact⟩)
  rotate_left
  · -- the scanner found the next value
    obtain ⟨hU, hws, hm, hsc, hst', hmb⟩ := hfacts
    have hsc' := hsc
    simp only [vsrnet.scanF, JsonScan.scanF, Prod.mk.injEq] at hsc'
    obtain ⟨h1, h2⟩ := hsc'
    rw [h1, h2]
    wp_auto
    rw [ite_eq_left hsb]
    wp_apply wp_skipSpace $$ Hrest as Hrest
    have hlenU : ws.length + (VsrWire.encEvent m).length + z.length =
        bs1.length - sint.nat d1.prevEnd' := by
      rw [← List.length_drop, hU]; simp; omega
    have hbl : (bs1.length : Int) = sint.Z d1.buf'.len := by rw [Hbl1.1]; word
    have hpn : (sint.nat d1.prevEnd' : Int) = sint.Z d1.prevEnd' := by
      rw [show sint.nat d1.prevEnd' = (sint.Z d1.prevEnd').toNat from rfl]; omega
    have hS : sint.Z (d1.prevEnd' + W64 ws.length) = sint.Z d1.prevEnd' + ws.length := by
      have hk : ws.length ≤ bs1.length - sint.nat d1.prevEnd' := by omega
      generalize ws.length = k at hk ⊢
      word
    have hE : sint.Z (d1.prevEnd' + W64 (ws.length + (VsrWire.encEvent m).length)) =
        sint.Z d1.prevEnd' + ws.length + (VsrWire.encEvent m).length := by word
    rw [hU, jsonstream.leadSpace_line ws z m hws hm]
    have hfb : 0 ≤ sint.Z (d1.prevEnd' + W64 ws.length) ∧
        sint.Z (d1.prevEnd' + W64 ws.length) ≤
          sint.Z (d1.prevEnd' + W64 (ws.length + (VsrWire.encEvent m).length)) ∧
        sint.Z (d1.prevEnd' + W64 (ws.length + (VsrWire.encEvent m).length)) ≤
          sint.Z (d1.prevEnd' + W64 (ws.length + (VsrWire.encEvent m).length)) ∧
        sint.Z (d1.prevEnd' + W64 (ws.length + (VsrWire.encEvent m).length)) ≤
          sint.Z d1.buf'.cap := by
      rw [hS, hE]; omega
    rw [ite_eq_left hfb]
    wp_auto
    wp_for_post
    -- the value's bytes, `buf[start:end]`
    have hnat : ∀ x : w64, sint.nat x = (sint.Z x).toNat := fun _ => rfl
    have hsn : sint.nat (d1.prevEnd' + W64 ws.length) - sint.nat d1.prevEnd' = ws.length := by
      rw [hnat, hnat, hS]; omega
    have hen : sint.nat (d1.prevEnd' + W64 (ws.length + (VsrWire.encEvent m).length)) -
        sint.nat (d1.prevEnd' + W64 ws.length) = (VsrWire.encEvent m).length := by
      rw [hnat, hnat, hS, hE]; omega
    have hb1 : 0 ≤ sint.Z d1.prevEnd' ∧ sint.Z d1.prevEnd' ≤ sint.Z (d1.prevEnd' + W64 ws.length) ∧
        sint.Z (d1.prevEnd' + W64 ws.length) ≤ sint.Z d1.buf'.len := by rw [hS]; omega
    have hb2 : 0 ≤ sint.Z (d1.prevEnd' + W64 ws.length) ∧
        sint.Z (d1.prevEnd' + W64 ws.length) ≤
          sint.Z (d1.prevEnd' + W64 (ws.length + (VsrWire.encEvent m).length)) ∧
        sint.Z (d1.prevEnd' + W64 (ws.length + (VsrWire.encEvent m).length)) ≤ sint.Z d1.buf'.len := by
      rw [hS, hE]; omega
    icases (ownSlice_split (d1.prevEnd' + W64 ws.length) d1.buf' _ _ d1.prevEnd' d1.buf'.len hb1).1
      $$ Hrest with ⟨Hws, Hrest⟩
    rw [hsn]
    have e1 : List.take ws.length (ws ++ VsrWire.encEvent m ++ z) = ws := by simp
    have e2 : List.drop ws.length (ws ++ VsrWire.encEvent m ++ z) = VsrWire.encEvent m ++ z := by
      simp
    rw [e1, e2]
    icases (ownSlice_split (d1.prevEnd' + W64 (ws.length + (VsrWire.encEvent m).length)) d1.buf' _ _
      (d1.prevEnd' + W64 ws.length) d1.buf'.len hb2).1 $$ Hrest with ⟨Henc, Hz⟩
    rw [hen]
    have e3 : List.take (VsrWire.encEvent m).length (VsrWire.encEvent m ++ z) = VsrWire.encEvent m := by
      simp
    have e4 : List.drop (VsrWire.encEvent m).length (VsrWire.encEvent m ++ z) = z := by simp
    rw [e3, e4]
    have hne : VsrWire.encEvent m ≠ [] := by
      simp only [VsrWire.encEvent, VsrJson.encEvent, hm, ↓reduceIte, VsrJson.evJV, VsrJson.ser]
      simp
    icases (jsonstream.ownSlice_fullSlice_iff d1.buf' _ _ _ _ hne ⟨hfb.1, hfb.2.1, hfb.2.2.2⟩).1
      $$ Henc with Henc
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists m, R1, z, ms', pend'
    iframe Henc Hfact
    isplitl [Hd Hb0 Hws Hz Hcap Htok]
    · iintro Henc
      icases (jsonstream.ownSlice_fullSlice_iff d1.buf' _ _ _ _ hne ⟨hfb.1, hfb.2.1, hfb.2.2.2⟩).2
        $$ Henc with Henc
      ihave Hez := ownSlice_combine (d1.prevEnd' + W64 (ws.length + (VsrWire.encEvent m).length))
        d1.buf' _ _ z (d1.prevEnd' + W64 ws.length) d1.buf'.len ⟨hen.symm, hb2⟩ $$ Henc Hz
      ihave Hall := ownSlice_combine (d1.prevEnd' + W64 ws.length) d1.buf' _ ws _ d1.prevEnd'
        d1.buf'.len ⟨hsn.symm, hb1⟩ $$ Hws Hez
      rw [show ws ++ (VsrWire.encEvent m ++ z) = List.drop (sint.nat d1.prevEnd') bs1 by
        rw [hU, List.append_assoc]]
      ihave Hb := (ownSlice_split_all d1.prevEnd' d1.buf' _ bs1 ⟨hp0, hpl⟩).2 $$ [Hb0 Hall]
      · iframe
      unfold encoding.json.decOkModel
      iexists ({ d1 with
                  prevStart' := d1.prevEnd' + W64 ws.length
                  prevEnd' := d1.prevEnd' + W64 (ws.length + (VsrWire.encEvent m).length) } :
        encoding.json.Decoder), bs1, pre1
      iframe Hd Hb Hcap Htok
      ipureintro
      refine ⟨Hr1, Herr1, HR1, ⟨hfb.1, hfb.2.1, by rw [hE]; omega, hq3⟩, ?_⟩
      have hen2 : sint.nat (d1.prevEnd' + W64 (ws.length + (VsrWire.encEvent m).length)) =
          sint.nat d1.prevEnd' + (ws.length + (VsrWire.encEvent m).length) := by
        rw [hnat, hnat, hE]; omega
      rw [hen2, ← List.drop_drop, hU]
      simp
    ipureintro
    exact ⟨hst', hm, hmb⟩
  -- the scanner asks for more
  have hm1 := hmore
  simp only [vsrnet.scanF, JsonScan.scanF] at hm1
  rw [hm1]
  wp_auto
  ihave ⟨#HEOFv, #HUEv⟩ := jsonstream.ioErrs_of_net $$ Hpkg2
  ihave ⟨%xe, #HEOFa, #HEOFe⟩ := jsonstream.newVar_errOrNil _ _ $$ HEOFv
  ihave ⟨%xu, #HUEa, #HUEe⟩ := jsonstream.newVar_errOrNil _ _ $$ HUEv
  have hUlen : (List.drop (sint.nat d1.prevEnd') bs1).length = bs1.length - sint.nat d1.prevEnd' :=
    List.length_drop
  have hbl : (bs1.length : Int) = sint.Z d1.buf'.len := by rw [Hbl1.1]; word
  have hpn : (sint.nat d1.prevEnd' : Int) = sint.Z d1.prevEnd' := by
    rw [show sint.nat d1.prevEnd' = (sint.Z d1.prevEnd').toNat from rfl]; omega
  have hkept : bs1.length - sint.nat d1.prevStart' < 2 ^ 60 := by rw [Hse]; omega
  cases eof
  · -- not at the end of the stream: fetch more
    wp_auto
    ihave Hb := (ownSlice_split_all d1.prevEnd' d1.buf' _ bs1 ⟨hp0, hpl⟩).2 $$ [Hb0 Hrest]
    · iframe
    wp_apply wp_fetch dec d1 bs1 cn s a (VsrWire.protoOf γ) R1 false
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #xu)
      ⟨hq0, hq1, hq2, hq3⟩ hkept $$ [Hd Hb Hcap Htok Hdead]
    · rw [Hr1]
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
      isplitr; · iexact HUEa
      iexact Hc
    iintro %err ⟨%d2, %ys, Hd, Hb, Hcap, Htok, %Hf, Hres⟩
    obtain ⟨Hf1, Hf2, Hf3, Hf4, Hf5, Hf6⟩ := Hf
    have hpos : d1.baseOffset' + d1.prevEnd' - d2.baseOffset' = d2.prevEnd' := by
      rw [Hf5, Hf4, Hse]; bv_omega
    have h00 : sint.Z (W64 0) = 0 := rfl
    have hz2 : d2.prevEnd' = W64 0 := by rw [Hf4, Hse]; simp
    unfold encoding.json.fetchRes
    icases Hres with (%Hres | ⟨%Hres, #Hdead⟩ | ⟨%Hres, #Herr⟩)
    · obtain ⟨rfl, hys, -⟩ := Hres
      wp_auto
      wp_for_post
      rw [hpos]
      iframe
      iexists d2, List.drop (sint.nat d1.prevStart') bs1 ++ ys,
        pre1 ++ List.take (sint.nat d1.prevStart') bs1, R1 ++ ys, false, ms1, pend1
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
      ipureintro
      refine ⟨trivial, Hf1.trans Hr1, Hf2.trans Herr1, ?_, ?_, by rw [Hf3, hz2]; rfl, ?_⟩
      · rw [HR1]
        conv => rhs; rw [List.append_assoc, ← List.append_assoc (List.take _ _), List.take_append_drop]
        rw [List.append_assoc]
      · unfold encoding.json.decBufOk
        rw [Hf3, hz2, h00]
        exact ⟨Int.le_refl _, Int.le_refl _, Int.natCast_nonneg _, Hf6⟩
      · rw [hz2, show sint.nat (W64 0) = 0 from rfl, List.drop_zero, Hse]
        exact jsonstream.rstreamAt_append _ _ _ _ _ Hst1
    · obtain ⟨rfl, rfl⟩ := Hres
      wp_auto
      wp_for_post
      rw [hpos]
      iframe
      iexists d2, List.drop (sint.nat d1.prevStart') bs1 ++ [],
        pre1 ++ List.take (sint.nat d1.prevStart') bs1, R1 ++ [], true, ms1, pend1
      simp only [↓reduceIte]
      iframe
      isplitr; · iexact Hdead
      ipureintro
      refine ⟨Hf1.trans Hr1, Hf2.trans Herr1, ?_, ?_, by rw [Hf3, hz2]; rfl, ?_⟩
      · rw [HR1]
        conv => rhs; rw [List.append_assoc, ← List.append_assoc (List.take _ _), List.take_append_drop]
        rw [List.append_assoc]
      · unfold encoding.json.decBufOk
        rw [Hf3, hz2, h00]
        exact ⟨Int.le_refl _, Int.le_refl _, Int.natCast_nonneg _, Hf6⟩
      · rw [hz2, show sint.nat (W64 0) = 0 from rfl, List.drop_zero, Hse]
        exact jsonstream.rstreamAt_append _ _ _ _ _ Hst1
    · obtain ⟨rfl, pe, rfl⟩ := Hres
      wp_auto
      wp_for_post
      iapply HΦ
      iright
      isplitr
      · ipureintro; intro h; cases h
      iframe Herr
      iexists d2
      iframe Hd
      ipureintro; exact ⟨Hf1.trans Hr1, Hf2.trans Herr1⟩
  · -- at the end of the stream
    wp_auto
    rw [ite_eq_left hsb]
    wp_apply wp_skipSpace $$ Hrest as Hrest
    wp_if_destruct
    · -- only whitespace left: `io.EOF`
      wp_for_post
      iapply HΦ
      iright
      isplitr
      · ipureintro; intro h; cases h
      iframe HEOFe
      iexists d1
      iframe Hd
      ipureintro; exact ⟨Hr1, Herr1⟩
    rw [ite_eq_left hsb]
    have h62 : sint.Z (slice.slice d1.buf' w8 d1.prevEnd' d1.buf'.len).len < 2 ^ 62 := by
      simp only [slice.slice]; word
    wp_apply wp_endsInNumber _ _ _ h62 $$ Hrest
    iintro %r Hrest
    ihave Hb := (ownSlice_split_all d1.prevEnd' d1.buf' _ bs1 ⟨hp0, hpl⟩).2 $$ [Hb0 Hrest]
    · iframe
    cases r
    · -- `io.ErrUnexpectedEOF`
      wp_auto
      wp_for_post
      iapply HΦ
      iright
      isplitr
      · ipureintro; intro h; cases h
      iframe HUEe
      iexists d1
      iframe Hd
      ipureintro; exact ⟨Hr1, Herr1⟩
    -- a number at the end: `fetch` again (the stream is dead: an error)
    wp_auto
    wp_apply wp_fetch dec d1 bs1 cn s a (VsrWire.protoOf γ) R1 true
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #xu)
      ⟨hq0, hq1, hq2, hq3⟩ hkept $$ [Hd Hb Hcap Htok Hdead]
    · iframe
      rw [Hr1]
      isplitr; · iexact HUEa
      isplitr; · iexact Hc
      simp only [↓reduceIte]
      iexact Hdead
    iintro %err ⟨%d2, %ys, Hd, Hb, Hcap, Htok, %Hf, Hres⟩
    unfold encoding.json.fetchRes
    icases Hres with (%Hres | ⟨%Hres, #Hdead⟩ | ⟨%Hres, #Herr⟩)
    · exact absurd Hres.2.2 (by simp)
    · obtain ⟨rfl, rfl⟩ := Hres
      wp_auto
      wp_for_post
      iapply HΦ
      iright
      isplitr
      · ipureintro; intro h; cases h
      iframe HUEe
      iexists d2
      iframe Hd
      ipureintro; exact ⟨Hf.1.trans Hr1, Hf.2.1.trans Herr1⟩
    · obtain ⟨rfl, pe, rfl⟩ := Hres
      wp_auto
      wp_for_post
      iapply HΦ
      iright
      isplitr
      · ipureintro; intro h; cases h
      iframe Herr
      iexists d2
      iframe Hd
      ipureintro; exact ⟨Hf.1.trans Hr1, Hf.2.1.trans Herr1⟩

set_option warn.classDefReducibility false in
attribute [local instance] examples.vsrnet.jsonCodec encoding.json.decRepModel in
/-- `events.Decoder.Decode_frame.spec` at the model's decoder (`decRepModel`) and the kit's codec
(`vsrnet.jsonCodec`): see the file header. -/
theorem events.Decoder.Decode_frame.wp_proof
    (wp_getCodec : encoding.json.getCodec.spec (GF := GF) (hG := hG))
    (wp_skipSpace : encoding.json.skipSpace.spec (GF := GF) (hG := hG))
    (wp_endsInNumber : encoding.json.endsInNumber.spec (GF := GF) (hG := hG))
    (wp_fetch : encoding.json.Decoder.fetch_conn.spec (GF := GF) (hG := hG)) :
    events.Decoder.Decode_frame.spec (GF := GF) (hG := hG) := by
  intro γ dec p fr hfr
  wp_start as ⟨#Hset, Hvia, Hrs, Hp⟩
  iunfold events.rstream at Hrs
  icases Hrs with ⟨%c, %cn, %s, %a, #Hc, #Hnet, Hrs⟩
  icases Hrs with (Herr | ⟨%R, %U, %ms, %pend, Hok, %Hst⟩)
  · -- the sticky error, returned again
    ihave Herr : (encoding.json.decErrModel (hG := hG) dec c) $$ [Herr]
    · iexact Herr
    iunfold encoding.json.decErrModel at Herr
    icases Herr with ⟨%d, Hd, %Hd, #He⟩
    obtain ⟨Hdr, Hdne⟩ := Hd
    obtain ⟨i, hi⟩ : ∃ i, d.err' = GoInterface.ok i := by
      cases h : d.err' with
      | nil => exact absurd h Hdne
      | ok i => exact ⟨i, rfl⟩
    wp_auto
    rw [hi]
    wp_auto
    iapply HΦ
    isplitl [Hd]
    · iunfold events.rstream
      iexists c, cn, s, a
      iframe Hc Hnet
      ileft
      ihave H : (encoding.json.decErrModel (hG := hG) dec c) $$ [Hd]
      · iunfold encoding.json.decErrModel
        iexists d
        iframe Hd
        isplitr
        · ipureintro; exact ⟨Hdr, Hdne⟩
        rw [hi]
        iexact He
      iexact H
    have hne : decide (d.err' = GoInterface.nil) = false := decide_eq_false Hdne
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexists fr
    iframe Hp
    rw [hi]
    iexact He
  ihave Hok : (encoding.json.decOkModel (hG := hG) dec c
    (recvTok (Gg := hG.goose_globalGS) cn s (VsrWire.protoOf γ)) R U) $$ [Hok]
  · iexact Hok
  iunfold encoding.json.decOkModel at Hok
  icases Hok with ⟨%d, %bs, %pre, Hd, Hb, Hcap, Htok, %Hd⟩
  obtain ⟨Hdr, Hde, HR, Hbuf, HU⟩ := Hd
  have hT : go.typeSetContains (go.GoType.PointerType examples.vsrwire.Frame.ty)
      encoding.json.modelUnmarshaler.ty = true := by go_type_set
  ihave ⟨#Hscan, Hat⟩ : (models_lab.jsoncodec.scanOk (GF := GF) JsonScan.scanF
      models_lab.jsoncodec.scanFn ∗
    encoding.json.unmarshalAt inferInstance JsonScan.scanF
      #(methods (go.GoType.PointerType examples.vsrwire.Frame.ty) go!"JSONModelUnmarshal" #p)
      (interface.mkOk (go.GoType.PointerType examples.vsrwire.Frame.ty) #p)) $$ [Hvia]
  · simp only [encoding.json.unmarshalVia, interface.mkOk, hT, ↓reduceIte]
    iexact Hvia
  wp_auto
  rw [Hde]
  wp_auto
  iunfold encoding.json.codecSet at Hset
  wp_apply wp_getCodec $$ Hset
  iintro %cd #Hfns
  wp_auto
  have hst : events.rstreamAt ms pend (bs.drop (sint.nat d.prevEnd')) R := HU ▸ Hst
  wp_apply (jsonstream.wp_readValue wp_skipSpace wp_endsInNumber wp_fetch γ dec cd
    (encoding.json.kitFn go!"jsonMarshal") (encoding.json.kitFn go!"jsonUnmarshal") d bs pre R cn s a
    ms pend Hde Hbuf HR hst) $$ [Hd Hb Hcap Htok]
  · rw [Hdr]
    iframe
    isplitr; · iexact Hc
    isplitr; · iexact Hfns
    iexact Hscan
  iintro %b %err Hres
  icases Hres with (⟨%Hen, %m, %R', %z, %ms', %pend', Hbm, Hback, %Hfacts, #Hfact⟩ |
    ⟨%Hne, #He, %d', Hd, %Hd'⟩)
  · subst Hen
    obtain ⟨Hst', hm, hmb⟩ := Hfacts
    wp_auto
    rw [hT]
    wp_auto
    have hdf := examples.vsrnet.dec_frame (GF := GF) [] m p fr (by simp) hm hfr
    simp only [List.nil_append] at hdf
    ihave Hdec := hdf $$ Hp
    unfold encoding.json.unmarshalAt
    wp_bind (App (App (Val #(methods _ _ _)) _) _)
    iapply Hat $$ Hbm Hdec
    inext
    iintro %err Hbm Hres
    ihave %Hbl := ownSlice_len _ _ _ $$ Hbm
    icases Hres with (⟨-, %ok, %Hok, %Hok', %data, Hp, Hdata, -⟩ | ⟨%Hbad, -⟩)
    rotate_left
    · exfalso
      refine Hbad.1 (examples.vsrnet.encEvent_valid [] m (by simp) hm ?_)
      have h63 : sint.Z b.len < 2 ^ 63 := by word
      have : sint.nat b.len < 2 ^ 64 := by
        show (sint.Z b.len).toNat < _
        omega
      simpa [Hbl.1] using this
    subst Hok'
    have he : err = GoInterface.nil := Hok.2 rfl
    subst he
    wp_auto
    iapply HΦ
    isplitl [Hback Hbm]
    · iunfold events.rstream
      iexists c, cn, s, a
      iframe Hc Hnet
      iright
      iexists R', z, ms', pend'
      isplitl
      · ihave H : (encoding.json.decOkModel (hG := hG) dec c
            (recvTok (Gg := hG.goose_globalGS) cn s (VsrWire.protoOf γ)) R' z) $$ [Hback Hbm]
        · rw [← Hdr]
          iapply Hback
          iexact Hbm
        iexact H
      ipureintro; exact Hst'
    simp only [_root_.decide_true, ↓reduceIte]
    iexists m, data
    iframe Hp Hdata Hfact
    ipureintro; exact ⟨hm, hmb⟩
  · obtain ⟨i, hi⟩ : ∃ i, err = GoInterface.ok i := by
      cases h : err with
      | nil => exact absurd h Hne
      | ok i => exact ⟨i, rfl⟩
    subst hi
    wp_auto
    iapply HΦ
    isplitl [Hd]
    · iunfold events.rstream
      iexists c, cn, s, a
      iframe Hc Hnet
      ileft
      ihave H : (encoding.json.decErrModel (hG := hG) dec c) $$ [Hd]
      · iunfold encoding.json.decErrModel
        iexists { d' with err' := GoInterface.ok i }
        iframe Hd
        isplitr
        · ipureintro; exact ⟨Hd'.1.trans Hdr, Hne⟩
        iexact He
      iexact H
    have hne : decide (GoInterface.ok i = GoInterface.nil) = false := decide_eq_false Hne
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexists fr
    iframe Hp
    iexact He

set_option warn.classDefReducibility false in
attribute [local instance] encoding.json.decRepModel in
/-- `events.newDecoder.spec` at the model's decoder (`decRepModel`), from `NewDecoder.spec`: a
connection is not nil, and a fresh decoder of the stream stands where nothing was read. -/
theorem events.newDecoder.wp_proof
    (wp_NewDecoder : encoding.json.NewDecoder.spec (GF := GF) (hG := hG)) :
    events.newDecoder.spec (GF := GF) (hG := hG) := by
  intro γ c cn s a
  wp_start_folded as ⟨#Hc, Htok⟩
  ihave #Hc2 := Hc
  iunfold net.isConn at Hc2
  icases Hc2 with ⟨%t, %la, %ra, %hc, -⟩
  wp_apply wp_NewDecoder c (recvTok (Gg := hG.goose_globalGS) cn s (VsrWire.protoOf γ)) $$ [Htok]
  · iframe
    ipureintro; rw [hc]; intro h; cases h
  iintro %dec Hok
  iapply HΦ
  iunfold events.rstream
  iexists c, cn, s, a
  iframe Hc Hpkg2
  iright
  iexists [], [], [], none
  iframe Hok
  ipureintro
  exact ⟨[], [], Or.inl rfl, rfl, rfl⟩

end proof

end Perennial.github_com.tangledbytes.go_vsr.pkg
