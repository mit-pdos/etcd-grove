/-
# `wire.BinaryVarintHyps` from Perennial's `encoding/binary` proofs

The class's five fields (`VarintWp.lean`) derived from Perennial's linked results of perennial#689
(`encoding.binary.wp_ReadUvarint`, `wp_ReadVarint`, `wp_PutUvarint`, `wp_PutVarint`) and the
package fact `encoding.binary.errOverflow_of_init`.

* The reads: dsv-bufio's `*bufio.Reader` `br` is an `io.ByteReader` (`io.byteReaderOk`) with the
  state `S r := ownReader br rd I (R ++ r)` (the bytes it returned after `R`) and the evidence
  `E r e := bufio.errE rd.E (R ++ r) e` of an error (`BufioSpecs.readByte`). Of what `uvarintRes`
  allows: an accepted varint is the encoding of its value, since the stream ahead begins a `uint64`
  varint prefix (`readNext ... vok`, learned at the end by an update: `wp_fupd`), and an accepted
  varint comparable with an encoding is that encoding (`uvarintOk_eq_enc`); the overflow is
  `errOverflow` and the reader's errors are `rdErr`'s disjuncts (`io.ErrUnexpectedEOF` in place of
  `io.EOF`).
* The writes: the local array as the full slice `slice.mk p n n`.
* The two `uvarintEnc` (gryff's `Wire/Enc.lean`, Perennial's `Varint.lean`) are the same
  function (`uvarintEnc_eq`).
-/
module

public import Dsverify.Proof.gryff.Wire.Proof.VarintWp
public import Perennial.Proof.encoding.binary.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.wire

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

theorem uvarintEnc_eq (n : Nat) : uvarintEnc n = encoding.binary.uvarintEnc n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [uvarintEnc, encoding.binary.uvarintEnc]
    split
    · rfl
    · rw [ih (n / 128) (by omega)]

theorem varintEnc_eq (x : Int) :
    varintEnc x = encoding.binary.uvarintEnc (encoding.binary.zigzag x) := by
  rw [varintEnc, uvarintEnc_eq]; rfl

/-- An accepted varint, the stream comparable with the encoding of a `uint64`, is the encoding of
its value. -/
theorem uvarintOk_vok {V : List w8} (x : w64) (hV : encoding.binary.uvarintOk V)
    (hx : uint.nat x = encoding.binary.uvarintDec V) (hv : ∃ pend, vok (V ++ pend)) :
    V = uvarintEnc (uint.nat x) := by
  obtain ⟨pend, n, -, hc⟩ := hv
  have hc' : comparable V (uvarintEnc n) := comparable_mono (List.prefix_append _ _) hc
  rw [uvarintEnc_eq] at hc'
  have he := encoding.binary.uvarintOk_eq_enc n hV hc'
  rw [hx, he, encoding.binary.uvarintDec_enc, uvarintEnc_eq]

section holds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The local array `p` as the full slice `slice.mk p n n`, and back. -/
theorem array_full_slice (p : Loc) (n : w64) (vs : List w8) :
    typedPointsto (GF := GF) p (array.mk (sint.Z n) vs) (DFrac.own 1) ⊢
      slice.mk p n n ↦* vs ∗
      (∀ vs' : List w8, slice.mk p n n ↦* vs' -∗
        typedPointsto (GF := GF) p (array.mk (sint.Z n) vs') (DFrac.own 1)) := by
  iintro H
  ihave %Hl := array_len _ _ _ _ $$ H
  have e := array_prefix_slice (GF := GF) p n n (sint.Z n) vs ⟨by omega, Int.le_refl _⟩ (Int.le_refl _)
  have hn : sint.nat n = vs.length := by
    show (sint.Z n).toNat = vs.length; rw [Hl]; simp
  have ht : vs.take (sint.nat n) = vs := List.take_of_length_le (by omega)
  have hd : vs.drop (sint.nat n) = [] := List.drop_of_length_le (by omega)
  rw [ht, hd] at e
  icases e $$ H with ⟨Hs, Hrest⟩
  iframe Hs
  iintro %vs' Hs
  have e2 := array_of_prefix_slice (GF := GF) p n n (sint.Z n - sint.Z n) vs' []
  rw [List.append_nil, show sint.Z n + (sint.Z n - sint.Z n) = sint.Z n by omega] at e2
  iapply e2
  iframe Hs Hrest

variable [encoding.binary.Assumptions]

theorem putUvarint_holds (p : Loc) (n : w64) (vs : List w8) (x : w64)
    (hn : (uvarintEnc (uint.nat x)).length ≤ sint.nat n) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
          typedPointsto p (array.mk (sint.Z n) vs) (DFrac.own 1) }}
        (App (App (Val (@! encoding.binary.PutUvarint)) (Val #(slice.mk p n n))) (Val #x))
      {{ RET #(W64 (uvarintEnc (uint.nat x)).length);
          typedPointsto p (array.mk (sint.Z n)
            (uvarintEnc (uint.nat x) ++ vs.drop (uvarintEnc (uint.nat x)).length)) (DFrac.own 1) }} := by
  rw [uvarintEnc_eq] at hn ⊢
  iintro %Φ ⟨-, Hp⟩ HΦ
  ihave %Hl := array_len _ _ _ _ $$ Hp
  icases array_full_slice (GF := GF) p n vs $$ Hp with ⟨Hs, Hback⟩
  wp_apply encoding.binary.wp_PutUvarint (GF := GF) (slice.mk p n n) vs x
    (by show _ ≤ vs.length; have : sint.nat n = vs.length := by
          { show (sint.Z n).toNat = vs.length; rw [Hl]; simp }
        omega) $$ [$Hs] as Hs
  iapply HΦ
  iapply Hback $$ Hs

theorem putVarint_holds (p : Loc) (n : w64) (nI : Int) (vs : List w8) (x : w64)
    (hnI : sint.Z n = nI) (_hx : 0 ≤ sint.Z x) (hn : (varintEnc (sint.Z x)).length ≤ sint.nat n) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
          typedPointsto p (array.mk nI vs) (DFrac.own 1) }}
        (App (App (Val (@! encoding.binary.PutVarint)) (Val #(slice.mk p n n))) (Val #x))
      {{ RET #(W64 (varintEnc (sint.Z x)).length);
          typedPointsto p (array.mk nI
            (varintEnc (sint.Z x) ++ vs.drop (varintEnc (sint.Z x)).length)) (DFrac.own 1) }} := by
  subst hnI
  rw [varintEnc_eq] at hn ⊢
  iintro %Φ ⟨-, Hp⟩ HΦ
  ihave %Hl := array_len _ _ _ _ $$ Hp
  icases array_full_slice (GF := GF) p n vs $$ Hp with ⟨Hs, Hback⟩
  wp_apply encoding.binary.wp_PutVarint (GF := GF) (slice.mk p n n) vs x
    (by show _ ≤ vs.length; have : sint.nat n = vs.length := by
          { show (sint.Z n).toNat = vs.length; rw [Hl]; simp }
        omega) $$ [$Hs] as Hs
  iapply HΦ
  iapply Hback $$ Hs

end holds

section reads
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions] [io.Assumptions] [encoding.binary.Assumptions] [BufioSpecs GF]

/-- dsv-bufio's `*bufio.Reader` `br` as an `io.ByteReader`: its state the bytes returned after
`R`, its errors' evidence `bufio.errE`. -/
theorem bufReader_byteReaderOk (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R : List w8) :
    ⊢ io.byteReaderOk (interface.mk (go.GoType.PointerType bufio.Reader.ty) #br)
      (fun r => ownReader br rd I (R ++ r))
      (fun r e => EtcdGrove.bufio.errE rd.E (R ++ r) e) := by
  iunfold io.byteReaderOk
  iintro !> %r %Φ !> Hown HΦ
  iapply BufioSpecs.readByte (GF := GF) br rd.ri (fun _ m => 0 < m) I rd.E (R ++ r) $$ [Hown]
  · iexact Hown
  iintro !> %c %err Hr
  iapply HΦ
  icases Hr with (⟨%he, Hown⟩ | ⟨%he, #HE, %Ht, Hown⟩)
  · ileft
    dsimp only
    rw [← List.append_assoc]
    iframe Hown
    ipureintro; exact he
  · iright
    iframe Hown HE
    ipureintro; exact ⟨he, Ht⟩

/-- What `ReadUvarint` returns, the stream ahead a `uint64` varint prefix (`hv`), as the class's
post: the encoding of the value, or an error `rdErr` allows. -/
theorem uvarintRes_post (rd : RSt GF) (R V : List w8) (x : w64) (err eof ueof ovf : GoInterface)
    (hv : ∃ pend, vok (V ++ pend)) (hue : ueof ≠ interface.nil) (hov : ovf ≠ interface.nil) :
    ((globalAddr io.ErrUnexpectedEOF ↦□ ueof : IProp GF) ∗
      (globalAddr encoding.binary.errOverflow ↦□ ovf : IProp GF) ∗
      encoding.binary.uvarintRes (fun r e => EtcdGrove.bufio.errE rd.E (R ++ r) e)
        eof ueof ovf [] V x err) ⊢
    ⌜err = interface.nil ∧ V = uvarintEnc (uint.nat x)⌝ ∨ rdErr rd err := by
  iintro ⟨#Hue, #Hov, #Hres⟩
  iunfold encoding.binary.uvarintRes at Hres
  icases Hres with (%Hok | %Hovf | ⟨%e, %He, #HE⟩)
  · obtain ⟨he, hV, hx⟩ := Hok
    ileft; ipureintro; exact ⟨he, uvarintOk_vok x hV hx hv⟩
  · obtain ⟨rfl, -⟩ := Hovf
    iright; iunfold rdErr
    isplitr
    · ipureintro; exact hov
    imodintro; iright; iright; iright; iexact Hov
  · obtain ⟨-, -, hne, hueof, hother⟩ := He
    iright; iunfold rdErr
    by_cases hx : e = eof ∧ V ≠ []
    · rw [hueof hx]
      isplitr
      · ipureintro; exact hue
      imodintro; iright; ileft; iexact Hue
    · rw [hother hx]
      isplitr
      · ipureintro; exact hne
      imodintro; ileft; iexists _; iexact HE

set_option goose.wp.extras true

theorem readUvarint_holds (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
          isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
          readerOk rd I ∗ readNext br rd I R vok ∗ ownReader br rd I R }}
        (App (Val (@! encoding.binary.ReadUvarint))
          (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
      {{ (x : w64) (err : GoInterface), RET (PairV #x #err); ∃ V : List w8,
          ownReader br rd I (R ++ V) ∗
          ((⌜err = interface.nil ∧ V = uvarintEnc (uint.nat x)⌝) ∨
           rdErr rd err) }} := by
  iintro %Φ ⟨#Hbin, -, #Hio, -, #Hnext, Hown⟩ HΦ
  ihave #Hinit := io.isInit_access $$ Hio
  icases Hinit with ⟨-, -, -, -, #HEOF, #HUE, -⟩
  iunfold errors.newVar at HEOF HUE
  icases HEOF with ⟨%eofl, #Heof, -⟩
  icases HUE with ⟨%ueofl, #Hueof, -⟩
  ihave #HOV := encoding.binary.errOverflow_of_init $$ Hbin
  iunfold errors.newVar at HOV
  icases HOV with ⟨%ovl, #Hovf, -⟩
  ihave #Hbr := bufReader_byteReaderOk (GF := GF) br rd I R
  ihave Hown := ownReader_eq br rd I R (R ++ []) (by simp) $$ Hown
  iapply wp_fupd
  wp_apply encoding.binary.wp_ReadUvarint (GF := GF)
    (interface.mk (go.GoType.PointerType bufio.Reader.ty) #br)
    (fun r => ownReader br rd I (R ++ r)) (fun r e => EtcdGrove.bufio.errE rd.E (R ++ r) e) []
    _ _ _ $$ [$Hbin $Hio $Hbr $Heof $Hueof $Hovf $Hown] as %x %err ⟨%V, Hown, #Hres⟩
  ihave Hown := ownReader_eq br rd I _ (R ++ V) (by simp) $$ Hown
  imod ownReader_peek vok br rd I R V $$ [Hnext Hown] with ⟨Hown, %Hpk⟩
  · iframe Hnext Hown
  ihave #Hpost := uvarintRes_post rd R V x err
    (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #eofl)
    (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #ueofl)
    (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #ovl)
    Hpk (fun h => by cases h) (fun h => by cases h)
    $$ [Hueof Hovf Hres]
  · iframe Hueof Hovf Hres
  imodintro
  iapply HΦ
  iexists V
  iframe Hown Hpost

theorem readVarint_holds (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
          isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
          readerOk rd I ∗ readNext br rd I R vok ∗ ownReader br rd I R }}
        (App (Val (@! encoding.binary.ReadVarint))
          (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
      {{ (x : w64) (err : GoInterface), RET (PairV #x #err); ∃ V : List w8,
          ownReader br rd I (R ++ V) ∗
          ((⌜err = interface.nil ∧ ∃ ux : w64, V = uvarintEnc (uint.nat ux) ∧
              x = (if ux &&& W64 1 = W64 0 then ux >>> W64 1 else ~~~ (ux >>> W64 1))⌝) ∨
           rdErr rd err) }} := by
  iintro %Φ ⟨#Hbin, -, #Hio, -, #Hnext, Hown⟩ HΦ
  ihave #Hinit := io.isInit_access $$ Hio
  icases Hinit with ⟨-, -, -, -, #HEOF, #HUE, -⟩
  iunfold errors.newVar at HEOF HUE
  icases HEOF with ⟨%eofl, #Heof, -⟩
  icases HUE with ⟨%ueofl, #Hueof, -⟩
  ihave #HOV := encoding.binary.errOverflow_of_init $$ Hbin
  iunfold errors.newVar at HOV
  icases HOV with ⟨%ovl, #Hovf, -⟩
  ihave #Hbr := bufReader_byteReaderOk (GF := GF) br rd I R
  ihave Hown := ownReader_eq br rd I R (R ++ []) (by simp) $$ Hown
  iapply wp_fupd
  wp_apply encoding.binary.wp_ReadVarint (GF := GF)
    (interface.mk (go.GoType.PointerType bufio.Reader.ty) #br)
    (fun r => ownReader br rd I (R ++ r)) (fun r e => EtcdGrove.bufio.errE rd.E (R ++ r) e) []
    _ _ _ $$ [$Hbin $Hio $Hbr $Heof $Hueof $Hovf $Hown] as %x %err ⟨%V, %ux, Hown, #Hres, %Hx⟩
  ihave Hown := ownReader_eq br rd I _ (R ++ V) (by simp) $$ Hown
  imod ownReader_peek vok br rd I R V $$ [Hnext Hown] with ⟨Hown, %Hpk⟩
  · iframe Hnext Hown
  ihave #Hpost := uvarintRes_post rd R V ux err
    (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #eofl)
    (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #ueofl)
    (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #ovl)
    Hpk (fun h => by cases h) (fun h => by cases h)
    $$ [Hueof Hovf Hres]
  · iframe Hueof Hovf Hres
  imodintro
  iapply HΦ
  iexists V
  iframe Hown
  icases Hpost with (%Hok | #Herr)
  · ileft; ipureintro; exact ⟨Hok.1, ux, Hok.2, Hx⟩
  · iright; iexact Herr

/-- **`wire.BinaryVarintHyps` holds**, from Perennial's proofs of `encoding/binary`
(perennial#689) and dsv-bufio's `ReadByte` (`BufioSpecs`). -/
theorem binaryVarintHyps_holds : BinaryVarintHyps GF :=
  ⟨readUvarint_holds, readVarint_holds, putUvarint_holds, putVarint_holds,
    encoding.binary.errOverflow_of_init⟩

end reads

end Perennial.gryff.wire
