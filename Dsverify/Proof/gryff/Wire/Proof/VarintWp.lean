/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Wire/Proof/VarintWp.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# U1: `encoding/binary.ReadUvarint` / `ReadVarint` on a `*bufio.Reader`

Over dsv-bufio's `*bufio.Reader` (`ownReader`, `Lemmas.lean`): its `ReadByte.wp_proof` gives the
error's `io.ptrTyped` (what `ReadUvarint`'s `err == io.EOF` needs; the lab copied its harness's
`wp_ReadByte` to keep it). The facts of the bytes ahead are `readNext` (the lab unfolded its reader).
-/
module

public import Dsverify.Proof.gryff.Wire.Proof.Lemmas
public import Dsverify.Proof.gryff.Wire.Proof.Varint

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.wire

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode


/-- The bytes `D` after the reader's position begin a (prefix of a) `uint64` varint. -/
def vok (D : List w8) : Prop := ∃ n : Nat, n < 2 ^ 64 ∧ comparable D (uvarintEnc n)

section varint
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The bytes after the reader's position `R` meet `P`, up to extension**, learned at each later
position `R ++ V` (the lab's `□ (∀ D, I (R ++ D) ={⊤}=∗ I (R ++ D) ∗ ⌜P D⌝)`, which unfolded its
reader to reach the buffered bytes; here stated of the reader `ownReader` itself, never unfolded:
for a connection it follows from `net.connReader_proto`). -/
def readNext (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R : List w8)
    (P : List w8 → Prop) : IProp GF :=
  iprop(□ ∀ V : List w8, ownReader br rd I (R ++ V) ={⊤}=∗
    ownReader br rd I (R ++ V) ∗ ⌜∃ pend, P (V ++ pend)⌝)

instance readNext_persistent (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R : List w8)
    (P : List w8 → Prop) : Persistent (readNext br rd I R P) := by
  unfold readNext; infer_instance

/-- A fact `P` of the stream after the reader's position, at the bytes it has returned. -/
theorem ownReader_peek (P : List w8 → Prop) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R V : List w8) :
    readNext br rd I R P ∗ ownReader br rd I (R ++ V) ⊢
      |={⊤}=> ownReader br rd I (R ++ V) ∗ ⌜∃ pend, P (V ++ pend)⌝ := by
  iintro ⟨#HP, Hown⟩
  iunfold readNext at HP
  iapply HP $$ Hown

/-- A trivial fact. -/
theorem readNext_true (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R : List w8)
    (P : List w8 → Prop) (hP : ∀ D, P D) : ⊢ readNext br rd I R P := by
  iunfold readNext
  iintro !> %V Hown
  imodintro
  iframe Hown
  ipureintro; exact ⟨[], hP _⟩

/-- The fact after `X` more bytes. -/
theorem readNext_shift (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R X : List w8)
    (P : List w8 → Prop) :
    readNext br rd I R P ⊢ readNext br rd I (R ++ X) (fun D => P (X ++ D)) := by
  iunfold readNext
  iintro #HP !> %V Hown
  rw [List.append_assoc] at *
  imod HP $$ %(X ++ V) Hown with ⟨Hown, %Hp⟩
  imodintro
  iframe Hown
  ipureintro
  obtain ⟨pend, hp⟩ := Hp
  exact ⟨pend, by simpa [List.append_assoc] using hp⟩

theorem readNext_mono (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R : List w8)
    (P P' : List w8 → Prop) (h : ∀ D, P D → P' D) :
    readNext br rd I R P ⊢ readNext br rd I R P' := by
  iunfold readNext
  iintro #HP !> %V Hown
  imod HP $$ %V Hown with ⟨Hown, %Hp⟩
  imodintro
  iframe Hown
  ipureintro
  obtain ⟨pend, hp⟩ := Hp
  exact ⟨pend, h _ hp⟩

end varint

section hyps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The varint functions of `encoding/binary`** (hypotheses: Perennial `7b2259a12` translates
`ReadUvarint`, `ReadVarint`, `PutUvarint`, `PutVarint` names only, `binary.toml`; notes/dsv-gryff.md,
"Hypotheses"). Each field is the lab's statement of the same name (`Wire/Proof/VarintWp.lean`, which
proved them over its own translation of the Go bodies, `Harness/Code/binary_extra.lean`), over
dsv-bufio's reader here. Never an instance: a premise of the kit's statement. -/
class BinaryVarintHyps : Prop where
  readUvarint : ∀ (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
          isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
          readerOk rd I ∗ readNext br rd I R vok ∗ ownReader br rd I R }}
        (App (Val (@! encoding.binary.ReadUvarint))
          (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
      {{ (x : w64) (err : GoInterface), RET (PairV #x #err); ∃ V : List w8,
          ownReader br rd I (R ++ V) ∗
          ((⌜err = interface.nil ∧ V = uvarintEnc (uint.nat x)⌝) ∨
           rdErr rd err) }}
  readVarint : ∀ (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
          isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
          readerOk rd I ∗ readNext br rd I R vok ∗ ownReader br rd I R }}
        (App (Val (@! encoding.binary.ReadVarint))
          (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
      {{ (x : w64) (err : GoInterface), RET (PairV #x #err); ∃ V : List w8,
          ownReader br rd I (R ++ V) ∗
          ((⌜err = interface.nil ∧ ∃ ux : w64, V = uvarintEnc (uint.nat ux) ∧
              x = (if ux &&& W64 1 = W64 0 then ux >>> W64 1 else ~~~ (ux >>> W64 1))⌝) ∨
           rdErr rd err) }}
  putUvarint : ∀ (p : Loc) (n : w64) (vs : List w8) (x : w64)
    (hn : (uvarintEnc (uint.nat x)).length ≤ sint.nat n),
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
          typedPointsto p (array.mk (sint.Z n) vs) (DFrac.own 1) }}
        (App (App (Val (@! encoding.binary.PutUvarint)) (Val #(slice.mk p n n))) (Val #x))
      {{ RET #(W64 (uvarintEnc (uint.nat x)).length);
          typedPointsto p (array.mk (sint.Z n)
            (uvarintEnc (uint.nat x) ++ vs.drop (uvarintEnc (uint.nat x)).length)) (DFrac.own 1) }}
  putVarint : ∀ (p : Loc) (n : w64) (nI : Int) (vs : List w8) (x : w64) (hnI : sint.Z n = nI)
    (hx : 0 ≤ sint.Z x) (hn : (varintEnc (sint.Z x)).length ≤ sint.nat n),
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
          typedPointsto p (array.mk nI vs) (DFrac.own 1) }}
        (App (App (Val (@! encoding.binary.PutVarint)) (Val #(slice.mk p n n))) (Val #x))
      {{ RET #(W64 (varintEnc (sint.Z x)).length);
          typedPointsto p (array.mk nI
            (varintEnc (sint.Z x) ++ vs.drop (varintEnc (sint.Z x)).length)) (DFrac.own 1) }}

end hyps

section varint2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

variable [bufio.Assumptions] [io.Assumptions] [encoding.binary.Assumptions]
set_option goose.wp.extras true

theorem wp_ReadUvarint [h : BinaryVarintHyps GF] (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R vok ∗ ownReader br rd I R }}
      (App (Val (@! encoding.binary.ReadUvarint))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (x : w64) (err : GoInterface), RET (PairV #x #err); ∃ V : List w8,
        ownReader br rd I (R ++ V) ∗
        ((⌜err = interface.nil ∧ V = uvarintEnc (uint.nat x)⌝) ∨
         rdErr rd err) }} :=
  h.readUvarint br rd I R

theorem wp_ReadVarint [h : BinaryVarintHyps GF] (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R vok ∗ ownReader br rd I R }}
      (App (Val (@! encoding.binary.ReadVarint))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (x : w64) (err : GoInterface), RET (PairV #x #err); ∃ V : List w8,
        ownReader br rd I (R ++ V) ∗
        ((⌜err = interface.nil ∧ ∃ ux : w64, V = uvarintEnc (uint.nat ux) ∧
            x = (if ux &&& W64 1 = W64 0 then ux >>> W64 1 else ~~~ (ux >>> W64 1))⌝) ∨
         rdErr rd err) }} :=
  h.readVarint br rd I R


end varint2

section putvarint
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [encoding.binary.Assumptions]

set_option goose.wp.extras true

/-- `binary.PutUvarint(b[:], x)` into a local byte array `b` (held as the array). -/
theorem wp_PutUvarint [h : BinaryVarintHyps GF] (p : Loc) (n : w64) (vs : List w8) (x : w64)
    (hn : (uvarintEnc (uint.nat x)).length ≤ sint.nat n) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
        typedPointsto p (array.mk (sint.Z n) vs) (DFrac.own 1) }}
      (App (App (Val (@! encoding.binary.PutUvarint)) (Val #(slice.mk p n n))) (Val #x))
    {{ RET #(W64 (uvarintEnc (uint.nat x)).length);
        typedPointsto p (array.mk (sint.Z n)
          (uvarintEnc (uint.nat x) ++ vs.drop (uvarintEnc (uint.nat x)).length)) (DFrac.own 1) }} :=
  h.putUvarint p n vs x hn

theorem varint_of_nonneg (x : w64) (hx : 0 ≤ sint.Z x) :
    varintEnc (sint.Z x) = uvarintEnc (uint.nat (x <<< W64 1)) := by
  have h63 : sint.Z x < 2 ^ 63 := by word
  have hu : uint.nat (x <<< W64 1) = 2 * (sint.Z x).toNat := by
    have hxz : (x.toNat : Int) = sint.Z x := by
      simp only [sint.Z] at hx h63 ⊢
      rw [BitVec.toInt_eq_toNat_cond] at hx h63 ⊢
      by_cases hc : 2 * x.toNat < 2 ^ 64
      · simp only [hc, ↓reduceIte] at hx h63 ⊢
      · simp only [hc, ↓reduceIte] at hx h63 ⊢; omega
    have h1 : (W64 1 : w64).toNat = 1 := rfl
    simp only [uint.nat]
    rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, h1, Nat.shiftLeft_eq]
    have : x.toNat < 2 ^ 63 := by omega
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hu, varintEnc, zigzag]
  simp only [hx, ↓reduceIte]
  congr 1
  omega

/-- `binary.PutVarint(b[:], x)` of a nonnegative `x` into a local byte array `b`. -/
theorem wp_PutVarint [h : BinaryVarintHyps GF] (p : Loc) (n : w64) (nI : Int) (vs : List w8) (x : w64) (hnI : sint.Z n = nI)
    (hx : 0 ≤ sint.Z x) (hn : (varintEnc (sint.Z x)).length ≤ sint.nat n) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
        typedPointsto p (array.mk nI vs) (DFrac.own 1) }}
      (App (App (Val (@! encoding.binary.PutVarint)) (Val #(slice.mk p n n))) (Val #x))
    {{ RET #(W64 (varintEnc (sint.Z x)).length);
        typedPointsto p (array.mk nI
          (varintEnc (sint.Z x) ++ vs.drop (varintEnc (sint.Z x)).length)) (DFrac.own 1) }} :=
  h.putVarint p n nI vs x hnI hx hn

theorem varintEnc_len_le (len : Nat) (h : len < 2 ^ 63) :
    (varintEnc (sint.Z (W64 (len : Int)))).length ≤ 10 := by
  rw [varintEnc_len len h]
  obtain ⟨V', c, he, -, -, hl, -⟩ := uvarintEnc_u64 (2 * len) (by omega)
  rw [he]; simp; omega

end putvarint

end Perennial.gryff.wire
