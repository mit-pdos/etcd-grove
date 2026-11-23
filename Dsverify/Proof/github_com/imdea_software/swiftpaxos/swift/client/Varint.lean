/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/Varint.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`readUvarint`/`readVarint` (swift/varint.go, copies of Go's `encoding/binary`; change log C5')
over a `*bufio.Reader` as an `io.ByteReader`: the bytes read so far `R` grow by `data`; without
an error, `data` is an accepted varint (`uvTerm`) and the result its value.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.VarintPure
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.swift

-- PORT: lab imports dropped: Harness.Proof.bufio.ReadFull

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [swift.Assumptions] [bufio.Assumptions] [io.Assumptions] [errors.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- A read error: return it (or `io.ErrUnexpectedEOF`) with the bytes read so far. -/
local macro "errtail" : tactic => `(tactic| (
  (try wp_auto)
  wp_for_post
  iapply HΦ
  iexists acc
  iframe
  ipureintro
  intro h
  first | exact absurd h Hune | cases h))

/-- `x | uint64(c) << k` with `x < 2^k`, `k ≤ 63`: the sum (mod 2^64). -/
theorem or_shl (a c k : Nat) (ha : a < 2 ^ k) (hk : k ≤ 63) (hc : c < 256) :
    (W64 (a : Int) ||| (W64 (c : Int) <<< W64 (k : Int))) = W64 ((a + c * 2 ^ k : Nat) : Int) := by
  apply BitVec.eq_of_toNat_eq
  have h2k : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hk
  have hsplit : (2:Nat) ^ 64 = 2 ^ (64 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  have hm : (c * 2 ^ k) % 2 ^ 64 = 2 ^ k * (c % 2 ^ (64 - k)) := by
    rw [hsplit, Nat.mul_mod_mul_right, Nat.mul_comm]
  have hka : (W64 (a : Int)).toNat = a := by simp [W64]; omega
  have hkk : (W64 (k : Int)).toNat = k := by simp [W64]; omega
  have hcc : (W64 (c : Int)).toNat = c := by simp [W64]; omega
  rw [BitVec.toNat_or, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, hka, hkk, hcc, Nat.shiftLeft_eq, hm]
  rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt ha]
  have hlt : 2 ^ k * (c % 2 ^ (64 - k)) + a < 2 ^ 64 := by
    have h1 : c % 2 ^ (64 - k) < 2 ^ (64 - k) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : 2 ^ k * (c % 2 ^ (64 - k)) + 2 ^ k ≤ 2 ^ k * 2 ^ (64 - k) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h1
    rw [hsplit]; rw [Nat.mul_comm (2 ^ (64 - k))]; omega
  simp only [W64, BitVec.toNat_ofInt]
  have : (a + c * 2 ^ k) % 2 ^ 64 = 2 ^ k * (c % 2 ^ (64 - k)) + a := by
    rw [Nat.add_mod, hm, Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.add_comm]
    exact Nat.mod_eq_of_lt hlt
  rw [← this]
  omega

theorem and127 (c : w8) : (c &&& W8 127).toNat = c.toNat % 128 := by
  rw [BitVec.toNat_and]
  have : (W8 127).toNat = 2 ^ 7 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem uvDec_step (acc : List w8) (c : w8) (hl : acc.length ≤ 9) :
    (W64 (sp.uvDec acc : Int) ||| W64 (uint.Z (c &&& W8 127)) <<< W64 ((7 * acc.length : Nat) : Int)) =
      W64 (sp.uvDec (acc ++ [c]) : Int) := by
  have h1 := sp.uvDec_lt acc
  have h2 : (128 : Nat) ^ acc.length = 2 ^ (7 * acc.length) := by rw [Nat.pow_mul]
  have := or_shl (sp.uvDec acc) (c &&& W8 127).toNat (7 * acc.length) (by omega) (by omega)
    (by have := (c &&& W8 127).isLt; simpa using this)
  rw [show uint.Z (c &&& W8 127) = ((c &&& W8 127).toNat : Int) from rfl, this, sp.uvDec_snoc,
    and127, h2, Nat.mul_comm]

theorem uvDec_last (acc : List w8) (c : w8) (hl : acc.length ≤ 9) (hc : c.toNat < 128) :
    (W64 (sp.uvDec acc : Int) ||| W64 (uint.Z c) <<< W64 ((7 * acc.length : Nat) : Int)) =
      W64 (sp.uvDec (acc ++ [c]) : Int) := by
  have h1 := sp.uvDec_lt acc
  have h2 : (128 : Nat) ^ acc.length = 2 ^ (7 * acc.length) := by rw [Nat.pow_mul]
  have := or_shl (sp.uvDec acc) c.toNat (7 * acc.length) (by omega) (by omega) (by omega)
  rw [show uint.Z c = (c.toNat : Int) from rfl, this, sp.uvDec_snoc, Nat.mod_eq_of_lt hc, h2,
    Nat.mul_comm]

/-- What `readUvarint` accepts decodes below `2 ^ 64` (the tenth byte is at most 1). -/
theorem uvDec_acc_lt (acc : List w8) (c : w8) (hl : acc.length ≤ 9)
    (h9 : acc.length = 9 → c.toNat ≤ 1) (hc : c.toNat < 128) :
    sp.uvDec (acc ++ [c]) < 2 ^ 64 := by
  rw [sp.uvDec_snoc, Nat.mod_eq_of_lt hc]
  have h1 := sp.uvDec_lt acc
  rcases Nat.lt_or_ge acc.length 9 with hlt | hge
  · have hp : 128 ^ acc.length ≤ 128 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
    have : 128 ^ acc.length * c.toNat ≤ 128 ^ 8 * 127 :=
      Nat.mul_le_mul hp (by omega)
    have : sp.uvDec acc < 128 ^ 8 := Nat.lt_of_lt_of_le h1 hp
    have : (128 : Nat) ^ 8 * 127 + 128 ^ 8 < 2 ^ 64 := by decide
    omega
  · have he : acc.length = 9 := by omega
    have hc1 := h9 he
    rw [he] at h1 ⊢
    have : 128 ^ 9 * c.toNat ≤ 128 ^ 9 * 1 := Nat.mul_le_mul_left _ hc1
    have : (128 : Nat) ^ 9 + 128 ^ 9 = 2 ^ 64 := by decide
    omega

theorem wp_readUvarint (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8)
    (ov : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        bufio.readerOk rd I ∗ bufio.ownReader br rd I R ∗
        typedPointsto (globalAddr swift.errVarintOverflow) ov DFrac.discard ∗
        ⌜ov ≠ interface.nil⌝ }}
      (App (Val (@! swift.readUvarint))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (x : w64) (err : GoInterface), RET (PairV #x #err); ∃ data : List w8,
        bufio.ownReader br rd I (R ++ data) ∗
        ⌜err = interface.nil → sp.uvTerm data ∧ sp.uvDec data < 2 ^ 64 ∧
          x = W64 (sp.uvDec data : Int)⌝ }} := by
  wp_start as ⟨#Hrd, Hown, #Hov, %Hovn⟩
  ihave #Hio := io.isInit_access $$ Hpkg2
  icases Hio with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
  ihave ⟨%ue, #Hue, #Hueo, %Hune⟩ := bufio.newVar_errOrNil _ _ $$ HUEOF
  iunfold errors.newVar at HEOF
  icases HEOF with ⟨%eofx, #HEOF, -⟩
  wp_auto
  ihave HL : (∃ (acc : List w8) (iv : w64),
      "i" ∷ i_ptr ↦ iv ∗ "x" ∷ x_ptr ↦ W64 (sp.uvDec acc : Int) ∗
      "s" ∷ s_ptr ↦ W64 ((7 * acc.length : Nat) : Int) ∗
      "Hown" ∷ bufio.ownReader br rd I (R ++ acc) ∗
      "%Hacc" ∷ ⌜sint.Z iv = acc.length ∧ acc.length ≤ 10 ∧ ∀ b ∈ acc, 128 ≤ b.toNat⌝ : IProp GF)
    $$ [i x s Hown]
  · iexists [], _
    simp only [List.append_nil]
    iframe
    ipureintro; simp
  wp_for HL
  obtain ⟨hiv, hlen, hhi⟩ := Hacc
  wp_if_destruct
  · wp_apply bufio.wp_ReadByte_wf br rd I (R ++ acc) $$ [$Hrd $Hown] as %c %err Hr
    icases Hr with (⟨%Hen, Hown⟩ | ⟨⟨%Hen, %Hwf⟩, #Ha, Hown⟩)
    · subst Hen
      dsimp only
      wp_auto
      have hl9 : acc.length < 10 := by
        have : sint.Z (W64 10) = 10 := rfl
        omega
      have h128 : uint.Z (W8 128) = 128 := rfl
      by_cases hc : uint.Z c < uint.Z (W8 128)
      · rw [decide_eq_true hc]
        wp_auto
        have hcl : c.toNat < 128 := by simp [uint.Z] at hc h128; omega
        -- the result, if returned
        have hres : sp.uvTerm (acc ++ [c]) := ⟨acc, c, rfl, hhi, hcl, by simp; omega⟩
        by_cases h9 : iv = W64 9
        · rw [decide_eq_true h9]
          wp_auto
          by_cases hc1 : uint.Z (W8 1) < uint.Z c
          · rw [decide_eq_true hc1]
            wp_auto
            wp_for_post
            iapply HΦ
            iexists acc ++ [c]
            rw [List.append_assoc]
            iframe
            ipureintro; intro h; exact absurd h Hovn
          · rw [decide_eq_false hc1]
            wp_auto
            wp_for_post
            iapply HΦ
            iexists acc ++ [c]
            rw [List.append_assoc]
            iframe
            ipureintro
            intro _
            refine ⟨hres, uvDec_acc_lt acc c (by omega) (fun _ => ?_) hcl, uvDec_last acc c (by omega) hcl⟩
            have : ¬ (1 < c.toNat) := by simp [uint.Z] at hc1; omega
            omega
        · rw [decide_eq_false h9]
          wp_auto
          wp_for_post
          iapply HΦ
          iexists acc ++ [c]
          rw [List.append_assoc]
          iframe
          ipureintro
          intro _
          refine ⟨hres, uvDec_acc_lt acc c (by omega) (fun he => ?_) hcl, uvDec_last acc c (by omega) hcl⟩
          exfalso; apply h9; apply BitVec.eq_of_toInt_eq; simp only [sint.Z] at hiv ⊢; rw [hiv, he]; rfl
      · rw [decide_eq_false hc]
        wp_auto
        wp_for_post
        iframe
        iexists acc ++ [c], _
        rw [uvDec_step acc c (by omega),
          show W64 ((7 * acc.length : Nat) : Int) + W64 7 = W64 ((7 * (acc ++ [c]).length : Nat) : Int)
            by simp only [List.length_append, List.length_singleton]; word]
        rw [List.append_assoc]
        iframe
        ipureintro
        refine ⟨by simp only [List.length_append, List.length_singleton]; word,
          by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
        intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact hhi x h
        · simp at h; subst h; simp [uint.Z] at hc; omega
    · rcases err with ei | _
      · dsimp only
        wp_auto
        by_cases hi0 : sint.Z (W64 0) < sint.Z iv
        · rw [decide_eq_true hi0]
          wp_auto
          by_cases hty : ei.ty = go.GoType.PointerType errors.errorString.ty
          · obtain ⟨l, hl⟩ := Hwf ei rfl _ hty
            simp only [hty, ↓reduceIte]
            rw [hl]
            wp_auto
            wp_if_destruct
            · errtail
            · errtail
          · simp only [hty, ↓reduceIte]
            errtail
        · rw [decide_eq_false hi0]
          errtail
      · exact absurd rfl Hen
  · iapply HΦ
    iexists acc
    iframe
    ipureintro; intro h; exact absurd h Hovn

/-- Zig-zag decoding (`readVarint`): `u >> 1`, complemented when `u` is odd. -/
def unzigzag (u : w64) : w64 := if u &&& W64 1 = W64 0 then u >>> W64 1 else ~~~(u >>> W64 1)

/-- A non-negative length as written by `binary.PutVarint` (`Wire.lean`'s `varintLen`) decodes
to itself. -/
theorem unzigzag_len (n : Nat) (h : n < 2 ^ 62) : unzigzag (W64 ((2 * n : Nat) : Int)) = W64 n := by
  unfold unzigzag
  have : W64 ((2 * n : Nat) : Int) &&& W64 1 = W64 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (W64 1).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp [W64]; omega
  rw [if_pos this]
  word

theorem wp_readVarint (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8)
    (ov : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        bufio.readerOk rd I ∗ bufio.ownReader br rd I R ∗
        typedPointsto (globalAddr swift.errVarintOverflow) ov DFrac.discard ∗
        ⌜ov ≠ interface.nil⌝ }}
      (App (Val (@! swift.readVarint))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (x : w64) (err : GoInterface), RET (PairV #x #err); ∃ data : List w8,
        bufio.ownReader br rd I (R ++ data) ∗
        ⌜err = interface.nil → sp.uvTerm data ∧ sp.uvDec data < 2 ^ 64 ∧
          x = unzigzag (W64 (sp.uvDec data : Int))⌝ }} := by
  wp_start as ⟨#Hrd, Hown, #Hov, %Hovn⟩
  wp_auto
  wp_apply wp_readUvarint br rd I R ov $$ [$Hrd $Hown $Hov] as %ux %err ⟨%data, Hown, %Hd⟩
  · ipureintro; exact Hovn
  by_cases h1 : ux &&& W64 1 = W64 0
  · rw [decide_eq_true h1]
    wp_auto
    iapply HΦ
    iexists data; iframe
    ipureintro; intro he
    obtain ⟨ht, hb, hx⟩ := Hd he
    refine ⟨ht, hb, ?_⟩
    rw [← hx]; unfold unzigzag; rw [if_pos h1]
  · rw [decide_eq_false h1]
    wp_auto
    iapply HΦ
    iexists data; iframe
    ipureintro; intro he
    obtain ⟨ht, hb, hx⟩ := Hd he
    refine ⟨ht, hb, ?_⟩
    rw [← hx]; unfold unzigzag; rw [if_neg h1]

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
