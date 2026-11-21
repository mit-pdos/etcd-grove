/-
The vocabulary of `encoding/base64`'s decoder specs (`Spec/encoding/base64/Encoding__Decode*.lean`,
prove-authcrypto, 2026-11-21): an `Encoding` that decodes padded base64 over its alphabet
(`decOk`), padded base64 text (`b64Ok`), and the facts about `NewEncoding`'s decode map
(`dmAfter`) the decoder's proofs read. Lean-first.
-/
module

public import Proof.encoding.base64.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace base64

/-- The most bytes `n` bytes of base64 decode to (`decodedLen(n, p)`): three per four, and for no
padding (`-1`) the bits of a final partial group. -/
def decLen (p : w32) (n : Nat) : Nat := if p = W32 (-1) then n / 4 * 3 + n % 4 * 6 / 8 else n / 4 * 3

/-- **Padded base64 text over the alphabet `α`** (RFC 4648 §4, as `StdEncoding` emits it): groups of
four symbols of `α`, the last of which may end in one or two `=` (61) after at least two symbols. -/
def b64Ok (α : List w8) : List w8 → Prop
  | [] => True
  | [a, b, c, d] => a ∈ α ∧ b ∈ α ∧ ((c ∈ α ∧ (d ∈ α ∨ d = 61)) ∨ (c = 61 ∧ d = 61))
  | a :: b :: c :: d :: e :: rest => a ∈ α ∧ b ∈ α ∧ c ∈ α ∧ d ∈ α ∧ b64Ok α (e :: rest)
  | _ => False

/-- `NewEncoding`'s decode map after `i` rounds maps each of the first `i` symbols to an index below
`i`, and every other byte to `0xff`. -/
theorem dmAfter_val (s : List w8) (x : w8) : ∀ i, i ≤ s.length → i ≤ 255 →
    (x ∈ s.take i → ((dmAfter s i).getD x.toNat 0).toNat < i) ∧
    (x ∉ s.take i → (dmAfter s i).getD x.toNat 0 = W8 255)
  | 0, _, _ => ⟨fun h => by simp at h, fun h => dmAfter_free s x 0 (Nat.zero_le _) h⟩
  | i + 1, hi, h255 => by
    have ih := dmAfter_val s x i (by omega) (by omega)
    have hlen := dmAfter_length s i
    have hsi : s.getD i 0 = s[i]'(by omega) := by
      simp [List.getD, List.getElem?_eq_getElem (show i < s.length by omega)]
    have htake : s.take (i + 1) = s.take i ++ [s[i]'(by omega)] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
    rw [dmAfter_succ, htake, hsi]
    have hx := x.isLt
    by_cases hxe : x = s[i]'(by omega)
    · rw [hxe]
      have hget : ((dmAfter s i).set (s[i]'(by omega)).toNat (W8 (i : Int))).getD
          (s[i]'(by omega)).toNat 0 = W8 (i : Int) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [hlen]; omega)]
        rfl
      rw [hget]
      refine ⟨fun _ => ?_, fun h => absurd (List.mem_append_right _ (List.mem_singleton_self _)) h⟩
      have : (W8 (i : Int)).toNat = i := by
        show (BitVec.ofInt 8 (i : Int)).toNat = i
        rw [BitVec.toNat_ofInt]; omega
      rw [this]; omega
    · have hne : (s[i]'(by omega)).toNat ≠ x.toNat := fun h => hxe (BitVec.eq_of_toNat_eq h).symm
      have key : ((dmAfter s i).set (s[i]'(by omega)).toNat (W8 (i : Int))).getD x.toNat 0 =
          (dmAfter s i).getD x.toNat 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]
      rw [key]
      have hmem : x ∈ s.take i ++ [s[i]'(by omega)] ↔ x ∈ s.take i := by
        simp only [List.mem_append, List.mem_singleton, hxe, or_false]
      rw [hmem]
      exact ⟨fun h => Nat.lt_succ_of_lt (ih.1 h), ih.2⟩

section enc
variable [GooseExts]

/-- **An `Encoding` that decodes padded base64 over its alphabet**: its alphabet is 64 symbols, none
of them `=`; its decode map is `NewEncoding`'s (`dmAfter`: each symbol's index, `0xff` for any other
byte); its padding is `=` and it is not strict (`StdEncoding`, bcrypt's `bcEncoding`). -/
def decOk (enc : _root_.Perennial.encoding.base64.Encoding) : Prop :=
  enc.encode'.arr.length = 64 ∧ (61 : w8) ∉ enc.encode'.arr ∧
  enc.decodeMap'.arr = dmAfter enc.encode'.arr 64 ∧ enc.padChar' = W32 61 ∧ enc.strict' = false

/-- The decode map of a `decOk` encoding: a symbol's entry is below 64. -/
theorem decOk_sym {enc : _root_.Perennial.encoding.base64.Encoding} (h : decOk enc) (x : w8)
    (hx : x ∈ enc.encode'.arr) : (enc.decodeMap'.arr.getD x.toNat 0).toNat < 64 := by
  obtain ⟨hl, -, hdm, -⟩ := h
  rw [hdm]
  have := (dmAfter_val enc.encode'.arr x 64 (by omega) (by omega)).1
  rw [← hl, List.take_length] at this
  rw [← hl]; exact this hx

/-- The decode map of a `decOk` encoding: any other byte's entry is `0xff`. -/
theorem decOk_nonsym {enc : _root_.Perennial.encoding.base64.Encoding} (h : decOk enc) (x : w8)
    (hx : x ∉ enc.encode'.arr) : enc.decodeMap'.arr.getD x.toNat 0 = W8 255 := by
  obtain ⟨hl, -, hdm, -⟩ := h
  rw [hdm]
  have := (dmAfter_val enc.encode'.arr x 64 (by omega) (by omega)).2
  rw [← hl] at this ⊢; rw [List.take_length] at this
  exact this hx

/-- The decode map of a `decOk` encoding has 256 entries. -/
theorem decOk_len {enc : _root_.Perennial.encoding.base64.Encoding} (h : decOk enc) :
    enc.decodeMap'.arr.length = 256 := by
  rw [h.2.2.1]; exact dmAfter_length _ _

end enc

/-- A symbol of `b64Enc` is the alphabet's: the index is below 64. -/
theorem getD_mem (α : List w8) (hα : α.length = 64) (x : w8) (hx : x.toNat < 64) :
    α.getD x.toNat 0 ∈ α := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

/-! The six-bit pieces' bounds, by their values (`toNat`), not `bv_decide`, whose proof rests on
native evaluation. -/

theorem shr_lt (b : w8) (k : Nat) (hk : k ≤ 8) : (b >>> k).toNat < 2 ^ (8 - k) := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hb := b.isLt
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← Nat.pow_add, Nat.sub_add_cancel hk]
  exact hb

theorem shl_and_lt (b : w8) (m k : Nat) (h : (m + 1) * 2 ^ k ≤ 64) :
    ((b &&& BitVec.ofNat 8 m) <<< k).toNat < 64 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq]
  have h1 : b.toNat &&& (BitVec.ofNat 8 m).toNat ≤ m :=
    Nat.le_trans Nat.and_le_right (by rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _)
  have h2 : (b.toNat &&& (BitVec.ofNat 8 m).toNat) * 2 ^ k < 64 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_of_le h1) (Nat.two_pow_pos k)) h
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h2

theorem and63_lt (b : w8) : (b &&& 63#8).toNat < 64 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem or_lt64' (a b : w8) (ha : a.toNat < 64) (hb : b.toNat < 64) : (a ||| b).toNat < 64 := by
  rw [BitVec.toNat_or]
  exact Nat.or_lt_two_pow (n := 6) ha hb

/-- **`b64Enc` with padding `=` is padded base64 text.** -/
theorem b64Enc_ok (α : List w8) (hα : α.length = 64) :
    ∀ d : List w8, b64Ok α (_root_.Perennial.encoding.base64.b64Enc α (some 61) d)
  | b0 :: b1 :: b2 :: rest => by
    have h0 : (b0 >>> 2).toNat < 64 := by
      exact shr_lt b0 2 (by decide)
    have h1 : (((b0 &&& 3) <<< 4) ||| (b1 >>> 4)).toNat < 64 := by
      exact or_lt64' _ _ (shl_and_lt b0 3 4 (by decide)) (Nat.lt_trans (shr_lt b1 4 (by decide)) (by decide))
    have h2 : (((b1 &&& 15) <<< 2) ||| (b2 >>> 6)).toNat < 64 := by
      exact or_lt64' _ _ (shl_and_lt b1 15 2 (by decide)) (Nat.lt_trans (shr_lt b2 6 (by decide)) (by decide))
    have h3 : (b2 &&& 63).toNat < 64 := by
      exact and63_lt b2
    have ih := b64Enc_ok α hα rest
    simp only [_root_.Perennial.encoding.base64.b64Enc]
    generalize _root_.Perennial.encoding.base64.b64Enc α (some 61) rest = r at ih
    match r, ih with
    | [], _ =>
      simp only [b64Ok]
      exact ⟨getD_mem α hα _ h0, getD_mem α hα _ h1, .inl ⟨getD_mem α hα _ h2, .inl (getD_mem α hα _ h3)⟩⟩
    | e :: r', ih =>
      simp only [b64Ok]
      exact ⟨getD_mem α hα _ h0, getD_mem α hα _ h1, getD_mem α hα _ h2, getD_mem α hα _ h3, ih⟩
  | [b0, b1] => by
    have h0 : (b0 >>> 2).toNat < 64 := by
      exact shr_lt b0 2 (by decide)
    have h1 : (((b0 &&& 3) <<< 4) ||| (b1 >>> 4)).toNat < 64 := by
      exact or_lt64' _ _ (shl_and_lt b0 3 4 (by decide)) (Nat.lt_trans (shr_lt b1 4 (by decide)) (by decide))
    have h2 : ((b1 &&& 15) <<< 2).toNat < 64 := by
      exact shl_and_lt b1 15 2 (by decide)
    simp only [_root_.Perennial.encoding.base64.b64Enc, Option.toList_some, List.cons_append,
      List.nil_append, b64Ok]
    exact ⟨getD_mem α hα _ h0, getD_mem α hα _ h1, .inl ⟨getD_mem α hα _ h2, .inr trivial⟩⟩
  | [b0] => by
    have h0 : (b0 >>> 2).toNat < 64 := by
      exact shr_lt b0 2 (by decide)
    have h1 : ((b0 &&& 3) <<< 4).toNat < 64 := by
      exact shl_and_lt b0 3 4 (by decide)
    simp only [_root_.Perennial.encoding.base64.b64Enc, Option.toList_some, List.cons_append,
      List.nil_append, b64Ok]
    exact ⟨getD_mem α hα _ h0, getD_mem α hα _ h1, .inr ⟨trivial, trivial⟩⟩
  | [] => by simp [_root_.Perennial.encoding.base64.b64Enc, b64Ok]

/-- Padded base64 text is a multiple of four bytes long. -/
theorem b64Ok_len (α : List w8) : ∀ s : List w8, b64Ok α s → s.length % 4 = 0
  | [], _ => rfl
  | [_, _, _, _], _ => by simp
  | _ :: _ :: _ :: _ :: e :: rest, h => by
    have := b64Ok_len α (e :: rest) h.2.2.2.2
    simp only [List.length_cons] at this ⊢; omega
  | [_], h | [_, _], h | [_, _, _], h => by simp_all [b64Ok]

/-- A nonempty padded base64 text starts with a group of four: two symbols, then a symbol or `=`,
then a symbol or `=` (`=` only after `=`), and the group with an `=` is the last. -/
theorem b64Ok_group (α : List w8) (h61 : (61 : w8) ∉ α) (l : List w8) (h : b64Ok α l)
    (hne : l ≠ []) :
    ∃ a b c d rest, l = a :: b :: c :: d :: rest ∧ a ∈ α ∧ b ∈ α ∧ (c ∈ α ∨ c = 61) ∧
      (d ∈ α ∨ d = 61) ∧ (c = 61 → d = 61) ∧ ((c = 61 ∨ d = 61) → rest = []) ∧ b64Ok α rest := by
  match l, h with
  | [], _ => exact absurd rfl hne
  | [_], h | [_, _], h | [_, _, _], h => simp [b64Ok] at h
  | [a, b, c, d], h =>
    refine ⟨a, b, c, d, [], rfl, h.1, h.2.1, ?_, ?_, ?_, fun _ => rfl, trivial⟩
    · rcases h.2.2 with ⟨hc, -⟩ | ⟨hc, -⟩
      · exact .inl hc
      · exact .inr hc
    · rcases h.2.2 with ⟨-, hd⟩ | ⟨-, hd⟩
      · exact hd
      · exact .inr hd
    · intro hc
      rcases h.2.2 with ⟨hc', -⟩ | ⟨-, hd⟩
      · exact absurd (hc ▸ hc') h61
      · exact hd
  | a :: b :: c :: d :: e :: rest, h =>
    refine ⟨a, b, c, d, e :: rest, rfl, h.1, h.2.1, .inl h.2.2.1, .inl h.2.2.2.1, ?_, ?_, h.2.2.2.2⟩
    · intro hc; exact absurd (hc ▸ h.2.2.1) h61
    · rintro (hc | hd)
      · exact absurd (hc ▸ h.2.2.1) h61
      · exact absurd (hd ▸ h.2.2.2.1) h61

/-- **The `j`-th byte of the quantum at `i`** of padded base64 text: the quantum is whole (four
bytes), its byte is a symbol, or `=` at position 2 or 3 of the last quantum (followed by `=` at 3). -/
theorem b64Ok_at (α : List w8) (h61 : (61 : w8) ∉ α) (s : List w8) (i j : Nat)
    (hb : b64Ok α (s.drop i)) (hi : i < s.length) (hj : j < 4) :
    i + 4 ≤ s.length ∧ ∃ x, s[i + j]? = some x ∧
      (x ∈ α ∨ (2 ≤ j ∧ x = 61 ∧ i + 4 = s.length ∧ (j = 2 → s[i + 3]? = some 61))) := by
  obtain ⟨a, b, c, d, rest, hdr, ha, hb', hc, hd, hcd, hrest, -⟩ :=
    b64Ok_group α h61 _ hb (by intro h; rw [List.drop_eq_nil_iff] at h; omega)
  have hlen := congrArg List.length hdr
  simp only [List.length_drop, List.length_cons] at hlen
  have hget : ∀ k, s[i + k]? = (a :: b :: c :: d :: rest)[k]? := by
    intro k; rw [← hdr, List.getElem?_drop]
  refine ⟨by omega, ?_⟩
  match j, hj with
  | 0, _ => exact ⟨a, by rw [hget]; rfl, .inl ha⟩
  | 1, _ => exact ⟨b, by rw [hget]; rfl, .inl hb'⟩
  | 2, _ =>
    refine ⟨c, by rw [hget]; rfl, ?_⟩
    rcases hc with hc | hc
    · exact .inl hc
    · have hr := hrest (.inl hc); subst hr
      exact .inr ⟨Nat.le_refl _, hc, by simp at hlen; omega, fun _ => by rw [hget]; simp [hcd hc]⟩
  | 3, _ =>
    refine ⟨d, by rw [hget]; rfl, ?_⟩
    rcases hd with hd | hd
    · exact .inl hd
    · have hr := hrest (.inr hd); subst hr
      exact .inr ⟨by omega, hd, by simp at hlen; omega, fun h => absurd h (by omega)⟩

/-- Padded base64 text after a quantum is padded base64 text. -/
theorem b64Ok_drop4 (α : List w8) (h61 : (61 : w8) ∉ α) (l : List w8) (h : b64Ok α l)
    (hne : l ≠ []) : b64Ok α (l.drop 4) := by
  obtain ⟨a, b, c, d, rest, rfl, -, -, -, -, -, -, hr⟩ := b64Ok_group α h61 l h hne
  simpa using hr

/-- Padded base64 text from `i`, then from the next quantum. -/
theorem b64Ok_dropAt (α : List w8) (h61 : (61 : w8) ∉ α) (s : List w8) (i : Nat)
    (h : b64Ok α (s.drop i)) (hi : i < s.length) : b64Ok α (s.drop (i + 4)) := by
  have h' := b64Ok_drop4 α h61 _ h (by intro h'; rw [List.drop_eq_nil_iff] at h'; omega)
  have e : (s.drop i).drop 4 = s.drop (i + 4) := by
    rw [List.drop_drop] <;> first | rfl | (congr 1; omega)
  rwa [e] at h'

/-- The OR of decode-map entries below 64 is not `0xff`: `assemble32`/`assemble64` accept. -/
theorem or_lt64 (a b : w8) (ha : a.toNat < 64) (hb : b.toNat < 64) : (a ||| b).toNat < 64 := by
  rw [BitVec.toNat_or]
  exact Nat.or_lt_two_pow (n := 6) ha hb

/-- An entry `0xff` makes the OR `0xff`: `assemble32`/`assemble64` reject. -/
theorem or_ff_left (a b : w8) (ha : a = W8 255) : a ||| b = W8 255 := by
  subst ha
  have e : (W8 255 : w8) = BitVec.allOnes 8 := by decide
  rw [e, BitVec.allOnes_or]

theorem or_ff_right (a b : w8) (hb : b = W8 255) : a ||| b = W8 255 := by
  subst hb
  have e : (W8 255 : w8) = BitVec.allOnes 8 := by decide
  rw [e, BitVec.or_allOnes]

end base64
end EtcdGrove
end Perennial
