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
byte); its padding is `=` and it is not strict; neither newline (`'\n'`, `'\r'`) is a symbol (which the
decoder skips: `dropNL`) (`StdEncoding`). -/
def decOk (enc : _root_.Perennial.encoding.base64.Encoding) : Prop :=
  enc.encode'.arr.length = 64 ∧ (61 : w8) ∉ enc.encode'.arr ∧
  enc.decodeMap'.arr = dmAfter enc.encode'.arr 64 ∧ enc.padChar' = W32 61 ∧ enc.strict' = false ∧
  W8 10 ∉ enc.encode'.arr ∧ W8 13 ∉ enc.encode'.arr

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

/-- The decode map of a `decOk` encoding: an entry other than `0xff` is a symbol's. -/
theorem decOk_sym_of_ne {enc : _root_.Perennial.encoding.base64.Encoding} (h : decOk enc) (x : w8)
    (hx : enc.decodeMap'.arr.getD x.toNat 0 ≠ W8 255) : x ∈ enc.encode'.arr :=
  Classical.byContradiction fun hn => hx (decOk_nonsym h x hn)

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


/-! The exact error condition of the decoder (D3 follow-up (a), 2026-11-28): the text without its
newlines (`dropNL`), read a quantum at a time. -/

section exact
variable [GooseExts]

open Perennial.encoding.base64 (dropNL)

theorem not_of_true_eq_not_decide {P : Prop} [Decidable P] (h : true = !decide P) : ¬ P := by
  intro hp; simp [hp] at h

theorem or_ne_ff {a b : w8} (h : a ||| b ≠ W8 255) : a ≠ W8 255 ∧ b ≠ W8 255 :=
  ⟨fun ha => h (or_ff_left a b ha), fun hb => h (or_ff_right a b hb)⟩

theorem drop_eq_cons (s : List w8) (k : Nat) (x : w8) (hx : s[k]? = some x) :
    s.drop k = x :: s.drop (k + 1) := by
  have hk : k < s.length := by
    rcases Nat.lt_or_ge k s.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hx; cases hx
  rw [List.drop_eq_getElem_cons hk]
  rw [List.getElem?_eq_getElem hk] at hx
  rw [Option.some.inj hx]

/-- A byte other than a newline is kept. -/
theorem dropNL_drop_keep (s : List w8) (k : Nat) (x : w8) (hx : s[k]? = some x) (h10 : x ≠ W8 10)
    (h13 : x ≠ W8 13) : dropNL (s.drop k) = x :: dropNL (s.drop (k + 1)) := by
  rw [drop_eq_cons s k x hx]
  simp only [dropNL, List.filter_cons]
  rw [ite_eq_left_of_eq_true _ _ (by simp; exact ⟨h10, h13⟩)]

/-- A newline is skipped. -/
theorem dropNL_drop_skip (s : List w8) (k : Nat) (x : w8) (hx : s[k]? = some x)
    (h : x = W8 10 ∨ x = W8 13) : dropNL (s.drop k) = dropNL (s.drop (k + 1)) := by
  rw [drop_eq_cons s k x hx]
  rcases h with rfl | rfl
  · simp [dropNL]
  · have e : (((W8 13 : w8) == W8 10) || ((W8 13 : w8) == W8 13)) = true := by decide
    simp only [dropNL, List.filter_cons, e, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem dropNL_drop_end (s : List w8) (k : Nat) (h : s.length ≤ k) : dropNL (s.drop k) = [] := by
  rw [List.drop_eq_nil_of_le h]; rfl

/-- A symbol is not a newline. -/
theorem decOk_ne10 {enc : _root_.Perennial.encoding.base64.Encoding} (h : decOk enc) {x : w8}
    (hx : x ∈ enc.encode'.arr) : x ≠ W8 10 := fun e => h.2.2.2.2.2.1 (e ▸ hx)

theorem decOk_ne13 {enc : _root_.Perennial.encoding.base64.Encoding} (h : decOk enc) {x : w8}
    (hx : x ∈ enc.encode'.arr) : x ≠ W8 13 := fun e => h.2.2.2.2.2.2 (e ▸ hx)

/-- A whole group of symbols in front does not change padded base64 text's validity. -/
theorem b64Ok_cons4 (α : List w8) {a b c d : w8} (t : List w8) (ha : a ∈ α) (hb : b ∈ α)
    (hc : c ∈ α) (hd : d ∈ α) : b64Ok α (a :: b :: c :: d :: t) ↔ b64Ok α t := by
  match t with
  | [] => simp only [b64Ok]; exact ⟨fun _ => trivial, fun _ => ⟨ha, hb, .inl ⟨hc, .inl hd⟩⟩⟩
  | e :: r => simp only [b64Ok]; exact ⟨fun h => h.2.2.2.2, fun h => ⟨ha, hb, hc, hd, h⟩⟩

/-- **What one quantum of `decodeQuantum` accepts** of the text `t` (without newlines), leaving
`t'`: either the rest is empty and `t` was padded base64 text (no quantum, or the last one), or a
whole group of four symbols. -/
def quantumOk (α t t' : List w8) : Prop :=
  (t' = [] ∧ b64Ok α t) ∨ ∃ a b c d, a ∈ α ∧ b ∈ α ∧ c ∈ α ∧ d ∈ α ∧ t = a :: b :: c :: d :: t'

theorem quantumOk_iff {α t t' : List w8} (h : quantumOk α t t') : b64Ok α t ↔ b64Ok α t' := by
  rcases h with ⟨rfl, h⟩ | ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩
  · exact ⟨fun _ => by simp [b64Ok], fun _ => h⟩
  · exact b64Ok_cons4 α _ ha hb hc hd

/-- `decodeQuantum`'s loop state: from `k0` it has read the `j` symbols `pre` (and any newlines),
up to `k`. -/
def readSyms (α s : List w8) (k0 j k : Nat) : Prop :=
  ∃ pre : List w8, pre.length = j ∧ (∀ x ∈ pre, x ∈ α) ∧ dropNL (s.drop k0) = pre ++ dropNL (s.drop k)

/-- In padded base64 text, the byte after fewer than four symbols of a group is a symbol, or `=`
after two (then followed by just `=`) or three (then the end). -/
theorem b64Ok_mid (α : List w8) (h61 : (61 : w8) ∉ α) (pre rest : List w8) (c : w8)
    (hpre : ∀ x ∈ pre, x ∈ α) (hlen : pre.length < 4) (h : b64Ok α (pre ++ c :: rest)) :
    c ∈ α ∨ (2 ≤ pre.length ∧ c = 61 ∧ (pre.length = 2 → rest = [61]) ∧
      (pre.length = 3 → rest = [])) := by
  obtain ⟨a, b, c', d, r, hl, ha, hb, hc, hd, hcd, hr, -⟩ := b64Ok_group α h61 _ h (by simp)
  match pre, hlen, hl with
  | [], _, hl =>
    simp only [List.nil_append, List.cons.injEq] at hl
    left; rw [hl.1]; exact ha
  | [p0], _, hl =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hl
    left; rw [hl.2.1]; exact hb
  | [p0, p1], _, hl =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hl
    obtain ⟨-, -, rfl, rfl⟩ := hl
    rcases hc with hc | hc
    · exact .inl hc
    · right
      refine ⟨by simp, hc, fun _ => ?_, fun h => by simp at h⟩
      rw [hcd hc, hr (.inl hc)]
  | [p0, p1, p2], _, hl =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hl
    obtain ⟨-, -, -, rfl, rfl⟩ := hl
    rcases hd with hd | hd
    · exact .inl hd
    · right
      exact ⟨by simp, hd, fun h => by simp at h, fun _ => hr (.inr hd)⟩
  | _ :: _ :: _ :: _ :: _, h, _ => simp at h; omega

/-- One to three symbols are not padded base64 text. -/
theorem b64Ok_short (α pre : List w8) (h1 : 1 ≤ pre.length) (h3 : pre.length < 4) :
    ¬ b64Ok α pre := fun h => by
  have := b64Ok_len α pre h; omega

theorem b64Ok_pad2 (α pre : List w8) (hpre : ∀ x ∈ pre, x ∈ α) (hl : pre.length = 2) :
    b64Ok α (pre ++ [61, 61]) := by
  match pre, hl with
  | [a, b], _ =>
    simp only [List.cons_append, List.nil_append, b64Ok]
    exact ⟨hpre a (by simp), hpre b (by simp), .inr ⟨trivial, trivial⟩⟩

theorem b64Ok_pad1 (α pre : List w8) (hpre : ∀ x ∈ pre, x ∈ α) (hl : pre.length = 3) :
    b64Ok α (pre ++ [61]) := by
  match pre, hl with
  | [a, b, c], _ =>
    simp only [List.cons_append, List.nil_append, b64Ok]
    exact ⟨hpre a (by simp), hpre b (by simp), .inl ⟨hpre c (by simp), .inr trivial⟩⟩

theorem quantumOk_four (α pre t : List w8) (hpre : ∀ x ∈ pre, x ∈ α) (hl : pre.length = 4) :
    quantumOk α (pre ++ t) t := by
  match pre, hl with
  | [a, b, c, d], _ =>
    exact .inr ⟨a, b, c, d, hpre a (by simp), hpre b (by simp), hpre c (by simp), hpre d (by simp), rfl⟩

theorem readSyms_congr {α s : List w8} {k0 j j' k k' : Nat} (hj : j = j') (hk : k = k')
    (h : readSyms α s k0 j k) : readSyms α s k0 j' k' := hj ▸ hk ▸ h

theorem readSyms_sym {α s : List w8} {k0 j k : Nat} {x : w8} (h : readSyms α s k0 j k)
    (hx : s[k]? = some x) (hxa : x ∈ α) (h10 : x ≠ W8 10) (h13 : x ≠ W8 13) :
    readSyms α s k0 (j + 1) (k + 1) := by
  obtain ⟨pre, hl, hp, he⟩ := h
  refine ⟨pre ++ [x], by simp [hl], fun y hy => ?_, ?_⟩
  · rcases List.mem_append.1 hy with hy | hy
    · exact hp y hy
    · rw [List.mem_singleton.1 hy]; exact hxa
  · rw [he, dropNL_drop_keep s k x hx h10 h13, List.append_assoc]; rfl

theorem readSyms_nl {α s : List w8} {k0 j k : Nat} {x : w8} (h : readSyms α s k0 j k)
    (hx : s[k]? = some x) (hn : x = W8 10 ∨ x = W8 13) : readSyms α s k0 j (k + 1) := by
  obtain ⟨pre, hl, hp, he⟩ := h
  exact ⟨pre, hl, hp, by rw [he, dropNL_drop_skip s k x hx hn]⟩

theorem readSyms_end {α s : List w8} {k0 j k : Nat} (h : readSyms α s k0 j k) (hk : s.length ≤ k) :
    ∃ pre : List w8, pre.length = j ∧ (∀ y ∈ pre, y ∈ α) ∧ dropNL (s.drop k0) = pre := by
  obtain ⟨pre, hl, hp, he⟩ := h
  exact ⟨pre, hl, hp, by rw [he, dropNL_drop_end s k hk, List.append_nil]⟩

/-- The input ends inside a group: not padded base64 text. -/
theorem readSyms_end_bad {α s : List w8} {k0 j k : Nat} (h : readSyms α s k0 j k)
    (hk : s.length ≤ k) (hj1 : 1 ≤ j) (hj4 : j < 4) : ¬ b64Ok α (dropNL (s.drop k0)) := by
  obtain ⟨pre, hl, -, he⟩ := readSyms_end h hk
  rw [he]; exact b64Ok_short α pre (by omega) (by omega)

/-- The input ends at a group's boundary: valid, if all of the text was read. -/
theorem readSyms_end_ok {α s : List w8} {k0 k : Nat} (h : readSyms α s k0 0 k)
    (hk : s.length ≤ k) : quantumOk α (dropNL (s.drop k0)) (dropNL (s.drop k)) := by
  obtain ⟨pre, hl, -, he⟩ := readSyms_end h hk
  rw [List.length_eq_zero_iff] at hl; subst hl
  exact .inl ⟨dropNL_drop_end s k hk, by rw [he]; simp [b64Ok]⟩

/-- Four symbols read. -/
theorem readSyms_four {α s : List w8} {k0 k : Nat} (h : readSyms α s k0 4 k) :
    quantumOk α (dropNL (s.drop k0)) (dropNL (s.drop k)) := by
  obtain ⟨pre, hl, hp, he⟩ := h
  rw [he]; exact quantumOk_four α pre _ hp hl

/-- A byte that is neither a symbol nor a newline, nor `=` after two or three symbols. -/
theorem readSyms_bad {α s : List w8} (h61 : (61 : w8) ∉ α) {k0 j k : Nat} {x : w8}
    (h : readSyms α s k0 j k) (hj : j < 4) (hx : s[k]? = some x) (hxa : x ∉ α) (h10 : x ≠ W8 10)
    (h13 : x ≠ W8 13) (hp : x ≠ 61 ∨ j < 2) : ¬ b64Ok α (dropNL (s.drop k0)) := by
  obtain ⟨pre, hl, hpre, he⟩ := h
  rw [he, dropNL_drop_keep s k x hx h10 h13]
  intro hb
  rcases b64Ok_mid α h61 pre _ x hpre (by omega) hb with h | ⟨h2, h61', -⟩
  · exact hxa h
  · rcases hp with hp | hp
    · exact hp h61'
    · omega

/-- `=` at `k` after `j` symbols. -/
theorem readSyms_pad {α s : List w8} {k0 j k : Nat} (h : readSyms α s k0 j k)
    (hx : s[k]? = some (W8 61)) : ∃ pre : List w8, pre.length = j ∧ (∀ y ∈ pre, y ∈ α) ∧
      dropNL (s.drop k0) = pre ++ 61 :: dropNL (s.drop (k + 1)) := by
  obtain ⟨pre, hl, hp, he⟩ := h
  exact ⟨pre, hl, hp, by rw [he, dropNL_drop_keep s k (W8 61) hx (by decide) (by decide)]; rfl⟩

theorem pad2_bad (α : List w8) (h61 : (61 : w8) ∉ α) (pre rest : List w8) (hp : ∀ y ∈ pre, y ∈ α)
    (hl : pre.length = 2) (hr : rest ≠ [61]) : ¬ b64Ok α (pre ++ 61 :: rest) := fun hb => by
  rcases b64Ok_mid α h61 pre rest 61 hp (by omega) hb with h | ⟨-, -, h2, -⟩
  · exact h61 h
  · exact hr (h2 hl)

theorem pad3_bad (α : List w8) (h61 : (61 : w8) ∉ α) (pre rest : List w8) (hp : ∀ y ∈ pre, y ∈ α)
    (hl : pre.length = 3) (hr : rest ≠ []) : ¬ b64Ok α (pre ++ 61 :: rest) := fun hb => by
  rcases b64Ok_mid α h61 pre rest 61 hp (by omega) hb with h | ⟨-, -, -, h3⟩
  · exact h61 h
  · exact hr (h3 hl)

/-- Four symbols at `k` (the fast paths' `assemble32`/`assemble64`): validity from `k` is validity
after them. -/
theorem b64Ok_drop_sym4 {enc : _root_.Perennial.encoding.base64.Encoding} (hok : decOk enc)
    (s : List w8) (k : Nat) (x0 x1 x2 x3 : w8)
    (hx0 : s[k]? = some x0) (hx1 : s[k + 1]? = some x1) (hx2 : s[k + 2]? = some x2)
    (hx3 : s[k + 3]? = some x3) (h0 : x0 ∈ enc.encode'.arr) (h1 : x1 ∈ enc.encode'.arr)
    (h2 : x2 ∈ enc.encode'.arr) (h3 : x3 ∈ enc.encode'.arr) :
    b64Ok enc.encode'.arr (dropNL (s.drop k)) ↔ b64Ok enc.encode'.arr (dropNL (s.drop (k + 4))) := by
  rw [dropNL_drop_keep s k x0 hx0 (decOk_ne10 hok h0) (decOk_ne13 hok h0),
    dropNL_drop_keep s (k + 1) x1 hx1 (decOk_ne10 hok h1) (decOk_ne13 hok h1),
    show k + 1 + 1 = k + 2 from rfl,
    dropNL_drop_keep s (k + 2) x2 hx2 (decOk_ne10 hok h2) (decOk_ne13 hok h2),
    show k + 2 + 1 = k + 3 from rfl,
    dropNL_drop_keep s (k + 3) x3 hx3 (decOk_ne10 hok h3) (decOk_ne13 hok h3),
    show k + 3 + 1 = k + 4 from rfl]
  exact b64Ok_cons4 _ _ h0 h1 h2 h3

/-- Every byte of padded base64 text is a symbol or `=`. -/
theorem b64Ok_mem (α : List w8) : ∀ l : List w8, b64Ok α l → ∀ y ∈ l, y ∈ α ∨ y = 61
  | [], _, y, hy => by simp at hy
  | [a, b, c, d], h, y, hy => by
    simp only [b64Ok] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    obtain ⟨ha, hb, hcd⟩ := h
    rcases hy with rfl | rfl | rfl | rfl
    · exact .inl ha
    · exact .inl hb
    · rcases hcd with ⟨hc, -⟩ | ⟨hc, -⟩
      · exact .inl hc
      · exact .inr hc
    · rcases hcd with ⟨-, hd⟩ | ⟨-, hd⟩
      · exact hd
      · exact .inr hd
  | a :: b :: c :: d :: e :: rest, h, y, hy => by
    simp only [b64Ok] at h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact .inl h.1
    rcases List.mem_cons.1 hy with rfl | hy
    · exact .inl h.2.1
    rcases List.mem_cons.1 hy with rfl | hy
    · exact .inl h.2.2.1
    rcases List.mem_cons.1 hy with rfl | hy
    · exact .inl h.2.2.2.1
    exact b64Ok_mem α (e :: rest) h.2.2.2.2 y hy
  | [_], h, _, _ | [_, _], h, _, _ | [_, _, _], h, _, _ => by simp [b64Ok] at h

/-- Padded base64 text over an alphabet without newlines has none. -/
theorem dropNL_of_b64Ok (α : List w8) (h10 : W8 10 ∉ α) (h13 : W8 13 ∉ α) (l : List w8)
    (h : b64Ok α l) : dropNL l = l := by
  unfold dropNL
  rw [List.filter_eq_self]
  intro y hy
  rcases b64Ok_mem α l h y hy with hy | rfl
  · have e1 : y ≠ W8 10 := fun e => h10 (e ▸ hy)
    have e2 : y ≠ W8 13 := fun e => h13 (e ▸ hy)
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨e1, e2⟩
  · decide

/-- **`StdEncoding` decodes what it encodes** without an error. -/
theorem _root_.Perennial.encoding.base64.stdDecOk_stdEnc (x : List w8) :
    _root_.Perennial.encoding.base64.stdDecOk (_root_.Perennial.encoding.base64.stdEnc x) := by
  unfold _root_.Perennial.encoding.base64.stdDecOk _root_.Perennial.encoding.base64.stdEnc
  have hb := b64Enc_ok _root_.Perennial.encoding.base64.stdAlphabet (by decide) x
  rw [dropNL_of_b64Ok _ (by decide) (by decide) _ hb]
  exact hb

end exact

end base64
end EtcdGrove
end Perennial
