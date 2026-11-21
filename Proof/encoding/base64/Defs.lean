/-
The vocabulary of `encoding/base64`'s specs (`Spec/encoding/base64/`): an `Encoding`'s padding as the
model sees it (`padOf`), and the length of an encoding (`encLen`, `EncodedLen`'s value). Lean-first.
-/
module

public import Proof.encoding.base64.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace base64

/-- The padding of an `Encoding` whose `padChar` is `p`: none for `NoPadding` (`-1`), else the byte
`byte(p)` (`Encode`'s `dst[i] = byte(enc.padChar)`). -/
def padOf (p : w32) : Option w8 := if p = W32 (-1) then none else some (W8 (sint.Z p))

/-- The length of the encoding of `n` bytes (`EncodedLen(n)`): `4` per group of 3 bytes, rounded
up with padding, else the symbols of the last group's bits only. -/
def encLen (pad : Option w8) (n : Nat) : Nat :=
  if pad.isSome then (n + 2) / 3 * 4 else n / 3 * 4 + (n % 3 * 8 + 5) / 6

theorem b64Enc_length (alpha : List w8) (pad : Option w8) :
    ∀ d : List w8, (_root_.Perennial.encoding.base64.b64Enc alpha pad d).length = encLen pad d.length
  | b0 :: b1 :: b2 :: rest => by
    have ih := b64Enc_length alpha pad rest
    simp only [_root_.Perennial.encoding.base64.b64Enc, List.length_cons, ih, encLen]
    split <;> omega
  | [b0, b1] => by
    cases pad <;> simp [_root_.Perennial.encoding.base64.b64Enc, encLen]
  | [b0] => by
    cases pad <;> simp [_root_.Perennial.encoding.base64.b64Enc, encLen]
  | [] => by
    cases pad <;> simp [_root_.Perennial.encoding.base64.b64Enc, encLen]

/-- Encoding whole groups and then the rest is encoding the concatenation. -/
theorem b64Enc_append (alpha : List w8) (pad : Option w8) :
    ∀ (xs ys : List w8), xs.length % 3 = 0 →
      _root_.Perennial.encoding.base64.b64Enc alpha pad (xs ++ ys) =
        _root_.Perennial.encoding.base64.b64Enc alpha pad xs ++
          _root_.Perennial.encoding.base64.b64Enc alpha pad ys
  | [], ys, _ => by simp [_root_.Perennial.encoding.base64.b64Enc]
  | [_], _, h => by simp at h
  | [_, _], _, h => by simp at h
  | b0 :: b1 :: b2 :: rest, ys, h => by
    simp only [List.cons_append, _root_.Perennial.encoding.base64.b64Enc]
    rw [b64Enc_append alpha pad rest ys (by simp at h; omega)]

/-- The first `3(k+1)` bytes are the first `3k` and the next group. -/
theorem take_group (d : List w8) (k : Nat) (h : 3 * k + 3 ≤ d.length) :
    d.take (3 * (k + 1)) = d.take (3 * k) ++
      [d[3 * k]'(by omega), d[3 * k + 1]'(by omega), d[3 * k + 2]'(by omega)] := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_append, List.length_cons, List.length_nil]; omega
  · intro i h1 h2
    simp only [List.getElem_take]
    by_cases hi : i < 3 * k
    · rw [List.getElem_append_left (by simp; omega)]; simp
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_take, Nat.min_eq_left (by omega : 3 * k ≤ d.length)]
      have : i - 3 * k < 3 := by simp at h1; omega
      rcases (by omega : i - 3 * k = 0 ∨ i - 3 * k = 1 ∨ i - 3 * k = 2) with h' | h' | h' <;>
        simp only [h', List.getElem_cons_zero, List.getElem_cons_succ] <;> congr 1 <;> omega

/-- Writing four symbols at position `n` of `pre ++ rest` (`pre` of length `n`). -/
theorem set4 (pre rest : List w8) (n : Nat) (hn : pre.length = n) (c0 c1 c2 c3 : w8)
    (h : 4 ≤ rest.length) :
    ((((pre ++ rest).set n c0).set (n + 1) c1).set (n + 2) c2).set
        (n + 3) c3 = pre ++ [c0, c1, c2, c3] ++ rest.drop 4 := by
  subst hn
  match rest, h with
  | r0 :: r1 :: r2 :: r3 :: rs, _ =>
    simp [List.set_append_right]

/-- Writing two symbols over the last two of `pre ++ rest`. -/
theorem set2 (pre rest : List w8) (n : Nat) (hn : pre.length = n) (c0 c1 : w8) (h : rest.length = 2) :
    ((pre ++ rest).set n c0).set (n + 1) c1 = pre ++ [c0, c1] := by
  subst hn
  match rest, h with
  | [r0, r1], _ => simp [List.set_append_right]

/-- Writing three symbols over the last three of `pre ++ rest`. -/
theorem set3 (pre rest : List w8) (n : Nat) (hn : pre.length = n) (c0 c1 c2 : w8)
    (h : rest.length = 3) :
    (((pre ++ rest).set n c0).set (n + 1) c1).set (n + 2) c2 = pre ++ [c0, c1, c2] := by
  subst hn
  match rest, h with
  | [r0, r1, r2], _ => simp [List.set_append_right]

/-- `NewEncoding`'s `decodeMap` after `i` rounds of its loop over the alphabet `s`: the inverse
of `s`'s first `i` symbols, `0xff` elsewhere. -/
def dmAfter (s : List w8) (i : Nat) : List w8 :=
  (List.range i).foldl (fun m j => m.set (s.getD j 0).toNat (W8 (j : Int))) (List.replicate 256 (W8 255))

theorem dmAfter_succ (s : List w8) (i : Nat) :
    dmAfter s (i + 1) = (dmAfter s i).set (s.getD i 0).toNat (W8 (i : Int)) := by
  unfold dmAfter; rw [List.range_succ, List.foldl_append]; rfl

theorem dmAfter_length (s : List w8) : ∀ i, (dmAfter s i).length = 256
  | 0 => by simp only [dmAfter, List.range_zero, List.foldl_nil, List.length_replicate]
  | i + 1 => by rw [dmAfter_succ, List.length_set, dmAfter_length s i]

/-- A byte none of the first `i` symbols is still `0xff`. -/
theorem dmAfter_free (s : List w8) (x : w8) : ∀ i, i ≤ s.length → x ∉ s.take i →
    (dmAfter s i).getD x.toNat 0 = W8 255
  | 0, _, _ => by
    have := x.isLt
    simp only [dmAfter, List.range_zero, List.foldl_nil, List.getD_eq_getElem?_getD,
      List.getElem?_replicate, show x.toNat < 256 by omega, if_true, Option.getD_some]
  | i + 1, hi, hx => by
    rw [dmAfter_succ]
    have hne : s.getD i 0 ≠ x := by
      intro h; apply hx
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.mem_append, List.mem_singleton]
      right; rw [← h]; simp [List.getD, List.getElem?_eq_getElem (show i < s.length by omega)]
    have hne' : (s.getD i 0).toNat ≠ x.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
    have key : ((dmAfter s i).set (s.getD i 0).toNat (W8 (i : Int)))[x.toNat]? =
        (dmAfter s i)[x.toNat]? := List.getElem?_set_ne hne'
    rw [List.getD_eq_getElem?_getD, key, ← List.getD_eq_getElem?_getD]
    exact dmAfter_free s x i (by omega) (fun h => hx (List.take_subset_take_left _ (by omega) h))

end base64
end EtcdGrove
end Perennial
