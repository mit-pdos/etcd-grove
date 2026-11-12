/-
The tables `first` and `acceptRanges` (`utf8.go`) against `utf8Lead`: for a leading byte
`n ≥ 0x80`, `first[n] & 7` is the sequence's length (`2`, `3`, `4`; anything else: no sequence starts
with `n`) and `acceptRanges[first[n] >> 4]` the range of its second byte. Pure lemmas for
`ValidString.lean`, checked over the 256 bytes.
-/
module

public import Proof.unicode.utf8.Base
public import Proof.unicode.utf8.Valid

@[expose] public section

namespace Perennial
namespace EtcdGrove

/-- `acceptRanges`' entries as pairs `(lo, hi)`. -/
def utf8.acceptPairs : List (w8 × w8) :=
  [(0x80, 0xBF), (0xA0, 0xBF), (0x80, 0x9F), (0x90, 0xBF), (0x80, 0x8F)] ++
    List.replicate 11 (0, 0)

/-- `acceptRanges[k]`, as a pair. -/
def utf8.accPair (k : Nat) : w8 × w8 := utf8.acceptPairs.getD k (0, 0)

theorem utf8.acceptTable_lookup [GooseExts] (k : Nat) (hk : k < 16) :
    utf8.acceptTable[k]? = some ⟨(utf8.accPair k).1, (utf8.accPair k).2⟩ := by
  match k, hk with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl
  | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl
  | 12, _ => rfl | 13, _ => rfl | 14, _ => rfl | 15, _ => rfl
  | _ + 16, h => omega

theorem utf8.firstTable_lookup (n : Nat) (hn : n < 256) :
    utf8.firstTable[n]? = some (utf8.firstEntry n) := by
  simp only [utf8.firstTable, List.getElem?_map, List.getElem?_range hn, Option.map_some]

theorem utf8.firstEntry_hi : ∀ n < 256, (utf8.firstEntry n).toNat / 16 < 16 := by
  decide +kernel

/-- The tables against `utf8Lead`, at a byte `n ≥ 0x80`: `first[n] & 7` is `2`, `3` or `4` exactly
when a sequence starts with `n`, one byte longer than its continuation, and
`acceptRanges[first[n] >> 4]` is its second byte's range. -/
theorem utf8.lead_table : ∀ n < 256, 0x80 ≤ n →
    utf8Lead n = if (utf8.firstEntry n &&& 7).toNat ∈ [2, 3, 4] then
      some ((utf8.firstEntry n &&& 7).toNat - 1,
        (utf8.accPair ((utf8.firstEntry n).toNat / 16)).1.toNat,
        (utf8.accPair ((utf8.firstEntry n).toNat / 16)).2.toNat)
    else none := by
  decide +kernel

/-- `first[n] >> 4`, the index of `acceptRanges`. -/
theorem utf8.shr4 (x : w8) : uint.Z (x >>> W64 4) = ((x.toNat / 16 : Nat) : Int) := by
  simp [uint.Z, Nat.shiftRight_eq_div_pow]

/-- One step of `utf8ValidB` at a byte `b ≥ 0x80`, through the tables: `first[b] & 7` is the
sequence's length and `acceptRanges[first[b] >> 4]` the range of its second byte. -/
theorem utf8.validB_lead (b : w8) (rest : List w8) (h80 : 0x80 ≤ b.toNat) :
    utf8ValidB (b :: rest) =
      (let sz := (utf8.firstEntry b.toNat &&& W8 7).toNat
       let p := utf8.accPair ((utf8.firstEntry b.toNat).toNat / 16)
       if sz = 2 then
         match rest with
         | c1 :: r => (decide (p.1.toNat ≤ c1.toNat) && decide (c1.toNat ≤ p.2.toNat)) && utf8ValidB r
         | _ => false
       else if sz = 3 then
         match rest with
         | c1 :: c2 :: r => (decide (p.1.toNat ≤ c1.toNat) && decide (c1.toNat ≤ p.2.toNat)) &&
             (decide (0x80 ≤ c2.toNat) && decide (c2.toNat ≤ 0xBF)) && utf8ValidB r
         | _ => false
       else if sz = 4 then
         match rest with
         | c1 :: c2 :: c3 :: r => (decide (p.1.toNat ≤ c1.toNat) && decide (c1.toNat ≤ p.2.toNat)) &&
             (decide (0x80 ≤ c2.toNat) && decide (c2.toNat ≤ 0xBF)) &&
             (decide (0x80 ≤ c3.toNat) && decide (c3.toNat ≤ 0xBF)) && utf8ValidB r
         | _ => false
       else false) := by
  have hL := utf8.lead_table b.toNat b.isLt h80
  have h7 : (W8 7 : w8) = 7 := rfl
  rw [h7]
  conv => lhs; unfold utf8ValidB
  rw [ite_eq_right (by omega), hL]
  generalize (utf8.firstEntry b.toNat &&& 7).toNat = sz
  generalize utf8.accPair ((utf8.firstEntry b.toNat).toNat / 16) = p
  by_cases h2 : sz = 2
  · subst h2
    rcases rest with _ | ⟨c1, r⟩ <;> rfl
  by_cases h3 : sz = 3
  · subst h3
    rcases rest with _ | ⟨c1, _ | ⟨c2, r⟩⟩ <;> rfl
  by_cases h4 : sz = 4
  · subst h4
    rcases rest with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, r⟩⟩⟩ <;> rfl
  have hn : sz ∉ [2, 3, 4] := by simp; omega
  simp only [hn, h2, h3, h4, ↓reduceIte]

end EtcdGrove
end Perennial
