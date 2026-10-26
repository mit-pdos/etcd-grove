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

theorem utf8.acceptTable_lookup [FfiSyntax] (k : Nat) (hk : k < 16) :
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

end EtcdGrove
end Perennial
