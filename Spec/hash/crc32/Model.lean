/-
**CRC-32C (Castagnoli) as a pure function** (the vocabulary of `hash/crc32`'s and `pkg/v3/crc`'s
specs, and the WAL's `WalCodec.crc32c`): `crc32c c p` is `crc32.Update(c, MakeTable(Castagnoli), p)`,
table-driven as Go's `simpleUpdate` computes it over the table of the reflected polynomial
`0x82F63B78`, bitwise (the table's definitions are below, moved from `TrustedCode/hash/crc32.lean` on 2026-11-24, when
the arch hooks became a Go model, `models/hash/crc32/model.go`; the trusted claim is only that
`archUpdateCastagnoli`'s assembly computes it). `slicingTableArr` is `slicingMakeTable`'s eight tables. `crc32cBits` is the bitwise definition, the same on
the standard check vector (`crc32c_check`, `crc32cBits_check`: "123456789" gives `0xE3069283`).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

namespace Perennial
namespace hash.crc32

/-! ## The table (pure) -/

/-- `crc32.Castagnoli` (`crc32.go`): the reversed Castagnoli polynomial. -/
def castagnoliPoly : w32 := 0x82f63b78#32

/-- One reflected shift-xor step of `simplePopulateTable` (`crc32_generic.go`):
`if crc&1 == 1 { crc = (crc >> 1) ^ poly } else { crc >>= 1 }`. -/
def crcBit (poly c : w32) : w32 := if c &&& 1#32 = 1#32 then (c >>> 1) ^^^ poly else c >>> 1

/-- `k` steps of `crcBit`. -/
def crcBits (poly : w32) : Nat → w32 → w32
  | 0, c => c
  | k + 1, c => crcBits poly k (crcBit poly c)

/-- Entry `i` of `simplePopulateTable(poly)`: eight steps from `uint32(i)`. -/
def crcTableEntry (poly : w32) (i : Nat) : w32 := crcBits poly 8 (BitVec.ofNat 32 i)

/-- The 256 entries of `simplePopulateTable(poly)`. -/
def crcTableOf (poly : w32) : List w32 := (List.range 256).map (crcTableEntry poly)

/-- **The Castagnoli table** (what `MakeTable(Castagnoli)` returns a pointer to: `simpleMakeTable`'s,
`castagnoliInitOnce`'s `castagnoliTable`). -/
def castagnoliTableArr : GoArray w32 256 := array.mk 256 (crcTableOf castagnoliPoly)

/-- One byte of `simpleUpdate` over the table `tab`: `tab[byte(crc)^v] ^ (crc >> 8)`. -/
def crcUpdByte (tab : List w32) (c : w32) (v : w8) : w32 :=
  tab.getD (BitVec.ofNat 8 c.toNat ^^^ v).toNat 0#32 ^^^ (c >>> 8)

/-- `simpleUpdate(c, tab, p)`: complemented in and out. -/
def crcUpdate (tab : List w32) (c : w32) (p : List w8) : w32 :=
  ~~~(p.foldl (crcUpdByte tab) (~~~c))

/-- **CRC-32C**: `crc32.Update(c, MakeTable(Castagnoli), p)`. -/
def crc32c (c : w32) (p : List w8) : w32 := crcUpdate (crcTableOf castagnoliPoly) c p

/-- The bitwise CRC-32C: each byte xored into the low bits, then 8 reflected steps. -/
def crc32cBits (c : w32) (p : List w8) : w32 :=
  ~~~(p.foldl (fun c v => crcBits castagnoliPoly 8 (c ^^^ v.zeroExtend 32)) (~~~c))

/-- Entry `i` of table `j` of `slicingMakeTable(poly)` (`crc32_generic.go:60-72`): `8 (j + 1)`
reflected steps from `uint32(i)` (table `0` is `crcTableOf poly`). -/
def slicingEntry (poly : w32) (j i : Nat) : w32 := crcBits poly (8 * (j + 1)) (BitVec.ofNat 32 i)

/-- **The slicing-by-8 table** of `poly` (what `slicingMakeTable(poly)` returns a pointer to). -/
def slicingTableArr (poly : w32) : GoArray (GoArray w32 256) 8 :=
  array.mk 8 ((List.range 8).map fun j => array.mk 256 ((List.range 256).map (slicingEntry poly j)))

/-- The ASCII bytes "123456789". -/
def checkInput : List w8 := [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]

/-- The standard check value of CRC-32C. -/
theorem crc32c_check : crc32c 0#32 checkInput = 0xE3069283#32 := by decide +kernel

theorem crc32cBits_check : crc32cBits 0#32 checkInput = 0xE3069283#32 := by decide +kernel

theorem crc32c_nil (c : w32) : crc32c c [] = c := by
  simp [crc32c, crcUpdate]

theorem crc32c_append (c : w32) (p q : List w8) : crc32c c (p ++ q) = crc32c (crc32c c p) q := by
  simp [crc32c, crcUpdate, List.foldl_append]

end hash.crc32
end Perennial
