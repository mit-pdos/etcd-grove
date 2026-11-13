/-
**CRC-32C (Castagnoli) as a pure function** (the vocabulary of `hash/crc32`'s and `pkg/v3/crc`'s
specs, and the WAL's `WalCodec.crc32c`): `crc32c c p` is `crc32.Update(c, MakeTable(Castagnoli), p)`,
table-driven as the trusted model computes it (`LinuxFs/TrustedCode/hash/crc32.lean`, the table of
the reflected polynomial `0x82F63B78`, bitwise). `crc32cBits` is the bitwise definition, the same on
the standard check vector (`crc32c_check`, `crc32cBits_check`: "123456789" gives `0xE3069283`).
-/
module

public import LinuxFs.TrustedCode.hash.crc32

@[expose] public section

namespace Perennial
namespace hash.crc32

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
