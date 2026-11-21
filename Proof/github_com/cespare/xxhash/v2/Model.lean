/-
The 64-bit xxHash (XXH64, seed 0) of a byte string, as `github.com/cespare/xxhash/v2` v2.3.0
computes it (the version etcd's `server/go.mod` pins, through prometheus's client_golang): a pure
model, so that statements can name the hash a Go function computes (prometheus's descriptor IDs,
`EtcdGrove.prometheus.descId`). No Go code is translated or proved here.

`sum64 b` follows `Sum64` of `xxhash_other.go` (the pure-Go build of the same function the
assembly of `xxhash_amd64.s` implements), step by step: the four-lane rounds over 32-byte blocks
when `len(b) >= 32`, the length, the 8-byte, 4-byte and 1-byte tails, the avalanche. A `Digest`
written in pieces (`New`, `Write`/`WriteString`, `Sum64`, what prometheus's `NewDesc` does) gives
`Sum64` of the concatenation (the package's documentation; `xxhash_test.go` checks it). The test
vectors below were computed with the Go package (`/shared/tmp/promdeep/vectors`, 2026-11-20) and
are checked by the kernel: lengths 0, 1, 3, 4, 8, 11, 31 and 71 cover every branch (no block, the
block loop, each tail).
-/
module

public import Perennial.Std.ByteString

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace xxhash

def prime1 : w64 := 11400714785074694791#64
def prime2 : w64 := 14029467366897019727#64
def prime3 : w64 := 1609587929392839161#64
def prime4 : w64 := 9650029242287828579#64
def prime5 : w64 := 2870177450012600261#64

/-- `bits.RotateLeft64(x, k)`. -/
def rol (k : Nat) (x : w64) : w64 := x.rotateLeft k

/-- The little-endian unsigned integer of the first `k` bytes of `b` (`u64`: `k = 8`, `u32`:
`k = 4`, `binary.LittleEndian`), zero-extended to 64 bits. -/
def le (k : Nat) (b : List w8) : w64 :=
  (b.take k).foldr (fun byte acc => (acc <<< 8) ||| byte.zeroExtend 64) 0

/-- `round(acc, input)`. -/
def round (acc input : w64) : w64 := rol 31 (acc + input * prime2) * prime1

/-- `mergeRound(acc, val)`. -/
def mergeRound (acc val : w64) : w64 := (acc ^^^ round 0 val) * prime1 + prime4

/-- The loop over 32-byte blocks (`fuel` bounds it: `len(b)` suffices), returning the lanes and
what is left (fewer than 32 bytes). -/
def blocks : Nat → List w8 → w64 × w64 × w64 × w64 → (w64 × w64 × w64 × w64) × List w8
  | 0, b, v => (v, b)
  | fuel + 1, b, (v1, v2, v3, v4) =>
    if 32 ≤ b.length then
      blocks fuel (b.drop 32)
        (round v1 (le 8 b), round v2 (le 8 (b.drop 8)), round v3 (le 8 (b.drop 16)),
          round v4 (le 8 (b.drop 24)))
    else ((v1, v2, v3, v4), b)

/-- The loop over 8-byte words (`fuel`: `len(b)` suffices), returning the hash and what is left
(fewer than 8 bytes). -/
def words : Nat → List w8 → w64 → w64 × List w8
  | 0, b, h => (h, b)
  | fuel + 1, b, h =>
    if 8 ≤ b.length then words fuel (b.drop 8) (rol 27 (h ^^^ round 0 (le 8 b)) * prime1 + prime4)
    else (h, b)

/-- The 4-byte word (if there are four bytes left), then the single bytes. -/
def rest (b : List w8) (h : w64) : w64 :=
  let hb : w64 × List w8 :=
    if 4 ≤ b.length then (rol 23 (h ^^^ le 4 b * prime1) * prime2 + prime3, b.drop 4) else (h, b)
  hb.2.foldl (fun h byte => rol 11 (h ^^^ byte.zeroExtend 64 * prime5) * prime1) hb.1

/-- The final mix. -/
def avalanche (h : w64) : w64 :=
  let h := h ^^^ (h >>> 33)
  let h := h * prime2
  let h := h ^^^ (h >>> 29)
  let h := h * prime3
  h ^^^ (h >>> 32)

/-- **`xxhash.Sum64(b)`**: XXH64 of `b` with seed 0. -/
def sum64 (b : List w8) : w64 :=
  let hb : w64 × List w8 :=
    if 32 ≤ b.length then
      let vb := blocks b.length b (prime1 + prime2, prime2, 0, -prime1)
      let v := vb.1
      let h := rol 1 v.1 + rol 7 v.2.1 + rol 12 v.2.2.1 + rol 18 v.2.2.2
      (mergeRound (mergeRound (mergeRound (mergeRound h v.1) v.2.1) v.2.2.1) v.2.2.2, vb.2)
    else (prime5, b)
  let wb := words hb.2.length hb.2 (hb.1 + BitVec.ofNat 64 b.length)
  avalanche (rest wb.2 wb.1)

/-! Test vectors (Go: `xxhash.Sum64String`). -/

theorem sum64_empty : sum64 go!"" = 0xef46db3751d8e999#64 := by decide +kernel
theorem sum64_a : sum64 go!"a" = 0xd24ec4f1a98c6e5b#64 := by decide +kernel
theorem sum64_abc : sum64 go!"abc" = 0x44bc2cf5ad770999#64 := by decide +kernel
theorem sum64_abcd : sum64 go!"abcd" = 0xde0327b0d25d92cc#64 := by decide +kernel
theorem sum64_abcdefgh : sum64 go!"abcdefgh" = 0x3ad351775b4634b7#64 := by decide +kernel
theorem sum64_abcdefghijk : sum64 go!"abcdefghijk" = 0x814e257441cf78e0#64 := by decide +kernel
theorem sum64_keys_total :
    sum64 (go!"etcd_debugging_mvcc_keys_total" ++ [255#8]) = 0x6f040a217f98b36f#64 := by
  decide +kernel
theorem sum64_71 :
    sum64 go!"0123456789012345678901234567890123456789012345678901234567890123456789x" =
      0x26e8b64301de3aec#64 := by
  decide +kernel

end xxhash
end EtcdGrove
end Perennial
