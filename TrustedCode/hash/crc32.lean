/-
Trusted model of `hash/crc32` (namespace of the generated package; project etcd, `Code/hash/crc32.toml`):
the three hooks of the Castagnoli fast path, `archAvailableCastagnoli`, `archInitCastagnoli` and
`archUpdateCastagnoli` (`crc32_amd64.go`, the target `notes/` and the tests build for: linux/amd64,
go1.27.3), whose Go is SSE4.2 assembly that goose cannot translate. Everything else that `MakeTable`,
`Update`, `New` and the digest reach is translated with its body: the package state
(`castagnoliTable`, `castagnoliTable8`, `updateCastagnoli`, `haveCastagnoli`, `IEEETable`), the once
`castagnoliInitOnce` that sets it up, `update`'s dispatch, `simpleUpdate`, and the slicing-by-8 code.
So `MakeTable(Castagnoli)` returns Go's one shared table, and which path `update` takes is decided by
the translated code (etcd-grove#14; until 2026-11-22 `MakeTable` and `update` were trusted, with a
fresh table per `MakeTable`).

`crc32.go` states the hooks' contract (its comment "The interface that they implement"):
`archAvailableCastagnoli()` reports whether the fast path exists; `archInitCastagnoli()` may be
called only if it does; `archUpdateCastagnoli(crc, p)` only after `archInitCastagnoli()`, and it
updates the CRC-32C `crc` with `p`. The translated code calls them only so (`castagnoliInitOnce`,
`crc32.go:83-98`: `archInitCastagnoli` and `updateCastagnoli = archUpdateCastagnoli` only after
`archAvailableCastagnoli()` returned true, and `update` calls `updateCastagnoli` only once
`haveCastagnoli` is set, after both). Each hook's docstring says why its model covers Go's.

What stays trusted: that the assembly computes the same CRC-32C as Go's portable code, on every CPU
where it is enabled (checked by Go's own `TestArchCastagnoli`, `crc32_test.go:271`, which compares
`archUpdateCastagnoli` with `simpleUpdate` over `simpleMakeTable(Castagnoli)` on every length up to
and beyond its cutoffs, and by `examples/stdlib/crc32/crc32_test.go` against the model's values).

The pure definitions below (the polynomial, the table) are the specs' vocabulary, not models.
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

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

section code
variable [GooseExts] [GoGlobalContext]

/-- `archAvailableCastagnoli() bool` (`crc32_amd64.go`: `return cpu.X86.HasSSE42`): **an arbitrary
`bool`**. Go's is a property of the CPU, fixed for the process; the model allows either answer at
each call, so it covers every CPU (with or without SSE4.2, and the other architectures' files, whose
answer is also fixed: `crc32_otherarch.go`'s `false`). Only `castagnoliInitOnce` calls it, once per
process. -/
noncomputable def archAvailableCastagnoli.impl : val :=
  λ: <>, ArbitraryInt =⟨go.int64⟩ #(W64 0)

/-- `archInitCastagnoli()` (`crc32_amd64.go`): **a no-op**. Go's panics unless SSE4.2 is present,
which the translated code rules out (it calls it only after `archAvailableCastagnoli()` returned
true), and otherwise fills `castagnoliSSE42TableK1`/`K2`, package variables that only
`archUpdateCastagnoli`'s Go reads (nothing translated names them; they are not translated). Its loop
calls only `castagnoliSSE42` on a zeroed stack buffer, so it reads and writes nothing else and
returns. The model's `archUpdateCastagnoli` reads no table, so skipping the fill changes no result. -/
noncomputable def archInitCastagnoli.impl : val :=
  λ: <>, #()

/-- `archUpdateCastagnoli(crc uint32, p []byte) uint32` (`crc32_amd64.go`: SSE4.2 `CRC32`
instructions, three streams combined through the K1/K2 tables): **`crc32c crc p`**, the CRC-32C of
Go's portable code, computed here by that code itself,

```go
	return simpleUpdate(crc, simpleMakeTable(Castagnoli), p)
```

(the translated `simpleUpdate` and `simpleMakeTable`; the table is a fresh allocation that nothing
else sees). Go's panics unless SSE4.2 is present, which the translated code rules out (it is called
only through `updateCastagnoli`, set to it only after `archAvailableCastagnoli()` returned true). It
reads `p` (as Go's assembly does) and nothing the caller can see changes. That the assembly computes
this function is the trusted claim of this file (the header: Go's `TestArchCastagnoli`). -/
noncomputable def archUpdateCastagnoli.impl : val :=
  λ: "crc" "p",
    let: "t" := (FuncResolve go!"hash/crc32.simpleMakeTable" []) #() #castagnoliPoly in
    (FuncResolve go!"hash/crc32.simpleUpdate" []) #() "crc" "t" "p"

end code
end hash.crc32

end Perennial
