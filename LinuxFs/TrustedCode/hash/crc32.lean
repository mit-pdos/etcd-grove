/-
Trusted model of `hash/crc32` (namespace of the generated package; project etcd's part `LinuxFs/`,
`LinuxFs/Code/hash/crc32.toml`): `MakeTable` and `Update`, what `pkg/v3/crc` and the WAL call
(`crcTable = crc32.MakeTable(crc32.Castagnoli)`, `crc32.Update(d.crc, d.tab, p)`). **Pending the
user's review** (a trusted model, 2026-11-13; `notes/perennial-changes.md`, "hash/crc32").

Go computes the Castagnoli CRC with SSE4.2 assembly (`crc32_amd64.go`, `castagnoliSSE42`), which
goose cannot translate. The model is Go's portable code (`crc32_generic.go`): the table of
`simplePopulateTable(Castagnoli)` (each byte's 8 reflected shift-xor steps), and `Update` as
`simpleUpdate` reading the table it is given. Go's arch path and its slicing-by-8 path compute the
same function of a Castagnoli table as `simpleUpdate` does (they are its optimizations; `go test
hash/crc32` checks them against `simpleUpdate`). Checked against Go on test vectors and on the
whole table by `examples/stdlib/crc32/crc32_test.go` (go1.27.3, linux/amd64).

Deviations from Go, outside what any proof here may use:
- `MakeTable(poly)` of a polynomial other than `Castagnoli` panics (Go builds that polynomial's
  table): a program calling it is never proved panic-free, so the model covers no such run.
- `MakeTable(Castagnoli)` allocates a fresh table holding the Castagnoli table; Go returns the
  package's one `castagnoliTable` (the same pointer at every call). A program comparing the
  pointers of two calls' results is outside the model's faithful range (the WAL calls it once, in
  its package initializer). Go never writes the table after it is built; the model's is read-only
  for good in the specs (`tab ↦□ castagnoliTableArr`).
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

/-- **The Castagnoli table** (what `MakeTable(Castagnoli)` returns a pointer to). -/
def castagnoliTableArr : GoArray w32 256 := array.mk 256 (crcTableOf castagnoliPoly)

section code
variable [GooseExts] [GoGlobalContext]

/-- `MakeTable(poly *Table)` (`crc32.go`): for `Castagnoli`, a pointer to a table holding
`castagnoliTableArr` (freshly allocated: the file header); any other polynomial panics (the file
header). The table's type is `crc32.Table`, `[256]uint32`, allocated at its underlying type. -/
noncomputable def MakeTable.impl : val :=
  λ: "poly",
    if: "poly" =⟨go.uint32⟩ #castagnoliPoly then
      GoAlloc (go.ArrayType 256 go.uint32) #castagnoliTableArr
    else Panic "crc32 model: MakeTable of a polynomial other than Castagnoli"

/-- `Update(crc uint32, tab *Table, p []byte) uint32` (`crc32.go`), as `simpleUpdate`
(`crc32_generic.go`):

```go
	crc = ^crc
	for _, v := range p {
		crc = tab[byte(crc)^v] ^ (crc >> 8)
	}
	return ^crc
```

the loop as a recursion on `p[1:]`. -/
noncomputable def Update.impl : val :=
  λ: "crc" "tab" "p",
    (rec: "loop" "c" "p" :=
      let: "n" := (FuncResolve go.len [go.GoType.SliceType go.byte]) #() "p" in
      if: "n" =⟨go.int⟩ #(W64 0) then ⟨go.uint32⟩^ "c"
      else
        let: "v" := ![go.byte] (IndexRef (go.GoType.SliceType go.byte) ("p", #(W64 0))) in
        let: "i" := Convert go.byte go.int ((Convert go.uint32 go.byte "c") ^⟨go.byte⟩ "v") in
        let: "e" := ![go.uint32] (IndexRef (go.ArrayType 256 go.uint32) ("tab", "i")) in
        "loop" ("e" ^⟨go.uint32⟩ ("c" >>⟨go.uint32⟩ #(W64 8)))
          (Slice (go.GoType.SliceType go.byte) (("p", #(W64 1)), "n")))
      (⟨go.uint32⟩^ "crc") "p"

end code
end hash.crc32

end Perennial
