/-
Pages as bytes: what bbolt's code reads out of a page through `unsafe.Pointer`
(`internal/common/page.go`), as functions of the page's bytes, and when a page is
well-formed (every element and every key and value inside the page).

A page is the bytes `pg` from its start (its header, then its elements, then the keys and
values they point to; an overflowing page runs over `1 + overflow` pages of the file). The
header is `id` (8 bytes), `flags` (2), `count` (2), `overflow` (4); element `i` is the 16
bytes at `16 + 16 i`: a leaf element is `flags`, `pos`, `ksize`, `vsize` (4 each), a branch
element `pos`, `ksize` (4 each) and `pgid` (8); an element's key is the `ksize` bytes `pos`
after the element, and a leaf element's value the `vsize` bytes after its key.

bbolt does not check a page it reads from the file (only the meta pages' checksum), so its
safety rests on the file being well-formed: these predicates are the database invariant's.
-/
module

public import Perennial.Golang.Theory.Bytes

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace bbolt

/-- The little-endian number of the `n` bytes at `off` (0 past the end). -/
def leAt (pg : List w8) (off n : Nat) : Nat := (leInt ((pg.drop off).take n)).toNat

def pageId (pg : List w8) : Nat := leAt pg 0 8
def pageFlags (pg : List w8) : Nat := leAt pg 8 2
def pageCount (pg : List w8) : Nat := leAt pg 10 2
def pageOverflow (pg : List w8) : Nat := leAt pg 12 4

/-- The offset of element `i`. -/
def elemOff (i : Nat) : Nat := 16 + 16 * i

def leafFlags (pg : List w8) (i : Nat) : Nat := leAt pg (elemOff i) 4
def leafPos (pg : List w8) (i : Nat) : Nat := leAt pg (elemOff i + 4) 4
def leafKsize (pg : List w8) (i : Nat) : Nat := leAt pg (elemOff i + 8) 4
def leafVsize (pg : List w8) (i : Nat) : Nat := leAt pg (elemOff i + 12) 4
def branchPos (pg : List w8) (i : Nat) : Nat := leAt pg (elemOff i) 4
def branchKsize (pg : List w8) (i : Nat) : Nat := leAt pg (elemOff i + 4) 4
def branchPgid (pg : List w8) (i : Nat) : Nat := leAt pg (elemOff i + 8) 8

/-- The `n` bytes at `off`. -/
def bytesAt (pg : List w8) (off n : Nat) : List w8 := (pg.drop off).take n

def leafKey (pg : List w8) (i : Nat) : List w8 :=
  bytesAt pg (elemOff i + leafPos pg i) (leafKsize pg i)
def leafValue (pg : List w8) (i : Nat) : List w8 :=
  bytesAt pg (elemOff i + leafPos pg i + leafKsize pg i) (leafVsize pg i)
def branchKey (pg : List w8) (i : Nat) : List w8 :=
  bytesAt pg (elemOff i + branchPos pg i) (branchKsize pg i)

def branchPageFlag : Nat := 0x01
def leafPageFlag : Nat := 0x02
def metaPageFlag : Nat := 0x04
def freelistPageFlag : Nat := 0x10

/-- A leaf page's elements, keys and values lie inside its `len` bytes, below
`MaxAllocSize` (what `UnsafeByteSlice` requires). -/
def leafWF (pg : List w8) (len : Nat) : Prop :=
  len ≤ pg.length ∧ elemOff (pageCount pg) ≤ len ∧
  ∀ i < pageCount pg,
    elemOff i + leafPos pg i + leafKsize pg i + leafVsize pg i ≤ len ∧
    leafPos pg i + leafKsize pg i + leafVsize pg i ≤ 2147483647

/-- A branch page's elements and keys lie inside its `len` bytes, and its children are
below the high-water mark `hwm`. -/
def branchWF (pg : List w8) (len hwm : Nat) : Prop :=
  len ≤ pg.length ∧ elemOff (pageCount pg) ≤ len ∧
  ∀ i < pageCount pg,
    elemOff i + branchPos pg i + branchKsize pg i ≤ len ∧
    branchPos pg i + branchKsize pg i ≤ 2147483647 ∧ branchPgid pg i < hwm

/-- A leaf page's contents: its elements' flags, keys and values. -/
def leafItems (pg : List w8) : List (Nat × List w8 × List w8) :=
  (List.range (pageCount pg)).map fun i => (leafFlags pg i, leafKey pg i, leafValue pg i)

/-- A branch page's contents: its elements' keys and children. -/
def branchItems (pg : List w8) : List (List w8 × Nat) :=
  (List.range (pageCount pg)).map fun i => (branchKey pg i, branchPgid pg i)

end bbolt
end EtcdGrove
end Perennial
