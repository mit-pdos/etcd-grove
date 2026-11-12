/-
A page at a location, as the Go code sees it (U0b of `notes/bbolt-proof-plan.md`): the `Inode`
values `common.ReadInodeFromPage` builds from the page at `p` (their key and value slices point
into the page), and what it needs of the page's bytes. Shared by `internal/common`'s
`ReadInodeFromPage` spec (U1 proves it) and the specs of `node.read`/`Bucket.node` (U7) and the
read path (U6).
-/
module

public import Proof.go_etcd_io.bbolt.Model.Page

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt.internal.common

section pageAt
variable [GooseExts]

/-- The byte slice of the `n` bytes at `l` (`UnsafeByteSlice(l, 0, 0, n)`: length and capacity
`n`). -/
def bslice (l : Loc) (n : Nat) : GoSlice := slice.mk l (W64 (n : Int)) (W64 (n : Int))

/-- The key slice of element `i` of the page `pg` at `p` (`elem.Key()`: `ksize` bytes `pos` bytes
after the element). -/
def keySliceAt (p : Loc) (pg : List w8) (i : Nat) : GoSlice :=
  if pageFlags pg = leafPageFlag then
    bslice (p +ₗ ((elemOff i + leafPos pg i : Nat) : Int)) (leafKsize pg i)
  else bslice (p +ₗ ((elemOff i + branchPos pg i : Nat) : Int)) (branchKsize pg i)

/-- The value slice of element `i` of the leaf page `pg` at `p` (`elem.Value()`: the `vsize`
bytes after the key). -/
def valSliceAt (p : Loc) (pg : List w8) (i : Nat) : GoSlice :=
  bslice (p +ₗ ((elemOff i + leafPos pg i + leafKsize pg i : Nat) : Int)) (leafVsize pg i)

/-- **Inode `i` of the page `pg` at `p`**, as `ReadInodeFromPage` builds it: a leaf's flags, key
and value (page id `0`); a branch's page id and key (flags `0`, value nil). -/
def pageInodeAt (p : Loc) (pg : List w8) (i : Nat) : Inode :=
  if pageFlags pg = leafPageFlag then
    ⟨(leafElem pg i).flags', W64 0, keySliceAt p pg i, valSliceAt p pg i⟩
  else ⟨W32 0, (branchElem pg i).pgid', keySliceAt p pg i, slice.nil⟩

/-- The inodes of the page `pg` at `p` (`ReadInodeFromPage(p)`). -/
def pageInodesAt (p : Loc) (pg : List w8) : List Inode :=
  (List.range (pageCount pg)).map (pageInodeAt p pg)

/-- The offset (from the page) one past element `i`'s last byte of key or value. -/
def elemEnd (pg : List w8) (i : Nat) : Nat :=
  if pageFlags pg = leafPageFlag then elemOff i + leafPos pg i + leafKsize pg i + leafVsize pg i
  else elemOff i + branchPos pg i + branchKsize pg i

/-- **`ReadInodeFromPage` can read the page `pg`** (it panics otherwise): its elements lie in
`pg`, and every element's key is non-empty and ends, with its value, below `MaxAllocSize` from the
page's start (the slices it makes; their bytes need not be in `pg`). `leafWF`/`branchWF` imply
it for a page with non-empty keys. -/
def pageReadable (pg : List w8) : Prop :=
  elemOff (pageCount pg) ≤ pg.length ∧
  ∀ i < pageCount pg,
    0 < (if pageFlags pg = leafPageFlag then leafKsize pg i else branchKsize pg i) ∧
    elemEnd pg i ≤ maxAllocSize

/-- **Every element of `pg` lies inside its bytes** (U7 fix: `node.read`'s inodes are then the
page's entries; `pageReadable` bounds them by `MaxAllocSize` only). `leafWF`/`branchWF` give it
(`leafWF_elemsIn`, `branchWF_elemsIn`). -/
def pageElemsIn (pg : List w8) : Prop := ∀ i < pageCount pg, elemEnd pg i ≤ pg.length

end pageAt

end bbolt
end EtcdGrove
end Perennial
