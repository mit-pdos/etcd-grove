/-
The read path's (U6, `notes/bbolt-proof-plan.md`) cursor positions over a reader's bucket, as
definitions only (pure; `Inv/Tx`'s `boltCurDef` states a reader cursor with them, maintainer R's
U6g item 1): the page a bucket position names (`rPageAt`), the bucket's entries in order (`rEnts`),
and a stack of page references at a position of them (`rPosAt`). Their facts are in `Read/Pos`.
-/
module

public import Proof.go_etcd_io.bbolt.Model.Cursor
public import Proof.go_etcd_io.bbolt.Model.TreeData

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section posDefs
variable [GooseExts]

/-- The page at position `pid` of the reader bucket whose value is `bv` (its inline page at `pp`):
where it is, its bytes. -/
def rPageAt (v : View) (bv : List w8) (pp : Loc) (pid : Nat) : Option (Loc × List w8) :=
  if inBucketRoot bv = 0 then (if pid = 0 then some (pp, inlinePage bv) else none)
  else (v.pages !! pid).map fun pg => (pageLoc v pid, pg)

/-- A leaf page's entries, as (leaf, index) pairs. -/
def lEnts (pg : List w8) : List (List w8 × Nat) := (List.range (pageCount pg)).map fun i => (pg, i)

/-- The number of entries of the leaves `L`. -/
def entCount (L : List (List w8)) : Nat := (L.flatMap lEnts).length

/-- The entries below the children before `j` of the branch page `pg` (fuel `n`). -/
def entsBefore (P : Pages) (n : Nat) (pg : List w8) (j : Nat) : Nat :=
  entCount ((List.range j).flatMap fun c => leavesF n P (branchPgid pg c))

/-- The fuel at a reader bucket's root (`bktLeaves`'). -/
def rFuel (v : View) (bv : List w8) : Nat := if inBucketRoot bv = 0 then 1 else v.pages.size + 1

/-- **The entries of a reader bucket**, in order, as (leaf, index) pairs. -/
def rEnts (v : View) (bv : List w8) : List (List w8 × Nat) := (bktLeaves v.pages bv).flatMap lEnts

/-- Stack element `e` refers to the branch page `pg` at position `pid`, at index `j`. -/
def rBrAt (v : View) (bv : List w8) (pp : Loc) (pid : Nat) (e : elemRef) (pg : List w8) (j : Nat) :
    Prop :=
  inBucketRoot bv ≠ 0 ∧ rPageAt v bv pp pid = some (e.page', pg) ∧ e.node' = null ∧
    pageFlags pg = branchPageFlag ∧ j < pageCount pg ∧ e.index' = W64 (j : Int)

/-- Stack element `e` refers to the leaf page `pg` at position `pid`, at index `i` (at most its
count). -/
def rLfAt (v : View) (bv : List w8) (pp : Loc) (pid : Nat) (e : elemRef) (pg : List w8) (i : Nat) :
    Prop :=
  rPageAt v bv pp pid = some (e.page', pg) ∧ e.node' = null ∧ pageFlags pg = leafPageFlag ∧
    i ≤ pageCount pg ∧ e.index' = W64 (i : Int)

/-- **A stack below position `pid` (fuel `n`) at position `i`** of the entries below it: branch
references down to a leaf reference; `s` is where `next` goes (`i + 1` on an entry, `i` past
the leaf's end). -/
def rPosF (v : View) (bv : List w8) (pp : Loc) : Nat → Nat → List elemRef → Nat → Nat → Prop
  | 0, _, _, _, _ => False
  | _ + 1, _, [], _, _ => False
  | _ + 1, pid, [e], i, s => ∃ pg, rLfAt v bv pp pid e pg i ∧
      s = (if i < pageCount pg then i + 1 else i)
  | n + 1, pid, e :: e' :: es, i, s => ∃ pg j i' s', rBrAt v bv pp pid e pg j ∧
      rPosF v bv pp n (branchPgid pg j) (e' :: es) i' s' ∧
      i = entsBefore v.pages n pg j + i' ∧ s = entsBefore v.pages n pg j + s'

/-- **A reader's cursor stack at position `i` of its bucket's entries** (`rEnts`), `next` going
to `s`. -/
def rPosAt (v : View) (bv : List w8) (pp : Loc) (els : List elemRef) (i s : Nat) : Prop :=
  rPosF v bv pp (rFuel v bv) (inBucketRoot bv) els i s

/-- **An empty reader bucket's cursor** (what `Last` leaves, which `rPosAt` does not cover): the
bucket has no entries and the stack is its root leaf alone, at index `0` or `-1`. -/
def rEmptyAt (v : View) (bv : List w8) (pp : Loc) (els : List elemRef) : Prop :=
  rEnts v bv = [] ∧ ∃ e pg, els = [e] ∧ rPageAt v bv pp (inBucketRoot bv) = some (e.page', pg) ∧
    e.node' = null ∧ pageFlags pg = leafPageFlag ∧ pageCount pg = 0 ∧
    (e.index' = W64 0 ∨ e.index' = W64 (-1))

/-- **A reader cursor's stack at `pos`** (`boltCurDef`'s reader branch): unpositioned, the empty
stack (`Bucket.Cursor`'s); at entry `i`, a stack at `i` (`rPosAt`), past its leaf's end only past
the bucket's last entry (from such a stack mid-bucket Go's `next` returns entry `i`, not `i + 1`;
coordinator's decision for U6i, item 1), or the empty bucket's root leaf at `i = 0`. -/
def rCurPos (v : View) (bv : List w8) (pp : Loc) (els : List elemRef) : Option Nat → Prop
  | none => els = []
  | some i => (∃ s, rPosAt v bv pp els i s ∧ (s = i → (rEnts v bv).length ≤ i)) ∨
      (i = 0 ∧ rEmptyAt v bv pp els)

end posDefs

end bbolt
end EtcdGrove
end Perennial
