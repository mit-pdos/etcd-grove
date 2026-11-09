/-
# etcd's interval tree (`pkg/v3/adt`): the vocabulary (batch 3f)

A red-black interval tree (`interval_tree.go`) whose entries are intervals of **affine** keys
(`StringAffineComparable`, `BytesAffineComparable`: the empty key is `+∞`) with a value of any
type. Its users: mvcc's watcher groups (string keys: `watcherGroup.add/delete/contains/
watcherSetByKey`, batch 3f), the auth store's permission cache (byte keys: `Insert`, `Intersects`,
`Contains`, batch 3d), the gRPC layer's duplicate-key check (string keys: `checkIntervals`, `Insert`,
`Intersects`, `Union`, batch 2a). (The gRPC proxy's cache uses it too; not verified.)

## The model (transparent)

* Keys are Go strings (`GoString`, a byte slice's contents for the bytes comparable) under the
  **affine order** `affCmp` (`""` the top); an interval is a pair `IvlS = (begin, end)`,
  `[begin, end)`; `ivlMem i k`: `k` is in it. `ivlCmp` is `Interval.Compare` (`0`: they overlap),
  `ivlLt` the tree's order (by begin, then by end).
* **The tree's contents** are a list of entries `Entry = (interval, value)` in the tree's order,
  equal intervals allowed (`Insert` never checks), in insertion order among equals (`ivtInsert`:
  `Insert` descends right on equal intervals; rotations and the successor-based `Delete` keep the
  in-order sequence). `stab q L` the entries overlapping `q`, in order.

## Resources

* `Cmp`: which comparable a tree's keys are (`str`, `bytes`); `keyAt c dq v k` (transparent): the
  Go value `v` holds the key `k` (a string: `v = #k`; a byte slice: its contents, read-only once in a
  tree). `Cmp.ivl c vb ve` the Go `Interval` of two key values.
* **`ivt c t L dq`** (opaque; fractional): the tree at `t` (a `*intervalTree`, the dynamic type of
  `NewIntervalTree`'s result) holds the entries `L` over keys of kind `c`, at `dq` (the writes,
  `Insert`/`Delete`/`Union`'s receiver, take it whole; the reads any fraction or `DFrac.discard`).
  Intended realization: the tree struct, the sentinel, the nodes from the root holding a red-black
  tree (`Internal.lean`'s `RbT`) whose in-order list is `L`, each node's `max` the largest end of its
  subtree, the count `L.length` (below `ivtCountMax`, so `count++` does not wrap: `Stab` reads
  `count == 0` as empty). Laws: `ivt_fractional`, `ivt_agree`, `ivt_persist` (a built tree made
  read-only: the auth store's caches are never modified), `ivt_sorted` (the entries are in the
  tree's order).
* `ivAt c p dq z` (transparent): `p` points to an `IntervalValue` (a node's `iv` field: `Find`'s and
  `Stab`'s results, `Visit`'s visitor's argument) holding the entry `z`, at `dq`: lent by the tree,
  given back by a wand (`Delete` copies a successor's `iv` into the deleted node, so it is not
  read-only for good).
* `ivVisitorOk c dq Q ok ivv I J` (transparent): the contract of a `Visit` callback.

## Requirement snippets

`examples/specreq/adt/`: `watchers.go` (the watcher group's use: `Find` then add to the set,
`Insert`, `Stab` of a point, `Intersects`, `Delete`), `perms.go` (the auth cache: `Insert` of byte
intervals and points, `Contains`, `Intersects` on a read-only tree), `dups.go` (`checkIntervals`:
`Union` of a nested level's deletes, `Intersects` of a point).
-/
module

public import GeneratedProof.go_etcd_io.etcd.pkg.v3.adt
public import Spec.PkgInit.go_etcd_io.etcd.pkg.v3.adt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Adt

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt
open Classical

/-! ## The affine order and intervals (pure) -/

/-- `StringAffineComparable.Compare` (and `BytesAffineComparable.Compare` of the slices'
contents): `""` is the top. -/
def affCmp (a b : GoString) : Int :=
  if a = go!"" then (if b = go!"" then 0 else 1) else if b = go!"" then -1
  else if go.GoStringLt a b then -1 else if go.GoStringLt b a then 1 else 0

/-- The strict affine order. -/
def affLt (a b : GoString) : Prop := a ≠ go!"" ∧ (b = go!"" ∨ go.GoStringLt a b)

/-- An affine interval `[begin, end)`. -/
abbrev IvlS := GoString × GoString

/-- `Interval.Compare` of `x` against `y`: `-1` if `x` is left of `y`, `1` if right, `0` if they
overlap. -/
def ivlCmp (x y : IvlS) : Int :=
  if affCmp x.1 y.1 < 0 ∧ affCmp x.2 y.1 ≤ 0 then -1 else if affCmp x.1 y.2 ≥ 0 then 1 else 0

/-- The tree's order on intervals: by begin, then end. -/
def ivlLt (x y : IvlS) : Prop :=
  affCmp x.1 y.1 < 0 ∨ (affCmp x.1 y.1 = 0 ∧ affCmp x.2 y.2 < 0)

/-- The key `k` is in the interval `i`. -/
def ivlMem (i : IvlS) (k : GoString) : Prop := ¬ affLt k i.1 ∧ affLt k i.2

/-- The point interval of a key, `[k, k ++ "\x00")` (`NewStringAffinePoint`,
`NewBytesAffinePoint`). -/
def pointOf (k : GoString) : IvlS := (k, k ++ [W8 0])

/-- A query `Visit`, `Stab` and `Contains` answer exactly: its begin is the top (it overlaps
nothing) or below its end. (On an empty finite query, `e ≤ b ≠ ""`, `visit`'s pruning on the
subtrees' `max` may miss entries.) -/
def IvlS.queryOk (q : IvlS) : Prop := q.1 = go!"" ∨ affLt q.1 q.2

/-- The largest count `Insert` keeps exact: `count` is a Go `int`. -/
def ivtCountMax : Nat := 2 ^ 63 - 1

section entries
variable [GooseExts]

/-- An entry of the tree: an interval and the value stored with it (`any`). -/
abbrev Entry := IvlS × GoInterface

/-- `Insert`: before the first entry it is below in the tree's order (so after the equal ones). -/
def ivtInsert (z : Entry) : List Entry → List Entry
  | [] => [z]
  | w :: ws => if ivlLt z.1 w.1 then z :: w :: ws else w :: ivtInsert z ws

/-- The entries overlapping the query `q`, in the tree's order. -/
def stab (q : IvlS) (L : List Entry) : List Entry :=
  L.filter fun z => decide (ivlCmp q z.1 = 0)

/-- The entries are in the tree's order (equal intervals allowed). -/
def IvSorted (L : List Entry) : Prop := L.Pairwise fun a b => ¬ ivlLt b.1 a.1

end entries

/-! ## Key values (Go) -/

/-- **The comparable a tree's keys are**: `StringAffineComparable` or `BytesAffineComparable`. -/
inductive Cmp where
  | str
  | bytes

section keys
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- The comparable's dynamic type. -/
def Cmp.ty : Cmp → go.GoType
  | .str => StringAffineComparable.ty
  | .bytes => BytesAffineComparable.ty

/-- **The Go value `v` holds the key `k`** at `dq`: a string `#k`; a byte slice with contents `k`. -/
def keyAt : Cmp → DFrac → val → GoString → IProp GF
  | .str, _, v, k => iprop(⌜v = #k⌝)
  | .bytes, dq, v, k => iprop(∃ s : GoSlice, ⌜v = #s⌝ ∗ s ↦*{dq} k)

/-- The Go `Interval` of two key values. -/
def Cmp.ivl (c : Cmp) (vb ve : val) : Interval :=
  { Begin' := interface.mkOk c.ty vb, End' := interface.mkOk c.ty ve }

/-- `NewStringAffineInterval(b, e)`. -/
def strIvl (b e : GoString) : Interval := Cmp.str.ivl #b #e

/-- **An `IntervalValue` at `p` holds the entry `z`**, at `dq`: two key values holding the entry's
keys (read-only) and the value. -/
def ivAt (c : Cmp) (p : Loc) (dq : DFrac) (z : Entry) : IProp GF :=
  iprop(∃ vb ve : val, p ↦{dq} ({ Ivl' := c.ivl vb ve, Val' := z.2 } : IntervalValue) ∗
    keyAt c DFrac.discard vb z.1.1 ∗ keyAt c DFrac.discard ve z.1.2)

/-- **The tree at `t` holds the entries `L`** over keys of kind `c`, at `dq` (see the header). -/
opaque ivt (c : Cmp) (t : Loc) (L : List Entry) (dq : DFrac) : IProp GF := iprop(True)

/-- **The contract of a `Visit` callback `ivv`** over the visited entries `Q` (the stabbed entries
in order) with the client's loop state: `I acc` after visiting `acc` and continuing, `J acc` after
stopping at its last. Called once per visited entry, in order, with the entry lent at the tree's
`dq`; `ok`: the visit is exact (`IvlS.queryOk`), else the visited entries are only a sublist. -/
def ivVisitorOk (c : Cmp) (dq : DFrac) (Q : List Entry) (ok : Prop) (ivv : GoFunc)
    (I J : List (Loc × Entry) → IProp GF) : IProp GF :=
  iprop(□ ∀ (acc : List (Loc × Entry)) (p : Loc) (z : Entry),
    ⌜List.Sublist (acc.map Prod.snd ++ [z]) Q ∧ (ok → acc.map Prod.snd ++ [z] <+: Q)⌝ -∗
    {{ I acc ∗ ivAt c p dq z }}
      (App (Val #ivv) (Val #p))
    {{ (b : Bool), RET #b; ivAt c p dq z ∗
        (if b then I (acc ++ [(p, z)]) else J (acc ++ [(p, z)])) }})

/-! ## Laws -/

/-- The tree's ownership splits and joins by fractions; two parts agree. -/
def ivt_fractional.spec : Prop :=
  (∀ c t L (d1 d2 : DFrac), ivt (GF := GF) c t L (d1 • d2) ⊣⊢ ivt c t L d1 ∗ ivt c t L d2) ∧
  (∀ c t (L1 L2 : List Entry) (d1 d2 : DFrac), ivt (GF := GF) c t L1 d1 ∗ ivt c t L2 d2 ⊢ ⌜L1 = L2⌝)

/-- A tree made read-only for good (`DFrac.discard`, persistent). -/
def ivt_persist.spec : Prop :=
  (∀ c t L dq, ivt (GF := GF) c t L dq ⊢ |==> ivt c t L DFrac.discard) ∧
  (∀ c t L, Persistent (ivt (GF := GF) c t L DFrac.discard))

/-- The entries are in the tree's order, and fewer than `ivtCountMax`. -/
def ivt_sorted.spec : Prop := ∀ c t L dq,
  ivt (GF := GF) c t L dq ⊢ ⌜IvSorted L ∧ L.length ≤ ivtCountMax⌝

/-- A tree's key values are persistent (a node keeps its keys read-only). -/
def keyAt_persistent.spec : Prop := ∀ c v k, Persistent (keyAt (GF := GF) c DFrac.discard v k)

end keys

end Adt
end EtcdGrove
end Perennial
