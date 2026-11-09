/-
# The k8s fork of google/btree: the vocabulary (batch 1g)

`k8s.io/utils/third_party/forked/golang/btree` (`btree.go`): a copy-on-write B-tree of items of a
Go type `T`, ordered by a `LessFunc[T]`. Its users: etcd's cache (`cache/store.go`,
`cache/snapshot.go`: `New`, `ReplaceOrInsert`, `Delete`, `Get`, `AscendGreaterOrEqual`, `AscendRange`,
`Clone`) and etcd's mvcc key index (`server/v3/storage/mvcc/index.go`, batch 3e: `New`, `Get` whose
item it mutates in place, `ReplaceOrInsert`, `Delete`, `Clone`, `Ascend`, `AscendGreaterOrEqual`
stopped early, `Len`, readers under an `RWMutex`'s read lock at fractions), and Kubernetes'
apiserver cacher (`k8s.io/apiserver/pkg/storage/cacher/store/{snapshotter,btree}.go`: a tree of
frozen clones, `DescendLessOrEqual`, `Min`, `DeleteMin`, `Clear`); every other exported
method has a spec too (PRINCIPLES, "A smaller API is not a narrower scope": all were verified).

## The model

A tree holds a **sorted map**: a list of entries `(v, k)` (the Go value stored, its key) with
strictly increasing keys (`Sorted`). The order is on **keys** `K`, related to items by a persistent
predicate the client fixes when it creates the tree (`ItemOrder.item v k`; for an ordered Go type
`v = k`, `orderedOrder`; for etcd's cache a `*kvItem` and the string its immutable `key` field
holds). `less` decides the strict total order `ItemOrder.lt` on the keys of the items it is given
(`isLess`). An order on items that is only a strict *weak* order is a strict total order on its
equivalence classes, which is what a client takes as keys.

Departure (PRINCIPLES, "TaDa, not HoCAP"): `ItemOrder.item` is a client predicate parameter of the
tree's predicate. It is the approved kind: persistent, fixed when the tree is created (`New`'s
`isLess`), read only by `less` and the iterators; a client that stores plain values uses
`orderedOrder` (`item v k := ⌜v = k⌝`).

The operations' effects (`mLookup`, `mInsert`, `mDelete`, `removeOp`, `ascRange`, `descRange`) are
transparent: they are the meaning of the specs.

## Resources

* `ownBTree o t dq s` (fractional in `dq`; persistent at `DFrac.discard`): **the tree `t` holds the
  entries `s`**. A write (`ReplaceOrInsert`, `Delete*`, `Clear`, `Clone`, which re-keys `t`'s
  copy-on-write context) takes the whole; a read (`Get`, `Has`, `Len`, `Min`, `Max`, the
  iterations) any fraction. Intended realization (the old `Defs.lean`): `t`'s fields, its
  copy-on-write context (`isCow`, persistent: its free list's mutex and `isLess`), the degree
  `2 ≤ d ≤ 2^62`, `length = |s|`, `Sorted o.lt s`, `allItems o s`, and the root's subtree
  (`ownRoot`, `Internal.lean`), whose nodes are either owned by `t`'s context (fractional
  points-tos) or **frozen**: shared with a clone, never written again (every write copies a node it
  does not own, `mutableFor`), hence persistent. `Clone` gives both trees fresh contexts, so after
  it the two are independent resources over shared frozen nodes.
* `isFreeList f` (persistent): a `FreeList` (its mutex invariant holding the free nodes).
* `isLess o less` (transparent, persistent): the `less` closure's triple.
* `iterProtocol o iter r I` (transparent, persistent): an iterator closure's contract over the
  entries `r` it is to visit, with the caller's state `I` (the visited prefix, and whether it asked
  to stop); `iterDone r I` what an iteration ends with.

## Laws

`ownBTree_sorted`, `ownBTree_items` (what a client reads off the model), `ownBTree_fractional`
(split/join), `ownBTree_persist` (freeze a tree read-only, as the cache does for a snapshot's
clone), `ownBTree_discard_persistent`, `isFreeList_persistent`.

## Requirement snippets

`examples/specreq/btree/mvcc.go`: mvcc's uses (`ReqMutateInPlace`, `ReqFractionalReaders`,
`ReqStopEarly`, `ReqCompactClone`). `examples/specreq/btree/btree.go`: the cache's uses (a sorted map of `*kvItem` by key: insert,
replace, delete, point and range reads, a frozen clone read concurrently with writes to the
original), an ordered tree (`NewOrdered`), and Kubernetes' (`ReqTreeOfSnapshots`: the apiserver
cacher's snapshotter, a tree of frozen clones keyed by resource version, read with
`DescendLessOrEqual` stopped at the first item, trimmed with `Min`/`DeleteMin`, reset with `Clear`;
verify-round A3 completeness F4).
-/
module

public import GeneratedProof.k8s_io.utils.third_party.forked.golang.btree
public import Spec.PkgInit.k8s_io.utils.third_party.forked.golang.btree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BTree

open Iris Iris.BI
open Classical

/-! ## Keys and the sorted-map model -/

/-- A strict total order on keys. -/
structure StrictOrder {K : Type} (lt : K → K → Prop) : Prop where
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  total : ∀ a b, lt a b ∨ a = b ∨ lt b a

section model
variable {V K : Type} (lt : K → K → Prop)

/-- Strictly increasing keys. -/
def Sorted (l : List (V × K)) : Prop :=
  l.Pairwise (fun a b => lt a.2 b.2)

/-- The item with key `k`. -/
def mLookup (s : List (V × K)) (k : K) : Option V :=
  (s.find? (fun e => decide (e.2 = k))).map Prod.fst

/-- `ReplaceOrInsert`: the entry `e` replaces the one with its key, or goes where its key
belongs. -/
def mInsert : List (V × K) → V × K → List (V × K)
  | [], e => [e]
  | x :: xs, e =>
    if lt e.2 x.2 then e :: x :: xs
    else if e.2 = x.2 then e :: xs
    else x :: mInsert xs e

/-- `Delete`: drop the entry with key `k`. -/
def mDelete (s : List (V × K)) (k : K) : List (V × K) :=
  s.filter (fun e => decide (e.2 ≠ k))

/-- The keys an ascending iteration from `start` (inclusive) to `stop` (exclusive) visits;
`none` is no bound. -/
def ascIn (start stop : Option K) (k : K) : Prop :=
  (∀ a, start = some a → ¬ lt k a) ∧ (∀ b, stop = some b → lt k b)

/-- The keys a descending iteration from `start` (inclusive) down to `stop` (exclusive)
visits. -/
def descIn (start stop : Option K) (k : K) : Prop :=
  (∀ a, start = some a → ¬ lt a k) ∧ (∀ b, stop = some b → lt b k)

/-- The entries an ascending iteration visits, in order. -/
def ascRange (s : List (V × K)) (start stop : Option K) : List (V × K) :=
  s.filter (fun e => decide (ascIn lt start stop e.2))

/-- The entries a descending iteration visits, in order. -/
def descRange (s : List (V × K)) (start stop : Option K) : List (V × K) :=
  (s.filter (fun e => decide (descIn lt start stop e.2))).reverse

end model

/-- What `deleteItem` removes: the entry with a key, the smallest, or the largest. -/
inductive Target (K : Type) where
  | key (k : K)
  | min
  | max

/-- The `toRemove` constant `deleteItem` is passed. -/
def Target.code {K : Type} : Target K → w64
  | .key _ => W64 0
  | .min => W64 1
  | .max => W64 2

/-- The entries left, and the item removed (if any). -/
def removeOp {V K : Type} : Target K → List (V × K) → List (V × K) × Option V
  | .key k, s => (mDelete s k, mLookup s k)
  | .min, s => (s.tail, s.head?.map Prod.fst)
  | .max, s => (s.dropLast, s.getLast?.map Prod.fst)

/-! ## How items are ordered -/

/-- **How items are ordered**: a strict total order `lt` on keys, and the persistent relation
`item v k` between an item and its key, fixed when the tree is created. -/
structure ItemOrder (GF : BundledGFunctors) (V K : Type) where
  lt : K → K → Prop
  order : StrictOrder lt
  item : V → K → IProp GF
  item_persistent : ∀ v k, Persistent (item v k)

/-- The order of an ordered Go type (`NewOrdered`, `Less`): items are their own keys. -/
def orderedOrder {GF : BundledGFunctors} {V : Type} (lt : V → V → Prop) (h : StrictOrder lt) :
    ItemOrder GF V V where
  lt := lt
  order := h
  item v k := iprop(⌜v = k⌝)
  item_persistent _ _ := by infer_instance

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- Every entry's item has its key. -/
def allItems {V K : Type} (o : ItemOrder GF V K) (l : List (V × K)) : IProp GF :=
  iprop(□ ∀ e, ⌜e ∈ l⌝ -∗ o.item e.1 e.2)

/-- **`less a b` decides `lt` on the keys of `a` and `b`** (persistent). -/
def isLess {V K : Type} (o : ItemOrder GF V K) (less : GoFunc) : IProp GF :=
  iprop(□ ∀ (a b : V) (ka kb : K),
    {{ o.item a ka ∗ o.item b kb }}
      (App (App (Val #less) (Val #a)) (Val #b))
    {{ (r : Bool), RET #r; ⌜r = true ↔ o.lt ka kb⌝ }})

/-- **The iterator protocol** for an iteration visiting the entries `r` in order: the callback
is called on each next entry, with the visited prefix's `I pre false`, and returns whether to go
on; `I pre true` records that it asked to stop after `pre`. -/
def iterProtocol {V K : Type} (o : ItemOrder GF V K) (iter : GoFunc) (r : List (V × K))
    (I : List (V × K) → Bool → IProp GF) : IProp GF :=
  iprop(□ ∀ (pre : List (V × K)) (e : V × K), ⌜(pre ++ [e]) <+: r⌝ -∗
    {{ I pre false ∗ o.item e.1 e.2 }}
      (App (Val #iter) (Val #e.1))
    {{ (b : Bool), RET #b; I (pre ++ [e]) (!b) }})

/-- What an iteration over `r` ends with: the callback stopped it after a prefix, or it visited
all of `r`. -/
def iterDone {V K : Type} (r : List (V × K)) (I : List (V × K) → Bool → IProp GF) : IProp GF :=
  iprop(∃ (pre : List (V × K)) (stopped : Bool),
    I pre stopped ∗ ⌜pre <+: r ∧ (stopped = false → pre = r)⌝)

/-- **The tree `t` holds the entries `s`** (fractional in `dq`). See the header. -/
opaque ownBTree {V K : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (o : ItemOrder GF V K) (t : Loc) (dq : DFrac) (s : List (V × K)) : IProp GF := iprop(True)

/-- **`f` is a free list** of nodes of item type `V` (persistent). -/
opaque isFreeList (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V] (f : Loc) : IProp GF :=
  iprop(True)

/-! ## Laws -/

/-- A tree's entries have strictly increasing keys. -/
def ownBTree_sorted.spec : Prop :=
  ∀ {V K : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (o : ItemOrder GF V K) (t : Loc)
    (dq : DFrac) (s : List (V × K)),
  ownBTree o t dq s ⊢ ⌜Sorted o.lt s⌝

/-- Each entry's item has its key. -/
def ownBTree_items.spec : Prop :=
  ∀ {V K : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (o : ItemOrder GF V K) (t : Loc)
    (dq : DFrac) (s : List (V × K)),
  ownBTree o t dq s ⊢ allItems o s

/-- Fractions split and join (at the same entries). -/
def ownBTree_fractional.spec : Prop :=
  ∀ {V K : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (o : ItemOrder GF V K) (t : Loc)
    (q1 q2 : Qp) (s : List (V × K)),
  ownBTree o t (DFrac.own (q1 + q2)) s ⊣⊢ ownBTree o t (DFrac.own q1) s ∗ ownBTree o t (DFrac.own q2) s

/-- Two fractions agree on the entries. -/
def ownBTree_agree.spec : Prop :=
  ∀ {V K : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (o : ItemOrder GF V K) (t : Loc)
    (dq1 dq2 : DFrac) (s1 s2 : List (V × K)),
  ownBTree o t dq1 s1 ∗ ownBTree o t dq2 s2 ⊢ ⌜s1 = s2⌝

/-- A tree no one will write again may be frozen read-only (the cache's snapshot clones). -/
def ownBTree_persist.spec : Prop :=
  ∀ {V K : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (o : ItemOrder GF V K) (t : Loc)
    (dq : DFrac) (s : List (V × K)),
  ownBTree o t dq s ⊢ |==> ownBTree o t DFrac.discard s

def ownBTree_discard_persistent.spec : Prop :=
  ∀ {V K : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (o : ItemOrder GF V K) (t : Loc)
    (s : List (V × K)),
  Persistent (ownBTree o t DFrac.discard s)

def isFreeList_persistent.spec : Prop :=
  ∀ (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V] (f : Loc),
  Persistent (isFreeList (GF := GF) V f)

end res

end BTree
end EtcdGrove
end Perennial
