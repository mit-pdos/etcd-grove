/-
The representation predicates of google/btree (`btree_generic.go`).

**Ownership of nodes.** A tree owns the nodes whose `cow` is its copy-on-write context
(`BTreeG.cow`); those it mutates in place. Every other node it reaches is *frozen*: it
was shared by a `Clone` (which gives both trees fresh contexts, so that no tree owns any
existing node) and is never written again (every write goes through `mutableFor`, which
copies a node it does not own). So a frozen node and everything below it is read-only
forever: `frozen` is persistent, and records that no node below has the tree's context
(`n.cow == cow` is a pointer comparison, so a frozen node must be known to differ).
`ownNode` is either an owned node (fractional points-tos, its children `ownNode` again)
or a frozen one.

**The free list** (`FreeListG`) is shared by a tree and its clones (and by any trees
built with `NewWithFreeListG` on it) and holds, under its mutex, nodes nobody reaches:
`freeNode`, with empty item and child slices whose capacity is owned for reuse.

**Copy-on-write contexts** never change after they are made (`Clone` copies one into a
fresh variable), so `isCow` is persistent: the context's points-to, the free list's
mutex invariant, and the `less` function's spec. All contexts of a tree family share
the free list and `less`.

**Items and keys.** Items are Go values `V`; the order is on *keys* `K`, related to
items by a persistent predicate `ItemOrder.item v k` (for an ordered type, `v = k`; for
etcd's cache, a `*kvItem` and the string its immutable `key` field holds). `less`
decides the strict total order `ItemOrder.lt` on the keys of the items it is called on.
The abstract state of a tree is the list of its entries `(v, k)`, keys strictly
increasing.
-/
import EtcdGrove.Btree.Tree
import GoogleBtree.GeneratedProof.github_com.google.btree
import Perennial.Proof.sync_proof.mutex

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI github_com.google.btree

/-- How items are ordered: a strict total order `lt` on keys, and the persistent
relation `item v k` between an item and its key. -/
structure ItemOrder (GF : BundledGFunctors) (V K : Type) where
  lt : K → K → Prop
  order : StrictOrder lt
  item : V → K → IProp GF
  item_persistent : ∀ v k, Persistent (item v k)

attribute [instance] ItemOrder.item_persistent

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
variable {K : Type}

/-- Every entry's item has its key. -/
def allItems (o : ItemOrder GF V K) (l : List (V × K)) : IProp GF :=
  iprop(□ ∀ e, ⌜e ∈ l⌝ -∗ o.item e.1 e.2)

instance allItems_persistent (o : ItemOrder GF V K) (l : List (V × K)) :
    Persistent (allItems o l) := by
  unfold allItems; infer_instance

/-- `less a b` decides `lt` on the keys of `a` and `b`. -/
def isLess (o : ItemOrder GF V K) (less : GoFunc) : IProp GF :=
  iprop(∀ (a b : V) (ka kb : K),
    {{ o.item a ka ∗ o.item b kb }}
      (App (App (Val #less) (Val #a)) (Val #b))
    {{ (r : Bool), RET #r; ⌜r = true ↔ o.lt ka kb⌝ }})

instance isLess_persistent (o : ItemOrder GF V K) (less : GoFunc) :
    Persistent (isLess o less) := by
  unfold isLess; infer_instance

/-- The fields of a node, as separate points-tos (the item and child slices are passed
to `items` methods by the address of the field). -/
def nodeFields (n : Loc) (dq : DFrac) (is cs : GoSlice) (cow : Loc) : IProp GF :=
  iprop(⌜n ≠ null⌝ ∗
    structFieldRef (node V) go!"items" n ↦{dq} is ∗
    structFieldRef (node V) go!"children" n ↦{dq} cs ∗
    structFieldRef (node V) go!"cow" n ↦{dq} cow)

/-- A node in the free list: no items or children, the capacity of both slices owned
(`mutableFor` reuses it). -/
def freeNode (n : Loc) : IProp GF :=
  iprop(∃ (is cs : GoSlice) (cow : Loc),
    nodeFields (V := V) n (DFrac.own 1) is cs cow ∗
    is ↦* ([] : List V) ∗ ownSliceCap V is (DFrac.own 1) ∗
    cs ↦* ([] : List Loc) ∗ ownSliceCap Loc cs (DFrac.own 1))

/-- The free list's mutex invariant. -/
def freeListInv (f : Loc) : IProp GF :=
  iprop(∃ (sl : GoSlice) (ns : List Loc),
    structFieldRef (FreeListG V) go!"freelist" f ↦ sl ∗
    sl ↦* ns ∗ ownSliceCap Loc sl (DFrac.own 1) ∗
    [∗list] n ∈ ns, freeNode (V := V) n)

/-- `f` is a free list (of nodes of item type `V`). -/
def isFreeList (f : Loc) : IProp GF :=
  sync.isMutex (structFieldRef (FreeListG V) go!"mu" f) (freeListInv (V := V) f)

instance isFreeList_persistent (f : Loc) : Persistent (isFreeList (GF := GF) (V := V) f) := by
  unfold isFreeList; infer_instance

/-- `c` is a copy-on-write context with free list `f` and less function `less`. -/
def isCow (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) : IProp GF :=
  iprop(c ↦□ (copyOnWriteContext.mk f less : copyOnWriteContext V) ∗
    isFreeList (V := V) f ∗ isLess o less)

instance isCow_persistent (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) :
    Persistent (isCow o c f less) := by
  unfold isCow; infer_instance

mutual
/-- A frozen subtree: read-only forever, and none of its nodes has context `c`. -/
def frozen (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (n : Loc) :
    Tree (V × K) → IProp GF
  | .node is cs => iprop(∃ (isl csl : GoSlice) (cow : Loc) (ps : List Loc),
      nodeFields (V := V) n DFrac.discard isl csl cow ∗ ⌜cow ≠ c⌝ ∗
      isCow o cow f less ∗
      isl ↦*□ is.map Prod.fst ∗ csl ↦*□ ps ∗
      frozenList o c f less ps cs)

def frozenList (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) :
    List Loc → List (Tree (V × K)) → IProp GF
  | [], [] => iprop(True)
  | p :: ps, t :: ts => iprop(frozen o c f less p t ∗ frozenList o c f less ps ts)
  | _, _ => iprop(False)
end

mutual
/-- The subtree at `n`, of a tree with context `c`: an owned node, at fraction `dq`, or
a frozen subtree. -/
def ownNode (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (dq : DFrac) (n : Loc) :
    Tree (V × K) → IProp GF
  | .node is cs => iprop((∃ (isl csl : GoSlice) (ps : List Loc),
        nodeFields (V := V) n dq isl csl c ∗
        isl ↦*{dq} is.map Prod.fst ∗ ownSliceCap V isl dq ∗
        csl ↦*{dq} ps ∗ ownSliceCap Loc csl dq ∗
        ownNodes o c f less dq ps cs) ∨
      frozen o c f less n (.node is cs))

def ownNodes (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (dq : DFrac) :
    List Loc → List (Tree (V × K)) → IProp GF
  | [], [] => iprop(True)
  | p :: ps, t :: ts => iprop(ownNode o c f less dq p t ∗ ownNodes o c f less dq ps ts)
  | _, _ => iprop(False)
end

/-- **The B-tree at `t` holds the entries `s`** (keys strictly increasing), at fraction
`dq`: `Clone` and every mutation need `DFrac.own 1`; the read-only methods take any
fraction.

The degree `d` is between 2 and `2^62` (`NewG` panics below; above, `maxItems() =
2d - 1` overflows `int`). `Len()` is `t.length`, which counts the entries modulo `2^64`
(`W64` of the length). An empty tree may have no root (fresh, or after `Clear`) or an
empty leaf root (after deleting its last item). -/
def ownBTree (o : ItemOrder GF V K) (t : Loc) (dq : DFrac) (s : List (V × K)) : IProp GF :=
  iprop(∃ (tv : BTreeG V) (f : Loc) (less : GoFunc) (d : Nat),
    "Ht" ∷ t ↦{dq} tv ∗
    "#Hcow" ∷ isCow o tv.cow' f less ∗
    "%Hdeg" ∷ ⌜sint.Z tv.degree' = d ∧ 2 ≤ d ∧ d ≤ 2 ^ 62⌝ ∗
    "%Hlen" ∷ ⌜tv.length' = W64 s.length⌝ ∗
    "%Hsorted" ∷ ⌜Sorted o.lt s⌝ ∗
    "#Hitems" ∷ allItems o s ∗
    "Hroot" ∷ (⌜tv.root' = null ∧ s = []⌝ ∨
      ∃ (h : Nat) (tr : Tree (V × K)),
        ⌜tr.Shape d h ∧ tr.RootBounds d h ∧ tr.elems = s⌝ ∗
        ownNode o tv.cow' f less dq tv.root' tr))

end defs

end Btree
end EtcdGrove
end Perennial
