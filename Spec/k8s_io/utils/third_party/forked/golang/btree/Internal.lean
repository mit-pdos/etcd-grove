/-
# The B-tree's internal vocabulary (batch 1g): nodes, contexts, the free list

What the specs of the package's unexported functions (`node.*`, `items.*`, `copyOnWriteContext.*`,
`FreeList.*`, `min`, `max`, `optional`, `empty`, `BTree.deleteItem`, `maxItems`, `minItems`) are
stated in. No client outside the package imports this module (the cache sees the tree through
`Api.lean` only).

* `Tree E` (transparent): the abstract node tree, its in-order contents `elems`, the shape
  invariant of a B-tree of degree `d` (`Shape`, `RootBounds`).
* `isCow o c f less` (persistent): `c` is a copy-on-write context with free list `f` and less
  function `less` (its points-to read-only, `isFreeList f`, `isLess o less`).
* `nodeShallow c dq n is ps`: a node's own memory (fields `items`, `children`, `cow = c`, the item
  slice holding `is`'s items and the child slice the pointers `ps`, with their capacities).
* `ownNode o c f less dq n t`: the subtree `t` at `n`, of a tree with context `c`: owned nodes at
  `dq`, or frozen (shared by a clone, read-only forever, no node with context `c`).
  `ownedNode` the same with the node at `n` itself owned.
* `ownRoot o c f less d dq r s`: the root `r` (or `nil` for an empty tree) of a tree of degree `d`
  holding `s`.
* `frozen o c f less n t` (persistent): a subtree shared by a clone, read-only forever.
* `freeNode n`: a node on the free list (no items, no children, capacities owned).
Intended realization: the old `Proof/k8s_io/.../btree/Defs.lean` (`nodeFields`, `frozen`,
`ownNodes`), unchanged.
-/
module

public import Spec.k8s_io.utils.third_party.forked.golang.btree.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BTree

open Iris Iris.BI
open Classical

/-! ## Trees -/

/-- The abstract node tree: a node's items (entries) and its children (none for a leaf). -/
inductive Tree (E : Type) where
  | node (items : List E) (children : List (Tree E))

namespace Tree
variable {E : Type}

def items : Tree E → List E
  | .node is _ => is

def children : Tree E → List (Tree E)
  | .node _ cs => cs

mutual
/-- The in-order contents. -/
def elems : Tree E → List E
  | .node is cs => elemsAux is cs

def elemsAux : List E → List (Tree E) → List E
  | is, [] => is
  | [], c :: cs => elems c ++ elemsAux [] cs
  | i :: is, c :: cs => elems c ++ i :: elemsAux is cs
end

/-- The shape of a B-tree of degree `d` and height `h` (the node itself unbounded). -/
def Shape (d : Nat) : Nat → Tree E → Prop
  | 0, .node _ cs => cs = []
  | h + 1, .node is cs => cs.length = is.length + 1 ∧
      ∀ c ∈ cs, (d - 1 ≤ c.items.length ∧ c.items.length ≤ 2 * d - 1) ∧ Shape d h c

/-- The root's bounds between operations. -/
def RootBounds (d h : Nat) (t : Tree E) : Prop :=
  t.items.length ≤ 2 * d - 1 ∧ (0 < h → 1 ≤ t.items.length)

end Tree

/-- The number of entries with keys below `k`: where `items.find` puts `k`. -/
def countLt {V K : Type} (lt : K → K → Prop) (s : List (V × K)) (k : K) : Nat :=
  (s.takeWhile (fun e => decide (lt e.2 k))).length

/-- The child `node.remove` descends into, of a node with items `is`. -/
def remIdx {V K : Type} (lt : K → K → Prop) : Target K → List (V × K) → Nat
  | .key k, is => countLt lt is k
  | .min, _ => 0
  | .max, is => is.length

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `c` is a copy-on-write context with free list `f` and less function `less` (persistent). -/
opaque isCow {V K : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (o : ItemOrder GF V K)
    (c f : Loc) (less : GoFunc) : IProp GF := iprop(True)

/-- An owned node's own memory. -/
opaque nodeShallow {V K : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (c : Loc) (dq : DFrac)
    (n : Loc) (is : List (V × K)) (ps : List Loc) : IProp GF := iprop(True)

/-- The subtree `t` at `n` (owned at `dq`, or frozen). -/
opaque ownNode {V K : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (o : ItemOrder GF V K)
    (c f : Loc) (less : GoFunc) (dq : DFrac) (n : Loc) (t : Tree (V × K)) : IProp GF := iprop(True)

/-- A frozen subtree: read-only forever, and none of its nodes has context `c` (persistent). -/
opaque frozen {V K : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (o : ItemOrder GF V K)
    (c f : Loc) (less : GoFunc) (n : Loc) (t : Tree (V × K)) : IProp GF := iprop(True)

/-- The subtree `t` at `n`, the node at `n` owned by the context `c`. -/
opaque ownedNode {V K : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (o : ItemOrder GF V K)
    (c f : Loc) (less : GoFunc) (dq : DFrac) (n : Loc) (t : Tree (V × K)) : IProp GF := iprop(True)

/-- The root `r` of a tree of degree `d` holding `s`. -/
opaque ownRoot {V K : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (o : ItemOrder GF V K)
    (c f : Loc) (less : GoFunc) (d : Nat) (dq : DFrac) (r : Loc) (s : List (V × K)) : IProp GF :=
  iprop(True)

/-- A node on the free list. -/
opaque freeNode (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V] (n : Loc) : IProp GF :=
  iprop(True)

/-- The item a removal is given: one with the key, for `Target.key`. -/
def targetItem {V K : Type} (o : ItemOrder GF V K) (tgt : Target K) (item : V) : IProp GF :=
  match tgt with
  | .key k => o.item item k
  | _ => iprop(True)

/-- The key of an `optionalItem` bound: `none` if it is not valid. -/
def optKey {V K : Type} (o : ItemOrder GF V K)
    (oi : k8s_io.utils.third_party.forked.golang.btree.optionalItem V) (ks : Option K) : IProp GF :=
  if oi.valid' then iprop(∃ k, ⌜ks = some k⌝ ∗ o.item oi.item' k) else iprop(⌜ks = none⌝)

end res

end BTree
end EtcdGrove
end Perennial
