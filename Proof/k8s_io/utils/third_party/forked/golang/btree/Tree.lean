/-
The pure model of google/btree: keys under a strict total order, the abstract tree of a
B-tree's nodes, its in-order contents, and the shape invariant of a B-tree of degree `d`.
-/

module
public import Perennial.Proof.ProofPrelude

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

/-! ## Keys -/

/-- A strict total order on keys. The B-tree's `less` function is required to decide it
on the keys of the items it is called on (`isLess`, `Defs.lean`); an order on items
that is only a strict *weak* order is a strict total order on its equivalence classes,
which is what a client takes as keys. -/
structure StrictOrder {K : Type} (lt : K → K → Prop) : Prop where
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  total : ∀ a b, lt a b ∨ a = b ∨ lt b a

/-! ## Trees -/

/-- The abstract node tree: a node's items, and its children (none for a leaf). The
items are entries `(v, k)`: the Go value stored and its key. -/
inductive Tree (E : Type) where
  | node (items : List E) (children : List (Tree E))
  deriving Inhabited

namespace Tree
variable {E : Type}

def items : Tree E → List E
  | .node is _ => is

def children : Tree E → List (Tree E)
  | .node _ cs => cs

@[simp] theorem items_node (is : List E) (cs : List (Tree E)) : (Tree.node is cs).items = is := rfl
@[simp] theorem children_node (is : List E) (cs : List (Tree E)) :
    (Tree.node is cs).children = cs := rfl

mutual
/-- The in-order contents: `c₀ ++ [i₀] ++ c₁ ++ … ++ [iₙ₋₁] ++ cₙ` for an internal node
with items `i₀ … iₙ₋₁` and children `c₀ … cₙ`, the items of a leaf. -/
def elems : Tree E → List E
  | .node is cs => elemsAux is cs

/-- `elems` of a node with items `is` and children `cs`. -/
def elemsAux : List E → List (Tree E) → List E
  | is, [] => is
  | [], c :: cs => elems c ++ elemsAux [] cs
  | i :: is, c :: cs => elems c ++ i :: elemsAux is cs
end

@[simp] theorem elems_node (is : List E) (cs : List (Tree E)) :
    (Tree.node is cs).elems = elemsAux is cs := by
  rw [elems]

@[simp] theorem elemsAux_nil (is : List E) : elemsAux is [] = is := by
  cases is <;> rw [elemsAux]

@[simp] theorem elemsAux_cons_cons (i : E) (is : List E) (c : Tree E) (cs : List (Tree E)) :
    elemsAux (i :: is) (c :: cs) = elems c ++ i :: elemsAux is cs := by
  rw [elemsAux]

@[simp] theorem elemsAux_nil_cons (c : Tree E) (cs : List (Tree E)) :
    elemsAux [] (c :: cs) = elems c ++ elemsAux [] cs := by
  rw [elemsAux]

/-- The shape of a B-tree of degree `d` and height `h`: a leaf at height 0, and an
internal node has one more child than items, every child of height `h - 1` and holding
between `d - 1` and `2d - 1` items. The node itself is not bounded here (the root is
not); see `RootBounds`. -/
def Shape (d : Nat) : Nat → Tree E → Prop
  | 0, .node _ cs => cs = []
  | h + 1, .node is cs => cs.length = is.length + 1 ∧
      ∀ c ∈ cs, (d - 1 ≤ c.items.length ∧ c.items.length ≤ 2 * d - 1) ∧ Shape d h c

/-- The root's bounds between operations: at most `2d - 1` items, and an internal root
has at least one (`deleteItem` replaces a root left without items by its only child). -/
def RootBounds (d h : Nat) (t : Tree E) : Prop :=
  t.items.length ≤ 2 * d - 1 ∧ (0 < h → 1 ≤ t.items.length)

end Tree

/-! ## Sorted lists of entries -/

section sorted
variable {V K : Type}

/-- Strictly increasing keys. -/
def Sorted (lt : K → K → Prop) (l : List (V × K)) : Prop :=
  l.Pairwise (fun a b => lt a.2 b.2)

end sorted

end btree
end EtcdGrove
end Perennial
