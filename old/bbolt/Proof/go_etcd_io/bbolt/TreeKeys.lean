/-
The keys of a bucket's tree: what bbolt's B+tree keeps beyond each page being sorted, and
what a spill relies on to write sorted pages and to replace a child's entry in its parent.

`treeKeys pages root lo hi`: every key of the tree rooted at `root` is in `[lo, hi)` (`none`:
no bound); a branch has at least two elements (`rebalance` asserts a node's parent has two
children), its element `i`'s key is the first key of its child `i`, which is not empty, the
children are all leaves or all branches (a merge in `rebalance` joins siblings), and child `i`
has the keys from element `i`'s key (from the branch's lower bound for `i = 0`: a writer puts
keys below the first one into the leftmost leaf) to element `i + 1`'s (the branch's upper bound
for the last). A nested bucket stored in pages has its own tree, with its own keys.

`node.spill` replaces a child's entry by the key the child was read with (`n.key`, its page's
first key): the entry's key must be that one, or `put` inserts a second entry and the first
keeps pointing at the freed page. The bounds make the keys `spill` writes into a branch (a
child's new first key, the first keys of its split parts) fall between their neighbours.
-/
module

public import Proof.go_etcd_io.bbolt.TxModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

/-- `k` is not below the bound `lo`. -/
def keyGe (lo : Option (List w8)) (k : List w8) : Prop := ∀ l, lo = some l → ¬ go.GoStringLt k l

/-- `k` is below the bound `hi`. -/
def keyLt (k : List w8) (hi : Option (List w8)) : Prop := ∀ h, hi = some h → go.GoStringLt k h

/-- `k` is in `[lo, hi)`. -/
def keyIn (lo hi : Option (List w8)) (k : List w8) : Prop := keyGe lo k ∧ keyLt k hi

/-- The key of element `i` of the page `pg` (a leaf's or a branch's). -/
def pageKey (pg : List w8) (i : Nat) : List w8 :=
  if pageFlags pg = leafPageFlag then leafKey pg i else branchKey pg i

/-- The lower bound of child `i` of a branch with keys `ks` and lower bound `lo`. -/
def childLo (lo : Option (List w8)) (ks : Nat → List w8) (i : Nat) : Option (List w8) :=
  if i = 0 then lo else some (ks i)

/-- The upper bound of child `i` of a branch with `n` keys `ks` and upper bound `hi`. -/
def childHi (hi : Option (List w8)) (ks : Nat → List w8) (n i : Nat) : Option (List w8) :=
  if i + 1 < n then some (ks (i + 1)) else hi

/-- The keys of the tree rooted at `root` (see the module doc). -/
inductive treeKeys (pages : GMap Nat (List w8)) : Nat → Option (List w8) → Option (List w8) → Prop
  | leaf (root : Nat) (pg : List w8) (lo hi : Option (List w8)) :
      pages !! root = some pg → pageFlags pg = leafPageFlag →
      (∀ i < pageCount pg, keyIn lo hi (leafKey pg i)) →
      (∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag →
        inBucketRoot (leafValue pg i) ≠ 0 → treeKeys pages (inBucketRoot (leafValue pg i)) none none) →
      treeKeys pages root lo hi
  | branch (root : Nat) (pg : List w8) (lo hi : Option (List w8)) (kind : Nat) :
      pages !! root = some pg → pageFlags pg = branchPageFlag → 2 ≤ pageCount pg →
      (∀ i < pageCount pg, keyIn lo hi (branchKey pg i)) →
      (∀ i < pageCount pg, ∃ cpg, pages !! branchPgid pg i = some cpg ∧ 0 < pageCount cpg ∧
        pageFlags cpg = kind ∧ pageKey cpg 0 = branchKey pg i) →
      (∀ i < pageCount pg, treeKeys pages (branchPgid pg i) (childLo lo (branchKey pg) i)
        (childHi hi (branchKey pg) (pageCount pg) i)) →
      treeKeys pages root lo hi

end bbolt
end EtcdGrove
end Perennial
