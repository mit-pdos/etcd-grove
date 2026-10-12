/-
What a write transaction needs of the current tree beyond `treeWF` (`TxModel.lean`), which
bbolt maintains (it writes no other tree) but the shape of a page does not imply:

- every key is non-empty (`ReadInodeFromPage`, which a writer calls to materialize a node,
  panics on an empty key; a leaf's first key may be empty in a `leafWF` page);
- an inline bucket's page has id 0 (a node read from it would otherwise free that page) and
  holds no nested bucket (bbolt inlines only buckets without one; an inline bucket's `page`
  points into the old mapping after a remap, and spill would read it through a nested bucket);
- no page is shared: the subtrees of a branch's children are disjoint and do not contain the
  branch (a writer materializes one node per page and frees each spilled page once).

`treeStrict pages hwm root` is the tree rooted at `root` well-formed and strict. A spill must
re-establish it for the tree it writes.
-/
module

public import Proof.go_etcd_io.bbolt.FilePages

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

/-- An inline bucket's page as bbolt writes one: id 0, a leaf, its keys non-empty, no nested
bucket. -/
def inlineGood (ip : List w8) : Prop :=
  pageId ip = 0 ∧ pageFlags ip = leafPageFlag ∧ leafWF ip ip.length ∧ 16 ≤ ip.length ∧
  ∀ i < pageCount ip, 0 < leafKsize ip i ∧ leafFlags ip i % 2 = 0

/-- A page `ReadInodeFromPage` reads, whose inline buckets are good. -/
def pageGood (pg : List w8) : Prop :=
  (pageFlags pg = leafPageFlag → ∀ i < pageCount pg, 0 < leafKsize pg i ∧
    (leafFlags pg i % 2 = bucketLeafFlag → inBucketRoot (leafValue pg i) = 0 →
      inlineGood (inlinePage (leafValue pg i)))) ∧
  (pageFlags pg = branchPageFlag → ∀ i < pageCount pg, 0 < branchKsize pg i)

/-- No page is shared: the subtrees of a branch's children are disjoint and do not contain the
branch. -/
def viewUnique (pages : GMap Nat (List w8)) : Prop :=
  ∀ id pg, pages !! id = some pg → pageFlags pg = branchPageFlag →
    (∀ i j, i < pageCount pg → j < pageCount pg → i ≠ j → ∀ d,
      treeHas pages (branchPgid pg i) d → ¬ treeHas pages (branchPgid pg j) d) ∧
    (∀ i < pageCount pg, ¬ treeHas pages (branchPgid pg i) id)

/-- Every page good and none shared. -/
def pagesStrict (pages : GMap Nat (List w8)) : Prop :=
  (∀ id pg, pages !! id = some pg → pageGood pg) ∧ viewUnique pages

/-- The tree rooted at `root` (high-water mark `hwm`) in `pages`: well-formed and strict. -/
def treeStrict (pages : GMap Nat (List w8)) (hwm root : Nat) : Prop :=
  treeWF pages hwm root ∧ pagesStrict pages

end bbolt
end EtcdGrove
end Perennial
