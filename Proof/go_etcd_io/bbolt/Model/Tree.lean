/-
The committed tree's well-formedness (U0a of `notes/bbolt-proof-plan.md`; design §3.2).

`treeWF pages hwm root`: the bucket tree rooted at page `root` is well-formed in `pages`: every
page of it a well-formed leaf or branch (elements, keys and values inside the page), its children
below the high-water mark, and so the trees of its nested buckets. Inductive: a page graph with
a cycle does not satisfy it. `treeStrict` adds what a writer needs beyond the shape (non-empty
keys, good inline pages, no shared page), the B+tree's keys (`treeKeys`) and uniform leaf depth
(`pageHts`). `treeOK C` is all of `fileHolds`' tree clauses over the committed state `C`.

Ported from `old/bbolt/.../{TxModel,FilePages,TreeStrict,TreeKeys,WriteTxShape}.lean` (pure
parts), over `Model/Page.lean`'s byte decoding.
-/
module

public import Proof.go_etcd_io.bbolt.Model.Meta
public import Spec.go_etcd_io.bbolt.Data

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


section tree
variable [GooseExts]

/-! ## Well-formed pages -/

/-- A leaf page's elements, keys and values lie inside its `len` bytes, below `MaxAllocSize`
from its start, and its keys increase strictly. -/
def leafWF (pg : List w8) (len : Nat) : Prop :=
  len ≤ pg.length ∧ elemOff (pageCount pg) ≤ len ∧
  (∀ i < pageCount pg,
    elemOff i + leafPos pg i + leafKsize pg i + leafVsize pg i ≤ len ∧
    elemOff i + leafPos pg i + leafKsize pg i + leafVsize pg i ≤ maxAllocSize) ∧
  ∀ i j, i < j → j < pageCount pg → go.GoStringLt (leafKey pg i) (leafKey pg j)

/-- A branch page has an element, its elements and keys lie inside its `len` bytes, below
`MaxAllocSize`, its children below the high-water mark `hwm`, and its keys increase strictly. -/
def branchWF (pg : List w8) (len hwm : Nat) : Prop :=
  0 < pageCount pg ∧ len ≤ pg.length ∧ elemOff (pageCount pg) ≤ len ∧
  (∀ i < pageCount pg,
    elemOff i + branchPos pg i + branchKsize pg i ≤ len ∧
    elemOff i + branchPos pg i + branchKsize pg i ≤ maxAllocSize ∧ branchPgid pg i < hwm) ∧
  ∀ i j, i < j → j < pageCount pg → go.GoStringLt (branchKey pg i) (branchKey pg j)

/- Well-formed bucket trees in `pages` (high-water mark `hwm`): `treeWF` from a page id,
`pageTreeWF` from a root page's bytes (`len` of them the page's), `bucketWF` from a nested
bucket's value. -/
mutual
inductive treeWF (pages : Pages) (hwm : Nat) : Nat → Prop
  | page (root : Nat) (pg : List w8) :
      2 ≤ root → root < hwm → pages !! root = some pg → pageId pg = root →
      pg.length = (1 + pageOverflow pg) * 4096 →
      pageTreeWF pages hwm pg pg.length → treeWF pages hwm root

inductive pageTreeWF (pages : Pages) (hwm : Nat) : List w8 → Nat → Prop
  | leaf (pg : List w8) (len : Nat) :
      pageFlags pg = leafPageFlag → leafWF pg len →
      (∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag →
        bucketWF pages hwm (leafValue pg i)) →
      pageTreeWF pages hwm pg len
  | branch (pg : List w8) (len : Nat) :
      pageFlags pg = branchPageFlag → branchWF pg len hwm →
      (∀ i < pageCount pg, treeWF pages hwm (branchPgid pg i)) →
      pageTreeWF pages hwm pg len

inductive bucketWF (pages : Pages) (hwm : Nat) : List w8 → Prop
  | file (v : List w8) : 16 ≤ v.length → inBucketRoot v ≠ 0 →
      treeWF pages hwm (inBucketRoot v) → bucketWF pages hwm v
  | inline (v : List w8) : 16 ≤ v.length → inBucketRoot v = 0 →
      pageFlags (inlinePage v) = leafPageFlag →
      pageTreeWF pages hwm (inlinePage v) (inlinePage v).length → bucketWF pages hwm v
end

/-! ## The pages of a tree -/

/- `treeHas pages root id`: page `id` is a page of the tree from page `root`, nested buckets'
trees included (`pageHas` from a page's bytes, `bucketHas` from a nested bucket's value). -/
mutual
inductive treeHas (pages : Pages) : Nat → Nat → Prop
  | root (root : Nat) (pg : List w8) : pages !! root = some pg → treeHas pages root root
  | sub (root : Nat) (pg : List w8) (id : Nat) :
      pages !! root = some pg → pageHas pages pg id → treeHas pages root id

inductive pageHas (pages : Pages) : List w8 → Nat → Prop
  | child (pg : List w8) (i id : Nat) :
      pageFlags pg = branchPageFlag → i < pageCount pg → treeHas pages (branchPgid pg i) id →
      pageHas pages pg id
  | bucket (pg : List w8) (i id : Nat) :
      pageFlags pg = leafPageFlag → i < pageCount pg → leafFlags pg i % 2 = bucketLeafFlag →
      bucketHas pages (leafValue pg i) id → pageHas pages pg id

inductive bucketHas (pages : Pages) : List w8 → Nat → Prop
  | file (v : List w8) (id : Nat) :
      inBucketRoot v ≠ 0 → treeHas pages (inBucketRoot v) id → bucketHas pages v id
  | inline (v : List w8) (id : Nat) :
      inBucketRoot v = 0 → pageHas pages (inlinePage v) id → bucketHas pages v id
end

/-- Page `id` is a page of the bucket tree from `root`, not of a nested bucket's tree (through
branches only). -/
inductive ownHas (pages : Pages) : Nat → Nat → Prop
  | root (root : Nat) (pg : List w8) : pages !! root = some pg → ownHas pages root root
  | child (root : Nat) (pg : List w8) (i id : Nat) :
      pages !! root = some pg → pageFlags pg = branchPageFlag → i < pageCount pg →
      ownHas pages (branchPgid pg i) id → ownHas pages root id

open Classical in
/-- The pages of `pages` the tree from `root` reaches. -/
def treePages (pages : Pages) (root : Nat) : Pages :=
  GMap.filter (fun id _ => decide (treeHas pages root id)) pages

/-- The slots a page of `pages` covers (page `id` covers `id` to `id + overflow`). -/
def coversSlot (pages : Pages) (s : Nat) : Prop :=
  ∃ id pg, pages !! id = some pg ∧ id ≤ s ∧ s < id + (1 + pageOverflow pg)

/-- Every slot a page of `pages` covers, in the order of `pages`' list. -/
def pagesSlots (pages : Pages) : List Nat :=
  pages.toList.flatMap fun ip => List.range' ip.1 (1 + pageOverflow ip.2)

/-- The slots of the committed tree. -/
def treeSlots (C : CommitSt) : List Nat := pagesSlots C.pages

/-- No two pages of `pages` share a slot. -/
def pagesDisjoint (pages : Pages) : Prop :=
  ∀ id1 pg1 id2 pg2, pages !! id1 = some pg1 → pages !! id2 = some pg2 → id1 ≠ id2 →
    id1 + (1 + pageOverflow pg1) ≤ id2 ∨ id2 + (1 + pageOverflow pg2) ≤ id1

/-! ## Strictness (what a writer needs of the tree) -/

/-- An inline bucket's page as bbolt writes one: id 0, a leaf, keys non-empty, no nested
bucket. -/
def inlineGood (ip : List w8) : Prop :=
  pageId ip = 0 ∧ pageFlags ip = leafPageFlag ∧ leafWF ip ip.length ∧ 16 ≤ ip.length ∧
  ∀ i < pageCount ip, 0 < leafKsize ip i ∧ leafFlags ip i % 2 = 0

/-- A page `ReadInodeFromPage` reads (non-empty keys), whose inline buckets are good. -/
def pageGood (pg : List w8) : Prop :=
  (pageFlags pg = leafPageFlag → ∀ i < pageCount pg, 0 < leafKsize pg i ∧
    (leafFlags pg i % 2 = bucketLeafFlag → inBucketRoot (leafValue pg i) = 0 →
      inlineGood (inlinePage (leafValue pg i)))) ∧
  (pageFlags pg = branchPageFlag → ∀ i < pageCount pg, 0 < branchKsize pg i)

/-- No page is shared: the subtrees of a branch's children are disjoint and do not contain the
branch, and so are a leaf's nested buckets' trees. -/
def viewUnique (pages : Pages) : Prop :=
  (∀ id pg, pages !! id = some pg → pageFlags pg = branchPageFlag →
    (∀ i j, i < pageCount pg → j < pageCount pg → i ≠ j → ∀ d,
      treeHas pages (branchPgid pg i) d → ¬ treeHas pages (branchPgid pg j) d) ∧
    (∀ i < pageCount pg, ¬ treeHas pages (branchPgid pg i) id)) ∧
  ∀ id pg, pages !! id = some pg → pageFlags pg = leafPageFlag →
    (∀ i j, i < pageCount pg → j < pageCount pg → i ≠ j → leafFlags pg i % 2 = bucketLeafFlag →
      leafFlags pg j % 2 = bucketLeafFlag → ∀ d, bucketHas pages (leafValue pg i) d →
        ¬ bucketHas pages (leafValue pg j) d) ∧
    (∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag →
      ¬ bucketHas pages (leafValue pg i) id)

/-- Every page good and none shared. -/
def pagesStrict (pages : Pages) : Prop :=
  (∀ id pg, pages !! id = some pg → pageGood pg) ∧ viewUnique pages

/-- The pages have the heights `pht`: a leaf 0, a branch one more than each of its children
(uniform leaf depth: `rebalance` merges siblings without checking their kinds). -/
def pageHts (P : Pages) (pht : Nat → Nat) : Prop :=
  ∀ id pg, P !! id = some pg → (pageFlags pg = leafPageFlag → pht id = 0) ∧
    (pageFlags pg = branchPageFlag → ∀ i < pageCount pg, pht (branchPgid pg i) + 1 = pht id)

/-! ## Keys -/

/-- `k` is not below the bound `lo`. -/
def keyGe (lo : Option (List w8)) (k : List w8) : Prop := ∀ l, lo = some l → ¬ go.GoStringLt k l

/-- `k` is below the bound `hi`. -/
def keyLt (k : List w8) (hi : Option (List w8)) : Prop := ∀ h, hi = some h → go.GoStringLt k h

/-- `k` is in `[lo, hi)`. -/
def keyIn (lo hi : Option (List w8)) (k : List w8) : Prop := keyGe lo k ∧ keyLt k hi

/-- The lower bound of child `i` of a branch with keys `ks` and lower bound `lo`. -/
def childLo (lo : Option (List w8)) (ks : Nat → List w8) (i : Nat) : Option (List w8) :=
  if i = 0 then lo else some (ks i)

/-- The upper bound of child `i` of a branch with `n` keys `ks` and upper bound `hi`. -/
def childHi (hi : Option (List w8)) (ks : Nat → List w8) (n i : Nat) : Option (List w8) :=
  if i + 1 < n then some (ks (i + 1)) else hi

/-- The bounds of entry `i`'s child, under a node with the keys `ks` and the bounds `b`. -/
def entryBnd (b : Option (List w8) × Option (List w8)) (ks : List (List w8)) (i : Nat) :
    Option (List w8) × Option (List w8) :=
  (childLo b.1 (fun j => ks.getD j []) i, childHi b.2 (fun j => ks.getD j []) ks.length i)

/-- The keys of the tree rooted at `root` are a B+tree's, in `[lo, hi)`: a branch has at least
two elements, element `i`'s key is the first key of its child `i` (not empty), the children are
all of one kind, and child `i` has the keys from element `i`'s key to element `i + 1`'s; a nested
bucket stored in pages has its own tree, with its own keys. -/
inductive treeKeys (pages : Pages) : Nat → Option (List w8) → Option (List w8) → Prop
  | leaf (root : Nat) (pg : List w8) (lo hi : Option (List w8)) :
      pages !! root = some pg → pageFlags pg = leafPageFlag →
      (∀ i < pageCount pg, keyIn lo hi (leafKey pg i)) →
      (∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag →
        inBucketRoot (leafValue pg i) ≠ 0 →
          treeKeys pages (inBucketRoot (leafValue pg i)) none none) →
      treeKeys pages root lo hi
  | branch (root : Nat) (pg : List w8) (lo hi : Option (List w8)) (kind : Nat) :
      pages !! root = some pg → pageFlags pg = branchPageFlag → 2 ≤ pageCount pg →
      (∀ i < pageCount pg, keyIn lo hi (branchKey pg i)) →
      (∀ i < pageCount pg, ∃ cpg, pages !! branchPgid pg i = some cpg ∧ 0 < pageCount cpg ∧
        pageFlags cpg = kind ∧ pageKey cpg 0 = branchKey pg i) →
      (∀ i < pageCount pg, treeKeys pages (branchPgid pg i) (childLo lo (branchKey pg) i)
        (childHi hi (branchKey pg) (pageCount pg) i)) →
      treeKeys pages root lo hi

/-- The tree rooted at `root`: well-formed and strict, its keys a B+tree's, its leaves at one
depth. -/
def treeStrict (pages : Pages) (hwm root : Nat) : Prop :=
  treeWF pages hwm root ∧ pagesStrict pages ∧ treeKeys pages root none none ∧
    ∃ pht, pageHts pages pht

/-! ## `treeOK`: `fileHolds`' tree clauses -/

/-- `pg` is a leaf page of the bucket whose value is `v` (its inline page, or a leaf of its
tree through branches). -/
def bktLeafPg (pages : Pages) (v : List w8) (pg : List w8) : Prop :=
  (inBucketRoot v = 0 ∧ pg = inlinePage v) ∨
  (inBucketRoot v ≠ 0 ∧ ∃ id, ownHas pages (inBucketRoot v) id ∧ pages !! id = some pg ∧
    pageFlags pg = leafPageFlag)

/-- The root bucket's leaves hold top-level buckets only, with names of `1..MaxKeySize` bytes
(item 3, batch 43.4: `CreateBucket` refuses a longer name, so every file bbolt writes has them),
each entry (name and bucket value) within `bboltEntryMax` (batch 37: an inline value is at most a
quarter page by `inlineable`); their leaves hold plain entries only (no nested bucket), each
within `bboltEntryMax`. The name bound is one conjunct with the non-emptiness
(`0 < ksize ∧ ksize ≤ maxKeySize`), so the positions of the others are unchanged. -/
def rootShape (pages : Pages) (root : Nat) : Prop :=
  ∀ id pg, ownHas pages root id → pages !! id = some pg → pageFlags pg = leafPageFlag →
    ∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag ∧
      (0 < leafKsize pg i ∧ leafKsize pg i ≤ maxKeySize) ∧
      leafKsize pg i + leafVsize pg i ≤ bboltEntryMax ∧
      ∀ bpg, bktLeafPg pages (leafValue pg i) bpg → ∀ j < pageCount bpg,
        leafFlags bpg j % 2 = 0 ∧ 0 < leafKsize bpg j ∧
        leafKsize bpg j + leafVsize bpg j ≤ bboltEntryMax

/-- **`fileHolds`' tree clauses** (design §3.2, D16) over the committed state:
- the tree is strict (`treeStrict`: well-formed, page ids are their headers', good inline pages,
  no shared page, B+tree keys with exact branch keys and branches of at least two elements, no
  empty child page, uniform leaf depth);
- `C.pages` is exactly the tree's pages;
- extents in `[2, hwm)` (by `treeWF`), pairwise disjoint, each page's bytes its whole extent;
- the root holds buckets only, names of `1..MaxKeySize` bytes, keys non-empty, entries within
  `bboltEntryMax` (`rootShape`);
- the txid below `2 ^ 63`. -/
def treeOK (C : CommitSt) : Prop :=
  treeStrict C.pages C.hwm C.root ∧ treePages C.pages C.root = C.pages ∧
  pagesDisjoint C.pages ∧
  (∀ id pg, C.pages !! id = some pg → id + (1 + pageOverflow pg) ≤ C.hwm) ∧
  rootShape C.pages C.root ∧ C.txid < 2 ^ 63

end tree

end bbolt
end EtcdGrove
end Perennial
