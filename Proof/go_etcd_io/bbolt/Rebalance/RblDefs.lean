/-
What `Commit`'s `tx.root.rebalance()` keeps and gives, at the level of one bucket (U8b of
`notes/bbolt-proof-plan.md`; pure), ported from `old/bbolt/.../RebalanceDefs.lean` over the new
model (`Model/Wtx.lean`).

**Keys** (`rblKeysB`). `rebalance` merges siblings and removes children, so the bounds of a node
(`bnd`) are no longer exactly its position's (`nodeKeys`): a node's bounds are *inside* its
position's (`bndIn`), and a branch's lower bound, if any, is its first key (`brFirst`). When a
branch loses its first entry its lower bound is tightened to its new first key (its children's
bounds are inside it), and a branch merged into its left sibling brings its first child's bound
with it (that child's keys are above the branch's first key). The exact form (`bktKeysB`) does
not survive each step, but it is recovered at the end: the exact bounds, defined top-down along
the parent chain, contain the rebalance's (`bktKeys_of_rbl`, `RblKeys.lean`).

A deficient node (`dfc`) is allowed for at most one node, the one being rebalanced: a branch
with one entry (as a branch that lost a child has while it is rebalanced), or an empty leaf no
longer marked unbalanced; every other branch has two entries, every other leaf under a branch
not marked unbalanced has one.
A leaf's entries have no child (`pgid` 0: the reparenting loop of a merge looks a leaf entry's
`pgid` up in `b.nodes`, which has no node for page 0 of a bucket that is not inline).

**What the transaction must give** (`rblReady`): the exact keys and, beyond them, `brFirst` and
the leaves' `pgid` 0 (both true of bbolt: branches are their pages' until `Commit` (`txPg`),
`Put` and `CreateBucket` put leaf entries with `pgid` 0), that the nodes' parent pointers have no
cycle (`rblAcyc`), and that all the leaves of a tree are at one depth (`rblHt`, of the nodes and
of the view's pages: a merge of two branches gives the merged one the children of both, which
must be of one kind; `pageHts`).

**Steps** (`rblStep`, `rblTxStep`): what a `node.rebalance` or a `Bucket.rebalance` changes.
-/
module

public import Proof.go_etcd_io.bbolt.Model.Wtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rbl
variable [GooseExts]

/-! ### Keys during rebalance -/

/-- The bound `a` is inside the bound `b`. -/
def bndIn (a b : Option (List w8) × Option (List w8)) : Prop :=
  (∀ y, b.1 = some y → ∃ x, a.1 = some x ∧ ¬ go.GoStringLt x y) ∧
  (∀ y, b.2 = some y → ∃ x, a.2 = some x ∧ ¬ go.GoStringLt y x)

/-- The node `l` (record `r`) of `B` and its keys during rebalance (see the module doc), the
nodes' bounds `bnd`, the deficient node `dfc`. -/
def rblNodeKeys (v : View) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (dfc : Option Loc) (l : Loc) (r : NRec) : Prop :=
  (∀ w ∈ r.ws, keyIn (bnd l).1 (bnd l).2 w.key) ∧
  (r.nv.parent' ≠ null → r.nv.key' ≠ slice.nil ∧ ∃ rp i w, B.ns !! r.nv.parent' = some rp ∧
    rp.ws[i]? = some w ∧ w.pgid = r.nv.pgid' ∧ w.key = r.key ∧
    bndIn (bnd l) (wEntryBnd (bnd r.nv.parent') rp.ws i)) ∧
  (r.nv.isLeaf' = false → (dfc ≠ some l → 2 ≤ r.ws.length) ∧
    (∀ x, (bnd l).1 = some x → wKey r.ws 0 = x) ∧
    ∃ kind : Bool, ∀ i w, r.ws[i]? = some w →
    (∀ l', B.nm !! w.pgid = some l' → ∃ r', B.ns !! l' = some r' ∧ r'.nv.isLeaf' = kind) ∧
    (B.nm !! w.pgid = none → ∃ pg, v.pages !! w.pgid.toNat = some pg ∧ 0 < pageCount pg ∧
      decide (pageFlags pg = leafPageFlag) = kind ∧ pageKey pg 0 = w.key ∧
      treeKeys v.pages w.pgid.toNat (wEntryBnd (bnd l) r.ws i).1
        (wEntryBnd (bnd l) r.ws i).2)) ∧
  (dfc ≠ some l → r.nv.isLeaf' = true → r.nv.unbalanced' = false → r.nv.parent' ≠ null →
    0 < r.ws.length) ∧
  (r.nv.isLeaf' = true → ∀ w ∈ r.ws, w.pgid = W64 0 ∧ (isBktFlag w.flags →
    inBucketRoot w.value ≠ 0 → ¬ opened B w.key →
      treeKeys v.pages (inBucketRoot w.value) none none))

/-- The keys of the bucket `B` during rebalance (see the module doc). -/
def rblKeysB (v : View) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (dfc : Option Loc) : Prop :=
  (B.bv.rootNode' = null → B.ib.root' ≠ W64 0 →
    treeKeys v.pages B.ib.root'.toNat none none) ∧
  (∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null) ∧
  ∀ l r, B.ns !! l = some r → rblNodeKeys v B bnd dfc l r

/-- The keys of the bucket `B` with no deficient node. -/
def rblKeys (v : View) (B : BRec) : Prop := ∃ bnd, rblKeysB v B bnd none

/-- The parent pointers of the bucket's nodes have no cycle: a height that a parent exceeds. -/
def rblAcyc (B : BRec) : Prop :=
  ∃ ht : Loc → Nat, ∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null → ht l < ht r.nv.parent'

/-- The bucket's nodes and the view's pages have heights (all the leaves of a tree are at one
depth): a leaf 0, a branch one more than its children, nodes or pages. -/
def rblHt (v : View) (B : BRec) : Prop :=
  ∃ (ht : Loc → Nat) (pht : Nat → Nat), pageHts v.pages pht ∧
    ∀ l r, B.ns !! l = some r → (r.nv.isLeaf' = true → ht l = 0) ∧
      (r.nv.isLeaf' = false → ∀ w ∈ r.ws, (∀ l', B.nm !! w.pgid = some l' → ht l' + 1 = ht l) ∧
        (B.nm !! w.pgid = none → pht w.pgid.toNat + 1 = ht l))

/-- The bucket `bl` (record `B`) during rebalance: clean, its keys (the deficient node `dfc`),
its parent pointers without cycle, its heights. -/
def rblB (v : View) (hwm : Nat) (bl : Loc) (B : BRec) (dfc : Option Loc) : Prop :=
  bktClean v hwm bl B ∧ (∃ bnd, rblKeysB v B bnd dfc) ∧ rblAcyc B ∧ rblHt v B

/-- A branch's lower bound, if any, is its first key. -/
def brFirst (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8)) : Prop :=
  ∀ l r, B.ns !! l = some r → r.nv.isLeaf' = false → ∀ x, (bnd l).1 = some x → wKey r.ws 0 = x

/-- A leaf's entries have no child page. -/
def leafPg0 (B : BRec) : Prop :=
  ∀ l r, B.ns !! l = some r → r.nv.isLeaf' = true → ∀ w ∈ r.ws, w.pgid = W64 0

/-- What `rebalance` needs of the transaction's keys (see the module doc): the exact keys with
`brFirst`, the leaves' `pgid` 0, acyclic parents, heights. -/
def rblReady (v : View) (T : WTx) : Prop :=
  ∀ bl B, T.bs !! bl = some B → (∃ bnd, bktKeysB v B bnd ∧ brFirst B bnd) ∧ leafPg0 B ∧
    rblAcyc B ∧ rblHt v B

/-- `txPg` gives the leaves' `pgid` 0 of each bucket. -/
theorem leafPg0_of_txPg (v : View) (bs : GMap Loc BRec) (h : txPg v bs) (bl : Loc) (B : BRec)
    (hb : bs !! bl = some B) : leafPg0 B :=
  fun l r hr hl => ((h bl B hb l r hr).1 hl).1

/-! ### Searches -/

/-- `j` is where a search for `key` lands among the entries `ws` (`childIndex`). -/
def wSearch (ws : List WEntry) (key : List w8) (j : Nat) : Prop :=
  j ≤ ws.length ∧ (∀ k < j, go.GoStringLt (wKey ws k) key) ∧
    (j < ws.length → ¬ go.GoStringLt (wKey ws j) key)

/-! ### Steps -/

/-- What a `node.rebalance` of the node `nl` did to its bucket: no field but the nodes, and
the unbalanced nodes after are some of those before (the same pages), not `nl`. -/
def rblStep (B B' : BRec) (nl : Loc) : Prop :=
  B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.bm = B.bm ∧
  ∀ l r', B'.ns !! l = some r' → r'.nv.unbalanced' = true →
    l ≠ nl ∧ ∃ r, B.ns !! l = some r ∧ r.nv.unbalanced' = true ∧ r'.nv.pgid' = r.nv.pgid'

/-- What a `Bucket.rebalance` did to the transaction's buckets: no field but the nodes, and no
node newly unbalanced. -/
def rblTxStep (T T' : WTx) : Prop :=
  ∀ b B', T'.bs !! b = some B' → ∃ B, T.bs !! b = some B ∧ B'.bv = B.bv ∧ B'.ib = B.ib ∧
    B'.bm = B.bm ∧ ∀ l r', B'.ns !! l = some r' → r'.nv.unbalanced' = true →
      ∃ r, B.ns !! l = some r ∧ r.nv.unbalanced' = true

end rbl

end bbolt
end EtcdGrove
end Perennial
