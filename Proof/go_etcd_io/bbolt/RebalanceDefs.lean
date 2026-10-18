/-
What `Commit`'s `tx.root.rebalance()` keeps and gives (`Bucket.rebalance`, `node.rebalance`,
`node.free`).

**Keys** (`rblKeysB`). `rebalance` merges siblings and removes children, so the bounds of a node
(`bnd`) are no longer exactly its position's (`nodeKeys`, `WriteTxShape.lean`): a node's bounds
are *inside* its position's (`bndIn`), and a branch's lower bound, if any, is its first key
(`brFirst`). When a branch loses its first entry its lower bound is tightened to its new first
key (its children's bounds are inside it), and a branch merged into its left sibling brings its
first child's bound with it (that child's keys are above the branch's first key). The exact
form (`bktKeysB`) does not survive: after the first entry of a branch is removed, its new first
child's exact bound is its parent's, and a later merge of that branch would need the lost one.
The bounds are inside the positions', so the children of a branch keep their keys apart, which
is what `spill` needs to write a strict tree.

A deficient node (`dfc`) is allowed for at most one node, the one being rebalanced: a branch
with one entry (as a branch that lost a child has while it is rebalanced), or an empty leaf no
longer marked unbalanced; every other branch has two entries, every other leaf under a branch
not marked unbalanced has one.
A leaf's entries have no child (`pgid` 0: the reparenting loop of a merge looks a leaf entry's
`pgid` up in `b.nodes`, which has no node for page 0 of a bucket that is not inline).

**What the transaction must give** (`rblReady`, from `txShape`): the exact keys and, beyond
them, `brFirst` and the leaves' `pgid` 0 (both true of bbolt: branches are their pages' until
`Commit`, `Put` and `CreateBucket` put leaf entries with `pgid` 0), and that the nodes' parent pointers
have no cycle (`rblAcyc`; bbolt materializes a node under its parent, which it never moves
before `Commit`), and that all the leaves of a tree are at one depth (`rblHt`, of the nodes and
of the view's pages: a merge of two branches gives the merged one the children of both, which
must be of one kind; bbolt only writes such trees, but `treeStrict` does not say so); they
are not consequences of `txShape` and the clean invariant (a materialized branch's first key is
not tied to its bounds there, a branch's entries not to its page).

**Freed pages** (`freedOK`; their tokens `pgToks γ F`, `freedToks` of `SpillDefs.lean`):
beyond `freedIn` (`SpillDefs.lean`: every slot of a freed page is pending for the
writer), the freed pages are the view's and the writer's pending ids are slots of freed pages
only, so a page freed next is not pending yet (`Free` panics on a page already freed).

**Reachability** (`balancedFrom`, over `WriteTxDeref.lean`'s `bktReach`): `Bucket.rebalance`
visits the buckets reachable through the bucket caches `b.buckets`; no node of them is unbalanced after it
(`txBalanced_of_reach` gives `txBalanced` when every bucket of the transaction is reachable
from its root).
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxShape
public import Proof.go_etcd_io.bbolt.WriteTxDeref
public import Proof.go_etcd_io.bbolt.internal.freelist.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-! ### Keys during rebalance -/

/-- The bound `a` is inside the bound `b`. -/
def bndIn (a b : Option (List w8) × Option (List w8)) : Prop :=
  (∀ y, b.1 = some y → ∃ x, a.1 = some x ∧ ¬ go.GoStringLt x y) ∧
  (∀ y, b.2 = some y → ∃ x, a.2 = some x ∧ ¬ go.GoStringLt y x)

/-- The node `l` (record `r`) of `B` and its keys during rebalance (see the module doc), the
nodes' bounds `bnd`, the deficient node `dfc`. -/
def rblNodeKeys (W : WView) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (dfc : Option Loc) (l : Loc) (r : NRec) : Prop :=
  (∀ w ∈ r.ws, keyIn (bnd l).1 (bnd l).2 w.key) ∧
  (r.nv.parent' ≠ null → r.nv.key' ≠ slice.nil ∧ ∃ rp i w, B.ns !! r.nv.parent' = some rp ∧
    rp.ws[i]? = some w ∧ w.pgid = r.nv.pgid' ∧ w.key = r.key ∧
    bndIn (bnd l) (entryBnd (bnd r.nv.parent') rp.ws i)) ∧
  (r.nv.isLeaf' = false → (dfc ≠ some l → 2 ≤ r.ws.length) ∧
    (∀ x, (bnd l).1 = some x → wKey r.ws 0 = x) ∧
    ∃ kind : Bool, ∀ i w, r.ws[i]? = some w →
    (∀ l', B.nm !! w.pgid = some l' → ∃ r', B.ns !! l' = some r' ∧ r'.nv.isLeaf' = kind) ∧
    (B.nm !! w.pgid = none → ∃ pg, W.pages !! uint.nat w.pgid = some pg ∧ 0 < pageCount pg ∧
      decide (pageFlags pg = leafPageFlag) = kind ∧ pageKey pg 0 = w.key ∧
      treeKeys W.pages (uint.nat w.pgid) (entryBnd (bnd l) r.ws i).1 (entryBnd (bnd l) r.ws i).2)) ∧
  (dfc ≠ some l → r.nv.isLeaf' = true → r.nv.unbalanced' = false → r.nv.parent' ≠ null →
    0 < r.ws.length) ∧
  (r.nv.isLeaf' = true → ∀ w ∈ r.ws, w.pgid = W64 0 ∧ (isBktFlag w.flags →
    inBucketRoot w.value ≠ 0 → treeKeys W.pages (inBucketRoot w.value) none none))

/-- The keys of the bucket `B` during rebalance (see the module doc). -/
def rblKeysB (W : WView) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (dfc : Option Loc) : Prop :=
  (B.bv.rootNode' = null → B.ib.root' ≠ W64 0 → treeKeys W.pages (uint.nat B.ib.root') none none) ∧
  (∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null) ∧
  ∀ l r, B.ns !! l = some r → rblNodeKeys W B bnd dfc l r

/-- The keys of the bucket `B` with no deficient node. -/
def rblKeys (W : WView) (B : BRec) : Prop := ∃ bnd, rblKeysB W B bnd none

/-- The parent pointers of the bucket's nodes have no cycle: a height that a parent exceeds. -/
def rblAcyc (B : BRec) : Prop :=
  ∃ ht : Loc → Nat, ∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null → ht l < ht r.nv.parent'

/-- The pages of `P` have the heights `pht`: a leaf 0, a branch one more than its children. -/
def pageHts (P : GMap Nat (List w8)) (pht : Nat → Nat) : Prop :=
  ∀ id pg, P !! id = some pg → (pageFlags pg = leafPageFlag → pht id = 0) ∧
    (pageFlags pg = branchPageFlag → ∀ i < pageCount pg, pht (branchPgid pg i) + 1 = pht id)

/-- The bucket's nodes and the view's pages have heights (all the leaves of a tree are at one
depth): a leaf 0, a branch one more than its children, nodes or pages. -/
def rblHt (W : WView) (B : BRec) : Prop :=
  ∃ (ht : Loc → Nat) (pht : Nat → Nat), pageHts W.pages pht ∧
    ∀ l r, B.ns !! l = some r → (r.nv.isLeaf' = true → ht l = 0) ∧
      (r.nv.isLeaf' = false → ∀ w ∈ r.ws, (∀ l', B.nm !! w.pgid = some l' → ht l' + 1 = ht l) ∧
        (B.nm !! w.pgid = none → pht (uint.nat w.pgid) + 1 = ht l))

/-- The bucket `bl` (record `B`) during rebalance: clean, its keys (the deficient node `dfc`),
its parent pointers without cycle, its heights. -/
def rblB (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (dfc : Option Loc) : Prop :=
  bktClean W hwm bl B ∧ (∃ bnd, rblKeysB W B bnd dfc) ∧ rblAcyc B ∧ rblHt W B

/-- A branch's lower bound, if any, is its first key. -/
def brFirst (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8)) : Prop :=
  ∀ l r, B.ns !! l = some r → r.nv.isLeaf' = false → ∀ x, (bnd l).1 = some x → wKey r.ws 0 = x

/-- A leaf's entries have no child page. -/
def leafPg0 (B : BRec) : Prop :=
  ∀ l r, B.ns !! l = some r → r.nv.isLeaf' = true → ∀ w ∈ r.ws, w.pgid = W64 0

/-- What `rebalance` needs of the transaction's keys, beyond `txShape` (see the module doc). -/
def rblReady (W : WView) (T : WTx) : Prop :=
  ∀ bl B, T.bs !! bl = some B → (∃ bnd, bktKeysB W B bnd ∧ brFirst B bnd) ∧ leafPg0 B ∧
    rblAcyc B ∧ rblHt W B

/-! ### Siblings -/

/-- `j` is where a search for `key` lands among the entries `ws` (`childIndex`). -/
def wSearch (ws : List WEntry) (key : List w8) (j : Nat) : Prop :=
  j ≤ ws.length ∧ (∀ k < j, go.GoStringLt (wKey ws k) key) ∧
    (j < ws.length → ¬ go.GoStringLt (wKey ws j) key)

theorem wSearch_of (ws : List WEntry) (es : List NodeEntry) (h : wMatch ws es) (key : List w8)
    (j : Nat) (hs : isSearchIdx es key j) : wSearch ws key j := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hl := wMatch_length h
  refine ⟨by rw [hl]; exact h1, fun k hk => ?_, fun hj => ?_⟩
  · rw [← wMatch_key ws es h]; exact h2 k hk
  · rw [← wMatch_key ws es h]; exact h3 (by rw [← hl]; exact hj)

/-- What `n.nextSibling()` (`next`) or `n.prevSibling()` of the node `r` did: nothing (a root,
or no such sibling), or `b.node` of the parent's entry after (before) the one `childIndex`
finds for the node's key (`j`), read from `p` (`pg`, `src`) if not materialized. -/
def siblingAt (W : WView) (B : BRec) (pm : GMap w64 Loc) (bl : Loc) (r : NRec) (next : Bool)
    (l : Loc) (B' : BRec) (st st' : go_etcd_io.bbolt.TxStats) : Prop :=
  (r.nv.parent' = null ∧ l = null ∧ B' = B ∧ st' = st) ∨
  ∃ rp j, B.ns !! r.nv.parent' = some rp ∧ wSearch rp.ws r.key j ∧
    (((if next then rp.ws.length ≤ j + 1 else j = 0) ∧ l = null ∧ B' = B ∧ st' = st) ∨
     ∃ i w p pg src, (if next then i = j + 1 else i + 1 = j) ∧ rp.ws[i]? = some w ∧
       (B.nm !! w.pgid = none → nodeSrcOK W B pm w.pgid p pg src) ∧
       nodeRes B bl w.pgid r.nv.parent' p pg src l B' st st')

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

/-! ### Reachable buckets -/

/-- No node of a bucket reachable from `b` is unbalanced. -/
def balancedFrom (T : WTx) (b : Loc) : Prop :=
  ∀ c, bktReach T b c → ∀ C, T.bs !! c = some C → ∀ l r, C.ns !! l = some r →
    r.nv.unbalanced' = false

/-- `txBalanced` (`SpillDefs.lean`) when every bucket is reachable from `rl`. -/
theorem txBalanced_of_reach (T : WTx) (rl : Loc)
    (hr : ∀ c, (T.bs !! c).isSome → bktReach T rl c) (h : balancedFrom T rl) :
    ∀ bl B, T.bs !! bl = some B → ∀ l r, B.ns !! l = some r → r.nv.unbalanced' = false := by
  intro c C hC l r hr'
  exact h c (hr c (by rw [hC]; rfl)) C hC l r hr'

/-! ### Freed pages -/

/-- The freed pages `F` (see the module doc): their slots pending for `txid`, they are the
view's, and the pending ids of `txid` are their slots only. -/
def freedOK (W : WView) (fl : FLState) (txid : w64) (F : GMap Nat (List w8)) : Prop :=
  (∀ id pg, F !! id = some pg → ∀ k < 1 + pageOverflow pg,
    ∃ pd, fl.pending !! txid = some pd ∧ W64 ((id + k : Nat) : Int) ∈ pd.ids) ∧ (∀ id pg, F !! id = some pg → W.pages !! id = some pg) ∧
  ∀ pd, fl.pending !! txid = some pd → ∀ x ∈ pd.ids,
    ∃ id pg k, F !! id = some pg ∧ k < 1 + pageOverflow pg ∧ x = W64 ((id + k : Nat) : Int)

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The write transaction's shape during and after rebalance: `txShape` with the keys
`rblKeys`. -/
def txShapeR (γ : GName) (W : WView) (T : WTx) : IProp GF :=
  iprop(∃ (M : GMap Nat Unit), ghostMapAuth γ 1 M ∗
    ⌜∀ id, (M !! id).isSome ↔ (W.pages !! id).isSome⌝ ∗
    ([∗map] _bl ↦ B ∈ T.bs, bktToks γ W B) ∗
    ⌜∀ bl B, T.bs !! bl = some B → rblKeys W B ∧ bktNested W T B⌝)

/-- The transaction's fields `rebalance` uses: its stats, its page cache (empty), its
database, its meta. -/
def rblTx (txl : Loc) (st : TxStats) (pmap : GoMap) (mp : Loc) (mv : Meta) (dbl : Loc) :
    IProp GF :=
  iprop(structFieldRef Tx go!"stats" txl ↦ st ∗ structFieldRef Tx go!"pages" txl ↦ pmap ∗
    pmap ↦$ (∅ : GMap w64 Loc) ∗ structFieldRef Tx go!"db" txl ↦ dbl ∗
    structFieldRef Tx go!"meta" txl ↦ mp ∗ mp ↦ mv)

end own

end bbolt
end EtcdGrove
end Perennial
