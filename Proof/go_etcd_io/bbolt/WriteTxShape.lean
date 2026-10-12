/-
What a write transaction keeps, beyond its clean invariant (`txClean`), for `Commit` to write
a strict tree (`treeStrict`) that shares no page with the pages it frees, the free ones or the
pending ones: `txShape`.

**Page tokens.** The transaction owns a ghost map (name `γ`) whose keys are page ids: one
exclusive token `id ↪[γ] ()` per page of the current tree (and, during `Commit`, per page it
allocated). Every token sits with exactly one *position* of the transaction's logical tree, so
two positions hold disjoint sets of pages and a tree assembled from separately held parts shares
no page (`viewUnique`) by separation alone. The positions of a bucket `B` (`bktToks`):
- `B` without a materialized root: its whole tree (`xPages`), but for the nested buckets `B`
  has opened (`B.buckets`, keyed by name: `opened`), which hold their own trees;
- otherwise each node: its own page (the one it was read from: id `pgid`, none for a node of an
  inline page), and, a branch, each child it has not materialized (`B.nodes` has no node for
  it): that child's subtree (`xPages`), or, a leaf, each nested bucket stored in pages that `B`
  has not opened: that bucket's whole tree (`treePages`).
`xPages pages op c` is the tree under `c` without the nested buckets whose key `op` holds (the
trees of the opened ones). The ghost map's authority knows exactly the view's page ids
(`txShape`), so a page `Commit` allocates gets a fresh token.

**Keys** (`bktKeys`, the transaction's side of `treeKeys`): each node has bounds (`bnd`, from
its parent's entry for it, `entryBnd`), its keys are inside them; a node under a parent was
read with the key of the parent's entry for it (`n.key`, what `spill` replaces), and is not
empty unless a delete marked it unbalanced (a leaf; a branch has two entries); a branch's
children are all leaves or all branches; a child not materialized is a page whose first key is
its entry's and whose tree has the entry's bounds (`treeKeys`).

**Nested buckets** (`bktNested`): an opened bucket `C` (name `k`) is the value of `B`'s entry
`k` (`entryIn`: in a materialized leaf, or on a page of a position of `B`): its root is the
value's, and, if `C` has no materialized root (it did not change), its header is the value's.
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxPred
public import Proof.go_etcd_io.bbolt.BucketOpen
public import Proof.go_etcd_io.bbolt.TreeKeys
public import Proof.go_etcd_io.bbolt.WriteCursor
public import Perennial.Ghost.GhostMap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

/-! ### Positions' pages -/

/-- Page `id` is a page of the tree under `root` in `pages`, but for the nested buckets whose
key `op` holds (and their trees). -/
inductive xHas (pages : GMap Nat (List w8)) (op : List w8 → Prop) : Nat → Nat → Prop
  | root (root : Nat) (pg : List w8) : pages !! root = some pg → xHas pages op root root
  | child (root : Nat) (pg : List w8) (i id : Nat) :
      pages !! root = some pg → pageFlags pg = branchPageFlag → i < pageCount pg →
      xHas pages op (branchPgid pg i) id → xHas pages op root id
  | bucket (root : Nat) (pg : List w8) (i id : Nat) :
      pages !! root = some pg → pageFlags pg = leafPageFlag → i < pageCount pg →
      leafFlags pg i % 2 = bucketLeafFlag → ¬ op (leafKey pg i) →
      bucketHas pages (leafValue pg i) id → xHas pages op root id

/-- Page `id` is a page of the bucket tree under `root`, not of a nested bucket's tree. -/
inductive ownHas (pages : GMap Nat (List w8)) : Nat → Nat → Prop
  | root (root : Nat) (pg : List w8) : pages !! root = some pg → ownHas pages root root
  | child (root : Nat) (pg : List w8) (i id : Nat) :
      pages !! root = some pg → pageFlags pg = branchPageFlag → i < pageCount pg →
      ownHas pages (branchPgid pg i) id → ownHas pages root id

section keys
variable [ext : FfiSyntax]

open Classical in
/-- The pages `xHas` reaches. -/
def xPages (pages : GMap Nat (List w8)) (op : List w8 → Prop) (c : Nat) : GMap Nat (List w8) :=
  GMap.filter (fun id _ => decide (xHas pages op c id)) pages

/-- The nested bucket named `k` is open in `B`. -/
def opened (B : BRec) (k : List w8) : Prop := (B.bm !! k).isSome

/-- The page positions of `B`: its root page if it has no materialized root, else the children
its branch nodes have not materialized. -/
def posRoot (B : BRec) (c : Nat) : Prop :=
  (B.bv.rootNode' = null ∧ B.ib.root' ≠ W64 0 ∧ c = uint.nat B.ib.root') ∨
  ∃ l i, pagePosAt B l i (W64 (c : Int)) ∧ c < 2 ^ 64

/-! ### Keys -/

/-- The bounds of entry `i`'s child, under a node with the entries `ws` and the bounds `b`. -/
def entryBnd (b : Option (List w8) × Option (List w8)) (ws : List WEntry) (i : Nat) :
    Option (List w8) × Option (List w8) :=
  (childLo b.1 (wKey ws) i, childHi b.2 (wKey ws) ws.length i)

/-- The node `l` (record `r`) of `B` and its keys (see the module doc), the nodes' bounds
`bnd`. -/
def nodeKeys (W : WView) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (l : Loc) (r : NRec) : Prop :=
  (∀ w ∈ r.ws, keyIn (bnd l).1 (bnd l).2 w.key) ∧
  (r.nv.parent' = null → bnd l = (none, none)) ∧
  (r.nv.parent' ≠ null → r.nv.key' ≠ slice.nil ∧ ∃ rp i w, B.ns !! r.nv.parent' = some rp ∧
    rp.ws[i]? = some w ∧ w.pgid = r.nv.pgid' ∧ w.key = r.key ∧
    bnd l = entryBnd (bnd r.nv.parent') rp.ws i) ∧
  (r.nv.isLeaf' = false → 2 ≤ r.ws.length ∧ ∃ kind : Bool, ∀ i w, r.ws[i]? = some w →
    (∀ l', B.nm !! w.pgid = some l' → ∃ r', B.ns !! l' = some r' ∧ r'.nv.isLeaf' = kind) ∧
    (B.nm !! w.pgid = none → ∃ pg, W.pages !! uint.nat w.pgid = some pg ∧ 0 < pageCount pg ∧
      decide (pageFlags pg = leafPageFlag) = kind ∧ pageKey pg 0 = w.key ∧
      treeKeys W.pages (uint.nat w.pgid) (entryBnd (bnd l) r.ws i).1 (entryBnd (bnd l) r.ws i).2)) ∧
  (r.nv.isLeaf' = true → r.nv.unbalanced' = false → r.nv.parent' ≠ null → 0 < r.ws.length) ∧
  (r.nv.isLeaf' = true → ∀ w ∈ r.ws, isBktFlag w.flags → inBucketRoot w.value ≠ 0 →
    treeKeys W.pages (inBucketRoot w.value) none none)

/-- The keys of the bucket `B` (see the module doc), its nodes' bounds `bnd`. -/
def bktKeysB (W : WView) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8)) : Prop :=
  (B.bv.rootNode' = null → B.ib.root' ≠ W64 0 → treeKeys W.pages (uint.nat B.ib.root') none none) ∧
  (∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null) ∧
  ∀ l r, B.ns !! l = some r → nodeKeys W B bnd l r

/-- The keys of the bucket `B` (see the module doc). -/
def bktKeys (W : WView) (B : BRec) : Prop := ∃ bnd, bktKeysB W B bnd

/-! ### A cursor's descent by a key -/

/-- The keys of position `pid` of `B` (its node's entries', or its page's). -/
def keysAt (W : WView) (B : BRec) (pid : w64) : Option (List (List w8)) :=
  match resolve B pid with
  | some l => (B.ns !! l).map fun r => r.ws.map WEntry.key
  | none => (wpageAt W B pid).map fun lp => (List.range (pageCount lp.2)).map (pageKey lp.2)

/-- Entry `i` of a branch with the keys `ks` is where a search for `k` descends: the last one
whose key is at most `k`, or the first. -/
def routes (ks : List (List w8)) (i : Nat) (k : List w8) : Prop :=
  i < ks.length ∧ (i = 0 ∨ ∃ ki, ks[i]? = some ki ∧ ¬ go.GoStringLt k ki) ∧
  ∀ kn, ks[i + 1]? = some kn → go.GoStringLt k kn

/-- The stack elements `es`, from position `pid` down, descend by the key `k` (`Cursor.search`):
at each branch the entry `routes` picks. -/
def kroute (W : WView) (B : BRec) (k : List w8) : w64 → List elemRef → Prop
  | _, [] => False
  | _, [_] => True
  | pid, r :: r2 :: rs => ∃ ks cs c, keysAt W B pid = some ks ∧
      routes ks (sint.Z r.index').toNat k ∧ kidsAt W B pid = some (false, cs) ∧
      cs[(sint.Z r.index').toNat]? = some c ∧ kroute W B k c (r2 :: rs)

/-! ### Nested buckets -/

/-- `B`'s entry named `k` is a nested bucket with the value `v`: in one of its materialized
leaves, or on a page of one of its positions. -/
def entryIn (W : WView) (B : BRec) (k v : List w8) : Prop :=
  (∃ l r w, B.ns !! l = some r ∧ r.nv.isLeaf' = true ∧ w ∈ r.ws ∧ w.key = k ∧
    isBktFlag w.flags ∧ w.value = v) ∨
  (∃ c p pg i, posRoot B c ∧ ownHas W.pages c p ∧ W.pages !! p = some pg ∧
    pageFlags pg = leafPageFlag ∧ i < pageCount pg ∧ leafKey pg i = k ∧
    leafFlags pg i % 2 = bucketLeafFlag ∧ leafValue pg i = v)

/-- The buckets `B` opened are its entries' (see the module doc). -/
def bktNested (W : WView) (T : WTx) (B : BRec) : Prop :=
  ∀ k c, B.bm !! k = some c → ∃ C v, T.bs !! c = some C ∧ entryIn W B k v ∧ 16 ≤ v.length ∧
    C.ib.root' = (ibOf v).root' ∧ (C.bv.rootNode' = null → C.ib = ibOf v)

end keys

/-! ### Tokens -/

section toks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- The tokens of the pages `P`. -/
def pgToks (γ : GName) (P : GMap Nat (List w8)) : IProp GF :=
  [∗map] id ↦ _pg ∈ P, id ↪[γ] ()

open Classical in
/-- The page of the node `l` (record `r`) of `B`, and its positions' pages (see the module
doc). -/
def nodeToks (γ : GName) (W : WView) (B : BRec) (r : NRec) : IProp GF :=
  iprop((if r.nv.pgid' = W64 0 then emp else
      pgToks γ (GMap.filter (fun id _ => decide (id = uint.nat r.nv.pgid')) W.pages)) ∗
    [∗list] w ∈ r.ws,
      if r.nv.isLeaf' = true then
        (if isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B w.key then
          pgToks γ (treePages W.pages (inBucketRoot w.value)) else emp)
      else (if B.nm !! w.pgid = none then pgToks γ (xPages W.pages (opened B) (uint.nat w.pgid))
        else emp))

open Classical in
/-- The tokens of the bucket `B`'s positions (see the module doc). -/
def bktToks (γ : GName) (W : WView) (B : BRec) : IProp GF :=
  if B.bv.rootNode' = null then
    (if B.ib.root' = W64 0 then emp else pgToks γ (xPages W.pages (opened B) (uint.nat B.ib.root')))
  else [∗map] _l ↦ r ∈ B.ns, nodeToks γ W B r

/-- A bucket's part of the shape: its tokens and its keys (`bktNested`, about the
transaction's buckets, is `txShape`'s). -/
def bktShape (γ : GName) (W : WView) (B : BRec) : IProp GF :=
  iprop(bktToks γ W B ∗ ⌜bktKeys W B⌝)

/-- The write transaction's shape (see the module doc), its tokens' ghost map `γ`. -/
def txShape (γ : GName) (W : WView) (T : WTx) : IProp GF :=
  iprop(∃ (M : GMap Nat Unit), ghostMapAuth γ 1 M ∗
    ⌜∀ id, (M !! id).isSome ↔ (W.pages !! id).isSome⌝ ∗
    ([∗map] _bl ↦ B ∈ T.bs, bktToks γ W B) ∗
    ⌜∀ bl B, T.bs !! bl = some B → bktKeys W B ∧ bktNested W T B⌝)

end toks

end bbolt
end EtcdGrove
end Perennial
