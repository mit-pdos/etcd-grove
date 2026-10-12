/-
A write transaction's objects as pure records (the predicate is `WriteTxPred.lean`).

**The view.** A writer reads the current tree through the database's mapping, as a reader does:
`WView` records where (`data`, the page size `ps`), the pages it sees (`pages`, page id ↦ bytes)
and its fraction `q` of them, and the database fields it reads (`logger`). Between operations
the transaction holds the view whole (`WriteTxPred.lean`'s `wView`).

**Sources.** The bytes of a slice the transaction keeps (a node entry's key or value, a node's
key, an inline bucket's page) are in the view (`Src.view`: a pure fact, `inViewAt`, says which
bytes of which page; the transaction holds no part of them apart from the view), held at a
fraction (`Src.own dq`: heap copies, the caller's values), or in an old mapping (`Src.stale`,
after a remap: never read again).

**Records.** A node (`NRec`): its struct, its inodes and their entries (`WEntry`: flags, child
page, key and value bytes, sources), its children slice, its key. A bucket (`BRec`): its struct,
its `InBucket` header, its node cache `nodes` (`nm`), its bucket cache `buckets` (`bm`), the nodes
it owns (`ns`, location ↦ record), its inline page. The transaction (`WTx`): its struct, its meta
copy, its page cache `pages` (`pm`) and the buffers' bytes (`bufs`), the buckets it owns (`bs`).

**The clean invariant** (`txClean`, before `Commit` spills): every bucket's logical tree is
well-formed. A bucket's position `c` (a page id) is its node `nm[c]` if materialized, else page
`c` of the view; every node is locally well-formed (`nodeClean`: sorted, non-empty keys, a
branch non-empty with its children below the high-water mark, materialized or a well-formed
page tree; a leaf's nested-bucket values well-formed), parents and children lists agree, and
the page positions under nodes (`pagePosAt`) have disjoint subtrees with no node in them
(`posDisjoint`, `posNodeFree`), so that materializing one keeps the others node-free.

**What the view must satisfy** (`viewOK`, from the database layer, beyond the tree being
`treeWF`): every page is readable (non-empty keys: `ReadInodeFromPage` panics otherwise), an
inline bucket's page has id 0 and no nested bucket (bbolt writes no other), and no page is
shared (the subtrees of a branch's children are disjoint and do not contain the branch).
-/
module

public import Proof.go_etcd_io.bbolt.NodeModel
public import Proof.go_etcd_io.bbolt.TreeStrict
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsValidPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

/-- Where the bytes of a slice the transaction keeps are (see the module doc). -/
inductive Src where
  | view
  | own (dq : DFrac)
  | stale

/-- A node's inode as the transaction keeps it: the entry and its bytes' sources. -/
structure WEntry where
  flags : w32
  pgid : w64
  key : List w8
  value : List w8
  ks : Src
  vs : Src

section view
variable [ext : FfiSyntax]

/-- The writer's view of the current tree (see the module doc). -/
structure WView where
  dbl : Loc
  data : Loc
  ps : Nat
  pages : GMap Nat (List w8)
  q : Qp
  /-- `db.logger`, and the default logger's address (`discardLogger`'s value). -/
  lg : GoInterface
  dl : Loc
  /-- `db.freelist` (the writer holds half of the field). -/
  fli : GoInterface
  /-- The view's high-water mark (the current meta's `pgid`). -/
  hwm : Nat

/-- The bytes `bs` at `p` are bytes of a page of the view. -/
def inViewLoc (W : WView) (p : Loc) (bs : List w8) : Prop :=
  ∃ (id : Nat) (pg : List w8) (off : Nat), W.pages !! id = some pg ∧
    off + bs.length ≤ pg.length ∧ bytesAt pg off bs.length = bs ∧
    p = W.data +ₗ ((id * W.ps + off : Nat) : Int)

/-- The slice `s` is the bytes `bs` of a page of the view. -/
def inViewAt (W : WView) (s : GoSlice) (bs : List w8) : Prop :=
  inViewLoc W s.ptr bs ∧ bs.length < 2 ^ 32 ∧ s.len = W64 (bs.length : Int) ∧
    s.cap = W64 (bs.length : Int)

/-- A node (see the module doc). -/
structure NRec where
  nv : node
  ins : List Inode
  ws : List WEntry
  cs : List Loc
  key : List w8
  ksrc : Src

/-- A bucket (see the module doc). -/
structure BRec where
  bv : Bucket
  ib : InBucket
  nm : GMap w64 Loc
  bm : GMap GoString Loc
  ns : GMap Loc NRec
  ipg : List w8
  isrc : Src

/-- A write transaction (see the module doc). -/
structure WTx where
  t : Tx
  mv : Meta
  pm : GMap w64 Loc
  bufs : GMap w64 (List w8)
  bs : GMap Loc BRec

end view

/-! ### Entries -/

/-- The key of entry `i` (empty past the end). -/
def wKey (ws : List WEntry) (i : Nat) : List w8 := ((ws[i]?).map WEntry.key).getD []

/-- The entries' keys increase strictly. -/
def wsSorted (ws : List WEntry) : Prop :=
  ∀ i j, i < j → j < ws.length → go.GoStringLt (wKey ws i) (wKey ws j)

/-- The node entries `es` are the entries `ws` (with the fractions of what `ws` holds). -/
def wMatch1 (w : WEntry) (e : NodeEntry) : Prop :=
  e.flags = w.flags ∧ e.pgid = w.pgid ∧ e.key = w.key ∧ e.value = w.value ∧
  (∀ d, w.ks = Src.own d → e.kq = d) ∧ (∀ d, w.vs = Src.own d → e.vq = d)

def wMatch (ws : List WEntry) (es : List NodeEntry) : Prop := List.Forall₂ wMatch1 ws es

theorem wMatch_length {ws : List WEntry} {es : List NodeEntry} (h : wMatch ws es) :
    ws.length = es.length := List.Forall₂.length_eq h

theorem wMatch_key (ws : List WEntry) (es : List NodeEntry) (h : wMatch ws es) (i : Nat) :
    entryKey es i = wKey ws i := by
  induction h generalizing i with
  | nil => rfl
  | cons h1 _ ih =>
    cases i with
    | zero => simp [entryKey, wKey, h1.2.2.1]
    | succ i => simpa [entryKey, wKey] using ih i

theorem wMatch_sorted (ws : List WEntry) (es : List NodeEntry) (h : wMatch ws es) :
    entriesSorted es ↔ wsSorted ws := by
  unfold entriesSorted wsSorted
  rw [← wMatch_length h]
  simp only [wMatch_key ws es h]

/-- The entries of a node hold no stale bytes. -/
def wsLive (ws : List WEntry) : Prop := ∀ w ∈ ws, w.ks ≠ Src.stale ∧ w.vs ≠ Src.stale

/-- A nested bucket's flag (`BucketLeafFlag`). -/
def isBktFlag (f : w32) : Prop := f &&& W32 1 ≠ W32 0

/-! ### Nodes read from pages (`Bucket.node`) -/

section readnode
variable [ext : FfiSyntax]

/-- The entries a node reads from the page `pg` (`ReadInodeFromPage`), their bytes from
`src` (a branch's values are nil). -/
def pageW (pg : List w8) (src : Src) (i : Nat) : WEntry :=
  if pageFlags pg = leafPageFlag then
    ⟨W32 (leafFlags pg i), W64 0, leafKey pg i, leafValue pg i, src, src⟩
  else ⟨W32 0, W64 (branchPgid pg i), branchKey pg i, [], src, Src.own DFrac.discard⟩

def pageWs (pg : List w8) (src : Src) : List WEntry :=
  (List.range (pageCount pg)).map (pageW pg src)

theorem pageWs_length (pg : List w8) (src : Src) : (pageWs pg src).length = pageCount pg := by
  simp [pageWs]


/-- Where `b.node(pgid, _)` reads a node from (`p`, its bytes `pg`, from the source `src`): the
inline page `b.page` (`pgid` 0; in the view or in persistent heap bytes), else page `pgid` of the
view, which is not a dirty page (`pm`, the transaction's page cache). -/
def nodeSrcOK (W : WView) (B : BRec) (pm : GMap w64 Loc) (pgid : w64) (p : Loc) (pg : List w8)
    (src : Src) : Prop :=
  pageReadable pg ∧ p.locCar ≠ 0 ∧
  (B.bv.page' ≠ null → pgid = W64 0 ∧ p = B.bv.page' ∧ pg = B.ipg ∧ src = B.isrc ∧
    (src = Src.view ∨ src = Src.own DFrac.discard) ∧ pageId pg = 0) ∧
  (B.bv.page' = null → pm !! pgid = none ∧ src = Src.view ∧
    W.pages !! uint.nat pgid = some pg ∧ p = W.data +ₗ ((uint.nat pgid * W.ps : Nat) : Int) ∧
    W64 (pageId pg) = pgid ∧ validPageFlags (W16 (pageFlags pg)) ∧
    uint.nat pgid * W.ps < 281474976710655)

/-- The node `n.read(p)` makes of the page `pg` at `p` (a node of the bucket `bl`, under
`parent`; its inodes the slice `s`). -/
def readNodeV (bl parent : Loc) (p : Loc) (pg : List w8) (s : GoSlice) : node :=
  { bucket' := bl, isLeaf' := decide (pageFlags pg = leafPageFlag), unbalanced' := false,
    spilled' := false,
    key' := if pageCount pg = 0 then slice.nil else (inodeOf p pg 0).key',
    pgid' := W64 (pageId pg), parent' := parent, children' := slice.nil, inodes' := s }

/-- Its record (the bytes of its entries from `src`). -/
def readNRec (bl parent : Loc) (p : Loc) (pg : List w8) (s : GoSlice) (src : Src) : NRec :=
  ⟨readNodeV bl parent p pg s, inodesOf p pg, pageWs pg src, [], wKey (pageWs pg src) 0, src⟩

/-- The node `l` added under `parent` (whose children slice becomes `cs'`). -/
def parentAdd (ns : GMap Loc NRec) (parent l : Loc) (cs' : GoSlice) : GMap Loc NRec :=
  if parent = null then ns else
  match ns !! parent with
  | some rp => <[parent := { rp with nv := { rp.nv with children' := cs' }, cs := rp.cs ++ [l] }]> ns
  | none => ns

/-- The bucket after `b.node(pgid, parent)` made the node `l` (record `r`). -/
def nodeAdded (B : BRec) (pgid : w64) (parent l : Loc) (r : NRec) (cs' : GoSlice) : BRec :=
  { B with
    bv := if parent = null then { B.bv with rootNode' := l } else B.bv
    nm := <[pgid := l]> B.nm
    ns := <[l := r]> (parentAdd B.ns parent l cs')
    isrc := match B.isrc with
      | .own _ => if B.bv.page' = null then B.isrc else Src.own DFrac.discard
      | s => s }

/-- What `b.node(pgid, parent)` did: the cached node `l`, or a new one (see `Bucket.node.spec`). -/
def nodeRes (B : BRec) (bl : Loc) (pgid : w64) (parent p : Loc) (pg : List w8) (src : Src)
    (l : Loc) (B' : BRec) (st st' : go_etcd_io.bbolt.TxStats) : Prop :=
  (B.nm !! pgid = some l ∧ B' = B ∧ st' = st) ∨
  (B.nm !! pgid = none ∧ B.ns !! l = none ∧ l ≠ null ∧
    st' = { st with NodeCount' := st.NodeCount' + W64 1 } ∧
    ∃ (s cs' : GoSlice) (src' : Src), (src = Src.view → src' = Src.view) ∧
      (src ≠ Src.view → src' = Src.own DFrac.discard) ∧
      B' = nodeAdded B pgid parent l (readNRec bl parent p pg s src') cs')

end readnode

/-! ### The view's facts -/

section facts
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- The view's facts (see the module doc), with the high-water mark `hwm`. -/
def viewOK (W : WView) : Prop :=
  W.data.locCar ≠ 0 ∧ 80 ≤ W.ps ∧ W.ps < 2 ^ 32 ∧
  (∀ id pg, W.pages !! id = some pg → id * W.ps < 281474976710655) ∧
  pagesStrict W.pages

/-- A nested bucket's value, well-formed and good. -/
def bvalOK (pages : GMap Nat (List w8)) (hwm : Nat) (v : List w8) : Prop :=
  bucketWF pages hwm v ∧ (inBucketRoot v = 0 → inlineGood (inlinePage v))

end facts

/-! ### The clean invariant -/

section clean
variable [ext : FfiSyntax]

/-- Entry `i` of the branch node `l` is a page position: its child `c` is not materialized. -/
def pagePosAt (B : BRec) (l : Loc) (i : Nat) (c : w64) : Prop :=
  ∃ r w, B.ns !! l = some r ∧ r.nv.isLeaf' = false ∧ r.ws[i]? = some w ∧ w.pgid = c ∧
    B.nm !! c = none

/-- Distinct page positions have disjoint subtrees. -/
def posDisjoint (W : WView) (B : BRec) : Prop :=
  ∀ l1 i1 c1 l2 i2 c2, pagePosAt B l1 i1 c1 → pagePosAt B l2 i2 c2 → (l1, i1) ≠ (l2, i2) →
    ∀ d, treeHas W.pages (uint.nat c1) d → ¬ treeHas W.pages (uint.nat c2) d

/-- No page of a page position's subtree is materialized. -/
def posNodeFree (W : WView) (B : BRec) : Prop :=
  ∀ l i c, pagePosAt B l i c → ∀ d, treeHas W.pages (uint.nat c) d → B.nm !! W64 (d : Int) = none

/-- An inline bucket's page, as the bucket reads it. -/
def inlineOK (ipg : List w8) : Prop := inlineGood ipg

/-- The node `l` (record `r`) of the bucket `bl` (record `B`) is well-formed (see the module
doc), the transaction's high-water mark being `hwm`. -/
def nodeClean (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (l : Loc) (r : NRec) : Prop :=
  r.nv.bucket' = bl ∧ r.ins.length = r.ws.length ∧ wsSorted r.ws ∧
  (∀ w ∈ r.ws, 0 < w.key.length) ∧ wsLive r.ws ∧ r.nv.spilled' = false ∧
  B.nm !! r.nv.pgid' = some l ∧
  (B.ib.root' = W64 0 → r.nv.pgid' = W64 0) ∧
  (B.ib.root' ≠ W64 0 → treeWF W.pages hwm (uint.nat r.nv.pgid')) ∧
  (r.nv.key' = slice.nil ∨ (0 < r.key.length ∧ r.ksrc ≠ Src.stale)) ∧
  (r.nv.isLeaf' = true → ∀ w ∈ r.ws, isBktFlag w.flags → bvalOK W.pages hwm w.value) ∧
  (r.nv.isLeaf' = false → 0 < r.ws.length ∧ (r.ws.map WEntry.pgid).Nodup ∧ ∀ w ∈ r.ws,
    uint.nat w.pgid < hwm ∧
    (∀ l', B.nm !! w.pgid = some l' → ∃ r', B.ns !! l' = some r' ∧ r'.nv.parent' = l) ∧
    (B.nm !! w.pgid = none → treeWF W.pages hwm (uint.nat w.pgid))) ∧
  (r.nv.parent' = null → B.bv.rootNode' = l) ∧
  (r.nv.parent' ≠ null → ∃ rp, B.ns !! r.nv.parent' = some rp ∧ rp.nv.isLeaf' = false ∧
    l ∈ rp.cs ∧ ∃ w ∈ rp.ws, w.pgid = r.nv.pgid') ∧
  r.cs.Nodup ∧ (∀ c ∈ r.cs, ∃ rc, B.ns !! c = some rc ∧ rc.nv.parent' = l)

/-- The bucket `bl` (record `B`) is well-formed (see the module doc). -/
def bktClean (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) : Prop :=
  (B.ib.root' = W64 0 → B.bv.rootNode' = null →
    B.bv.page' ≠ null ∧ (B.isrc = Src.view ∨ B.isrc = Src.own DFrac.discard) ∧ inlineOK B.ipg) ∧
  (B.ib.root' ≠ W64 0 → uint.nat B.ib.root' < hwm ∧
    (B.bv.rootNode' = null → treeWF W.pages hwm (uint.nat B.ib.root'))) ∧
  (B.bv.rootNode' = null → B.ns = ∅ ∧ B.nm = ∅) ∧
  (B.bv.rootNode' ≠ null → B.nm !! B.ib.root' = some B.bv.rootNode') ∧
  (∀ c l, B.nm !! c = some l → l ≠ null ∧ ∃ r, B.ns !! l = some r ∧ r.nv.pgid' = c) ∧
  (B.ib.root' ≠ W64 0 → B.bv.page' = null) ∧
  (B.ib.root' = W64 0 → ∀ l r, B.ns !! l = some r → r.nv.isLeaf' = true) ∧
  (∀ l r, B.ns !! l = some r → nodeClean W hwm bl B l r) ∧
  posDisjoint W B ∧ posNodeFree W B

end clean

end bbolt
end EtcdGrove
end Perennial
