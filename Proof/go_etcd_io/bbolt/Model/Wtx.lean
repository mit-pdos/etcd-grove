/-
A write transaction's objects as pure records (U0a of `notes/bbolt-proof-plan.md`; design
§3.2, §3.13), ported from `old/bbolt/.../{WriteTxModel,WriteCursor,WriteTxShape,NodePages}.lean`
over a `View` (in place of the old `WView`).

**Sources.** A slice the transaction keeps (an entry's key or value, a node's key, an inline
bucket's page) is in the view (`Src.view`, a pure fact on `X.v`), held at a fraction
(`Src.own dq`: heap copies, the caller's values), or in an old mapping (`Src.stale`).

**Records.** A node (`NRec`), a bucket (`BRec`, with its nodes `ns`), the transaction (`WTx`,
its buckets `bs` and the nodes and buckets no longer reachable, `dead`, `deadB`). `WX` adds the
live sets (nodes', buckets'), the handle
map, the node-location registry and the base view (§3.13). Its `wOK` is the old clean invariant
(`txClean`), keys (`bktKeys`), nested buckets (`bktNested`) and nodes' pages (`txPg`).

The records are countable (they are stored in `boltTx`'s agreed ghost state, `Inv/Tx.lean`).
-/
module

public import Proof.go_etcd_io.bbolt.Model.Mvcc
public import GeneratedProof.go_etcd_io.bbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

/-! ## Countable instances (the records live in ghost state) -/

-- `Qp` and `DFrac` are countable by Iris's and Perennial's instances (`Std/Qextra.lean`).

section wtx
variable [GooseExts]

instance InBucket.countable : Pos.Countable InBucket :=
  countableOfLeftInverse (fun v => (v.root', v.sequence')) (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

instance Meta.countable : Pos.Countable Meta :=
  countableOfLeftInverse
    (fun v => (v.magic', v.version', v.pageSize', v.flags', v.root', v.freelist', v.pgid',
      v.txid', v.checksum'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩) (fun _ => rfl)

instance Inode.countable : Pos.Countable Inode :=
  countableOfLeftInverse (fun v => (v.flags', v.pgid', v.key', v.value'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

instance TxStats.countable : Pos.Countable TxStats :=
  countableOfLeftInverse
    (fun v => (v.PageCount', v.PageAlloc', v.CursorCount', v.NodeCount', v.NodeDeref',
      v.Rebalance', v.RebalanceTime', v.Split', v.Spill', v.SpillTime', v.Write', v.WriteTime'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2⟩) (fun _ => rfl)

instance Bucket.countable : Pos.Countable Bucket :=
  countableOfLeftInverse
    (fun v => (v.InBucket', v.tx', v.buckets', v.page', v.rootNode', v.nodes', v.FillPercent'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩)
    (fun _ => rfl)

instance Tx.countable : Pos.Countable Tx :=
  countableOfLeftInverse
    (fun v => (v.writable', v.managed', v.db', v.meta', v.root', v.pages', v.stats',
      v.commitHandlers', v.WriteFlag'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩) (fun _ => rfl)

instance node.countable : Pos.Countable node :=
  countableOfLeftInverse
    (fun v => (v.bucket', v.isLeaf', v.unbalanced', v.spilled', v.key', v.pgid', v.parent',
      v.children', v.inodes'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩) (fun _ => rfl)

/-! ## The records -/

/-- Where the bytes of a slice the transaction keeps are (see the module doc). -/
inductive Src where
  | view
  | own (dq : DFrac)
  | stale
  deriving Inhabited

instance Src.countable : Pos.Countable Src :=
  countableOfLeftInverse
    (fun s => match s with | .view => (0, none) | .own dq => (1, some dq) | .stale => (2, none))
    (fun p => match p with | (1, some dq) => .own dq | (2, _) => .stale | _ => .view)
    (fun s => by cases s <;> rfl)

/-- A node's inode as the transaction keeps it: the entry and its bytes' sources. -/
structure WEntry where
  flags : w32
  pgid : w64
  key : List w8
  value : List w8
  ks : Src
  vs : Src
  deriving Inhabited

instance WEntry.countable : Pos.Countable WEntry :=
  countableOfLeftInverse (fun w => (w.flags, w.pgid, w.key, w.value, w.ks, w.vs))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩) (fun _ => rfl)

/-- A node: its struct, its inodes and their entries, its children, its key and its source. -/
structure NRec where
  nv : node
  ins : List Inode
  ws : List WEntry
  cs : List Loc
  key : List w8
  ksrc : Src
  /-- Whether the node owns its `inodes` slice's capacity (U9a fix): every node but a piece of
  `node.split` other than the last, whose capacity is the next pieces' inodes. -/
  capOwn : Bool := true

instance NRec.countable : Pos.Countable NRec :=
  countableOfLeftInverse (fun r => (r.nv, r.ins, r.ws, r.cs, r.key, r.ksrc, r.capOwn))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-- The status of a bucket's `page` field (round 4, N2): none (`page = nil`), view-backed (set by
`openBucket`, while `rootNode = nil` and no remap has happened since), or stale (never read
again). -/
inductive PageSt where
  | none
  | view
  | stale
  deriving Inhabited, DecidableEq

instance PageSt.countable : Pos.Countable PageSt :=
  countableOfLeftInverse
    (fun s => match s with | .none => (0 : Nat) | .view => 1 | .stale => 2)
    (fun n => match n with | 1 => .view | 2 => .stale | _ => .none)
    (fun s => by cases s <;> rfl)

/-- A bucket: its struct, its `InBucket` header, its node cache `nodes` (`nm`), its bucket
cache `buckets` (`bm`), the nodes it owns (`ns`), its inline page's bytes and source, and its
`page` field's status. -/
structure BRec where
  bv : Bucket
  ib : InBucket
  nm : GMap w64 Loc
  bm : GMap GoString Loc
  ns : GMap Loc NRec
  ipg : List w8
  isrc : Src
  pst : PageSt

instance BRec.countable : Pos.Countable BRec :=
  countableOfLeftInverse (fun B => (B.bv, B.ib, B.nm, B.bm, B.ns, B.ipg, B.isrc, B.pst))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2⟩) (fun _ => rfl)

/-- An object of the transaction's heap: a bucket, or a node (with its bucket's location). -/
inductive WObj where
  | bkt (B : BRec)
  | node (bl : Loc) (r : NRec)

instance WObj.countable : Pos.Countable WObj :=
  countableOfLeftInverse
    (fun o => match o with | .bkt B => Sum.inl B | .node bl r => Sum.inr (bl, r))
    (fun s => match s with | .inl B => .bkt B | .inr (bl, r) => .node bl r)
    (fun o => by cases o <;> rfl)

/-- A write transaction: its struct, its meta copy, its page cache `pages` (`pm`) and the
buffers' bytes, its reachable buckets (`bs`, each with its nodes), and the objects removed from
them (still owned, never read): the dead nodes (`dead`, each with its bucket's location: by
`rebalance`, `DeleteBucket`) and the dead buckets (`deadB`: `DeleteBucket`'s). Nodes and buckets
are kept apart (batch 14): a node's location and a bucket's may coincide as far as the heap can
tell (`structFieldRef` is abstract for non-plain structs). -/
structure WTx where
  t : Tx
  mv : Meta
  pm : GMap w64 Loc
  bufs : GMap w64 (List w8)
  bs : GMap Loc BRec
  dead : GMap Loc (Loc × NRec)
  deadB : GMap Loc BRec := ∅

instance WTx.countable : Pos.Countable WTx :=
  countableOfLeftInverse (fun T => (T.t, T.mv, T.pm, T.bufs, T.bs, T.dead, T.deadB))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-- Every node the transaction ever materialized (round 4, N2; batch 14: nodes only): its
buckets' nodes and the dead ones. -/
def WTx.objs (T : WTx) : GMap Loc WObj :=
  T.bs.toList.foldl (fun m bB =>
    bB.2.ns.toList.foldl (fun m' lr => m'.insert lr.1 (.node bB.1 lr.2)) m)
    (T.dead.fmap fun p => .node p.1 p.2)

/-- Every bucket the transaction ever opened (batch 14): its buckets and the dead ones. -/
def WTx.bobjs (T : WTx) : GMap Loc BRec := T.bs ∪ T.deadB

/-- **A node is in at most one bucket** (`wtxHeap` keeps it: every node is added at a fresh
location, `nodeAdded`). Under it a bucket's node record is its object (`objs_node`). (Batch 14:
nodes and buckets are separate maps, so a node need not be shown to be no bucket.) -/
def objsDisj (T : WTx) : Prop :=
  ∀ bl B, T.bs !! bl = some B → ∀ n, (B.ns !! n).isSome →
    ∀ bl' B', T.bs !! bl' = some B' → bl' ≠ bl → B'.ns !! n = none

/-- **The writer's logical state** (design §3.13): the records, the live nodes (those the code
reaches from `tx.root`: `b.buckets` recursively, then each `b.rootNode` through `children`) and
the live buckets (`liveB`, batch 14: one live set for both would let a node's death un-live a
bucket at the same location), every
handle given out (name and generation), the node-location registry (node ↦ its bucket's location
and the page id it was read from, N3), the base view (re-based by a remap), and the root bucket's
location (`txRoot tx`). -/
structure WX where
  t : WTx
  live : GMap Loc Unit
  liveB : GMap Loc Unit
  handles : GMap Loc (GoString × Nat)
  nloc : GMap Loc (Loc × Nat)
  v : View
  rl : Loc

instance WX.countable : Pos.Countable WX :=
  countableOfLeftInverse (fun X => (X.t, X.live, X.liveB, X.handles, X.nloc, X.v, X.rl))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-! ## Entries -/

/-- The key of entry `i` (empty past the end). -/
def wKey (ws : List WEntry) (i : Nat) : List w8 := ((ws[i]?).map WEntry.key).getD []

/-- The entries' keys increase strictly. -/
def wsSorted (ws : List WEntry) : Prop :=
  ∀ i j, i < j → j < ws.length → go.GoStringLt (wKey ws i) (wKey ws j)

/-- The entries of a node hold no stale bytes. -/
def wsLive (ws : List WEntry) : Prop := ∀ w ∈ ws, w.ks ≠ Src.stale ∧ w.vs ≠ Src.stale

/-- A nested bucket's flag (`BucketLeafFlag`). -/
def isBktFlag (f : w32) : Prop := f &&& W32 1 ≠ W32 0

instance (f : w32) : Decidable (isBktFlag f) := by unfold isBktFlag; infer_instance

/-- The `InBucket` of a nested bucket's value. -/
def ibOf (v : List w8) : InBucket := inBucketOf v

/-- The bytes `bs` at `p` are bytes of a page of the view (pages at `base + 4096 · id`). -/
def inViewLoc (v : View) (p : Loc) (bs : List w8) : Prop :=
  ∃ (id : Nat) (pg : List w8) (off : Nat), v.pages !! id = some pg ∧
    off + bs.length ≤ pg.length ∧ bytesAt pg off bs.length = bs ∧
    p = v.base +ₗ ((id * 4096 + off : Nat) : Int)

/-- The slice `s` is the bytes `bs` of a page of the view. -/
def inViewAt (v : View) (s : GoSlice) (bs : List w8) : Prop :=
  inViewLoc v s.ptr bs ∧ bs.length < 2 ^ 32 ∧ s.len = W64 (bs.length : Int) ∧
    s.cap = W64 (bs.length : Int)

/-! ## Positions -/

/-- The node a bucket keeps at position `pid` (its root node for an inline bucket). -/
def resolve (B : BRec) (pid : w64) : Option Loc :=
  if B.ib.root' = W64 0 then (if B.bv.rootNode' = null then none else some B.bv.rootNode')
  else B.nm !! pid

/-- The page at position `pid` of the bucket: where it is, its bytes. -/
def wpageAt (v : View) (B : BRec) (pid : w64) : Option (Loc × List w8) :=
  if B.ib.root' = W64 0 then (if pid = W64 0 then some (B.bv.page', B.ipg) else none)
  else (v.pages !! pid.toNat).map fun pg => (v.base +ₗ ((pid.toNat * 4096 : Nat) : Int), pg)

/-- Entry `i` of the branch node `l` is a page position: its child `c` is not materialized. -/
def pagePosAt (B : BRec) (l : Loc) (i : Nat) (c : w64) : Prop :=
  ∃ r w, B.ns !! l = some r ∧ r.nv.isLeaf' = false ∧ r.ws[i]? = some w ∧ w.pgid = c ∧
    B.nm !! c = none

/-- Distinct page positions have disjoint subtrees. -/
def posDisjoint (v : View) (B : BRec) : Prop :=
  ∀ l1 i1 c1 l2 i2 c2, pagePosAt B l1 i1 c1 → pagePosAt B l2 i2 c2 → (l1, i1) ≠ (l2, i2) →
    ∀ d, treeHas v.pages c1.toNat d → ¬ treeHas v.pages c2.toNat d

/-- No page of a page position's subtree is materialized. -/
def posNodeFree (v : View) (B : BRec) : Prop :=
  ∀ l i c, pagePosAt B l i c → ∀ d, treeHas v.pages c.toNat d → B.nm !! W64 (d : Int) = none

/-- The page positions of `B`: its root page if it has no materialized root, else the children
its branch nodes have not materialized. -/
def posRoot (B : BRec) (c : Nat) : Prop :=
  (B.bv.rootNode' = null ∧ B.ib.root' ≠ W64 0 ∧ c = B.ib.root'.toNat) ∨
  ∃ l i, pagePosAt B l i (W64 (c : Int)) ∧ c < 2 ^ 64

/-! ## The clean invariant (old `txClean`) -/

/-- An inline page's entries within `bboltEntryMax` (batch 22, U7b: `entriesBounded` of the
nodes it materializes; `Bucket.Bucket_w` proves it on open from `rootShape` for a view value,
`Put`'s premise for a written one). -/
def inlineBnd (ipg : List w8) : Prop :=
  ∀ j < pageCount ipg, leafKsize ipg j + leafVsize ipg j ≤ bboltEntryMax

/-- A nested bucket's value, well-formed and good; (batch 37, U6e) a tree bucket's leaves hold
plain entries only (nesting depth 2, as `rootShape` for the view: `Bucket.node` gives it from the
view page, `CreateBucket` writes an inline value). -/
def bvalOK (pages : Pages) (hwm : Nat) (v : List w8) : Prop :=
  bucketWF pages hwm v ∧
    (inBucketRoot v = 0 → inlineGood (inlinePage v) ∧ inlineBnd (inlinePage v)) ∧
    (inBucketRoot v ≠ 0 → ∀ pg, bktLeafPg pages v pg → ∀ j < pageCount pg,
      leafFlags pg j % 2 = 0 ∧ 0 < leafKsize pg j ∧ leafKsize pg j + leafVsize pg j ≤ bboltEntryMax)

/-- The node `l` (record `r`) of the bucket `bl` (record `B`) is well-formed. -/
def nodeClean (v : View) (hwm : Nat) (bl : Loc) (B : BRec) (l : Loc) (r : NRec) : Prop :=
  r.nv.bucket' = bl ∧ r.capOwn = true ∧ r.ins.length = r.ws.length ∧ wsSorted r.ws ∧
  (∀ w ∈ r.ws, 0 < w.key.length) ∧ wsLive r.ws ∧ r.nv.spilled' = false ∧
  B.nm !! r.nv.pgid' = some l ∧
  (B.ib.root' = W64 0 → r.nv.pgid' = W64 0) ∧
  (B.ib.root' ≠ W64 0 → treeWF v.pages hwm r.nv.pgid'.toNat) ∧
  (r.nv.key' = slice.nil ∨ (0 < r.key.length ∧ r.ksrc ≠ Src.stale)) ∧
  (r.nv.isLeaf' = true → ∀ w ∈ r.ws, isBktFlag w.flags →
    ((B.bm !! w.key).isSome = false → bvalOK v.pages hwm w.value) ∧
    (w.vs = Src.view ∨ w.vs = Src.own DFrac.discard)) ∧
  (r.nv.isLeaf' = false → 0 < r.ws.length ∧ (r.ws.map WEntry.pgid).Nodup ∧ ∀ w ∈ r.ws,
    w.pgid.toNat < hwm ∧
    (∀ l', B.nm !! w.pgid = some l' → ∃ r', B.ns !! l' = some r' ∧ r'.nv.parent' = l) ∧
    (B.nm !! w.pgid = none → treeWF v.pages hwm w.pgid.toNat)) ∧
  (r.nv.parent' = null → B.bv.rootNode' = l) ∧
  (r.nv.parent' ≠ null → ∃ rp, B.ns !! r.nv.parent' = some rp ∧ rp.nv.isLeaf' = false ∧
    l ∈ rp.cs ∧ ∃ w ∈ rp.ws, w.pgid = r.nv.pgid') ∧
  r.cs.Nodup ∧ (∀ c ∈ r.cs, ∃ rc, B.ns !! c = some rc ∧ rc.nv.parent' = l)

/-- The bucket `bl` (record `B`) is well-formed. -/
def bktClean (v : View) (hwm : Nat) (bl : Loc) (B : BRec) : Prop :=
  (B.ib.root' = W64 0 → B.bv.rootNode' = null →
    B.bv.page' ≠ null ∧
      ((B.isrc = Src.view ∧ B.pst = PageSt.view) ∨ (B.isrc = Src.own DFrac.discard ∧ B.pst = PageSt.none)) ∧
      inlineGood B.ipg ∧ inlineBnd B.ipg) ∧
  (B.ib.root' ≠ W64 0 → B.ib.root'.toNat < hwm ∧
    (B.bv.rootNode' = null → treeWF v.pages hwm B.ib.root'.toNat)) ∧
  (B.bv.rootNode' = null → B.ns = ∅ ∧ B.nm = ∅) ∧
  (B.bv.rootNode' ≠ null → B.nm !! B.ib.root' = some B.bv.rootNode') ∧
  (∀ c l, B.nm !! c = some l → l ≠ null ∧ ∃ r, B.ns !! l = some r ∧ r.nv.pgid' = c) ∧
  (B.ib.root' ≠ W64 0 → B.bv.page' = null) ∧
  (B.ib.root' = W64 0 → ∀ l r, B.ns !! l = some r → r.nv.isLeaf' = true) ∧
  (∀ l r, B.ns !! l = some r → nodeClean v hwm bl B l r) ∧
  posDisjoint v B ∧ posNodeFree v B ∧
  -- batch 37 (U6e): the cached child buckets are non-nil (a nil entry is a miss for
  -- `Bucket.Bucket`, which would open over it)
  (∀ n c, B.bm !! n = some c → c ≠ null)

/-- **The root shape on the writer's leaf nodes** (batch 30, U9d): the root bucket's leaves hold
only bucket entries, every other bucket's leaves none (nesting depth 2, as `treeOK`'s
`rootShape` for the view: `Put` writes plain entries, `CreateBucket` buckets only at the root). -/
def leafShape (X : WX) : Prop :=
  ∀ bl B, X.t.bs !! bl = some B → ∀ l r, B.ns !! l = some r → r.nv.isLeaf' = true →
    ∀ w ∈ r.ws, (isBktFlag w.flags ↔ bl = X.rl)

/-- **The root shape on the view pages under the writer's page positions** (batch 35, U7e's
finding): every leaf page of the view tree under a page position of a bucket `bl` (`posRoot`: its
root page without a root node, or an unmaterialized child of one of its branch nodes; `ownHas`:
the pages below it) holds bucket entries iff `bl` is the root bucket. What a materialization's new
leaf node inherits for `leafShape`. Established at `beginRWTx` from `rootShape` (U5d), kept by
`Bucket.Bucket_w`'s open (U6e, from the parent's value), materialization (U7), rebalance (U8d),
dereferencing (`Spill/DerefWOK.posShape_step`) and spill (U9). -/
def posShape (X : WX) : Prop :=
  ∀ bl B, X.t.bs !! bl = some B → ∀ c p pg, posRoot B c → ownHas X.v.pages c p →
    X.v.pages !! p = some pg → pageFlags pg = leafPageFlag →
    ∀ i < pageCount pg, (leafFlags pg i % 2 = bucketLeafFlag ↔ bl = X.rl) ∧
      -- batch 38 (S1): the view leaf entries are bounded (`rootShape`'s clauses; item 3/batch
      -- 43.4: the root bucket's too, unconditionally), and the root bucket's names at most
      -- `MaxKeySize` (`rootShape`'s name bound)
      (0 < leafKsize pg i ∧ leafKsize pg i + leafVsize pg i ≤ bboltEntryMax) ∧
      (bl = X.rl → leafKsize pg i ≤ maxKeySize) ∧
      -- maintainer 13 (item 2): a root bucket's entry that is a bucket has `rootShape`'s nested
      -- clause (its own leaves plain, keys non-empty, entries bounded)
      (bl = X.rl → leafFlags pg i % 2 = bucketLeafFlag → ∀ bpg, bktLeafPg X.v.pages (leafValue pg i) bpg →
        ∀ j < pageCount bpg, leafFlags bpg j % 2 = 0 ∧ 0 < leafKsize bpg j ∧
          leafKsize bpg j + leafVsize bpg j ≤ bboltEntryMax)

/-- **The root bucket is not inline** (batch 37, U7f): its root is a page (the view's meta root at
`beginRWTx`; no operation makes it inline). -/
def rootNotInline (X : WX) : Prop := ∀ B, X.t.bs !! X.rl = some B → B.ib.root' ≠ W64 0

/-- The clean invariant of the transaction (old `txClean`), its root bucket at `X.rl`; batch 30
(U9d), in its second clause beside `pm = ∅` (so that the six-clause patterns stand): no dirty-page
buffers yet (`spill` allocates them; `WX.bufPages` reads all of `bufs`), the leaves' root shape
(`leafShape`), (batch 35) the view pages' under the page positions (`posShape`), and (batch 37)
the root bucket not inline (`rootNotInline`). -/
def txClean (X : WX) : Prop :=
  X.t.t.writable' = true ∧
    (X.t.pm = ∅ ∧ X.t.bufs = ∅ ∧ leafShape X ∧ posShape X ∧ rootNotInline X) ∧
  2 ≤ X.t.mv.pgid'.toNat ∧ X.v.txid + 1 = X.t.mv.txid'.toNat ∧ (X.t.bs !! X.rl).isSome ∧
  ∀ bl B, X.t.bs !! bl = some B → bktClean X.v X.t.mv.pgid'.toNat bl B ∧
    ∀ name c, B.bm !! name = some c → (X.t.bs !! c).isSome

/-! ## Keys (old `bktKeys`) -/

/-- The bounds of entry `i`'s child, under a node with the entries `ws` and the bounds `b`. -/
def wEntryBnd (b : Option (List w8) × Option (List w8)) (ws : List WEntry) (i : Nat) :
    Option (List w8) × Option (List w8) :=
  entryBnd b (ws.map WEntry.key) i

/-- The nested bucket named `k` is open in `B`. -/
def opened (B : BRec) (k : List w8) : Prop := (B.bm !! k).isSome

/-- The node `l` (record `r`) of `B` and its keys, the nodes' bounds `bnd`. -/
def nodeKeys (v : View) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (l : Loc) (r : NRec) : Prop :=
  (∀ w ∈ r.ws, keyIn (bnd l).1 (bnd l).2 w.key) ∧
  (r.nv.parent' = null → bnd l = (none, none)) ∧
  (r.nv.parent' ≠ null → r.nv.key' ≠ slice.nil ∧ ∃ rp i w, B.ns !! r.nv.parent' = some rp ∧
    rp.ws[i]? = some w ∧ w.pgid = r.nv.pgid' ∧ w.key = r.key ∧
    bnd l = wEntryBnd (bnd r.nv.parent') rp.ws i) ∧
  (r.nv.isLeaf' = false → 2 ≤ r.ws.length ∧ ∃ kind : Bool, ∀ i w, r.ws[i]? = some w →
    (∀ l', B.nm !! w.pgid = some l' → ∃ r', B.ns !! l' = some r' ∧ r'.nv.isLeaf' = kind) ∧
    (B.nm !! w.pgid = none → ∃ pg, v.pages !! w.pgid.toNat = some pg ∧ 0 < pageCount pg ∧
      decide (pageFlags pg = leafPageFlag) = kind ∧ pageKey pg 0 = w.key ∧
      treeKeys v.pages w.pgid.toNat (wEntryBnd (bnd l) r.ws i).1
        (wEntryBnd (bnd l) r.ws i).2)) ∧
  (r.nv.isLeaf' = true → r.nv.unbalanced' = false → r.nv.parent' ≠ null → 0 < r.ws.length) ∧
  (r.nv.isLeaf' = true → ∀ w ∈ r.ws, isBktFlag w.flags → inBucketRoot w.value ≠ 0 →
    ¬ opened B w.key → treeKeys v.pages (inBucketRoot w.value) none none)

/-- The keys of the bucket `B`, its nodes' bounds `bnd`. -/
def bktKeysB (v : View) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8)) : Prop :=
  (B.bv.rootNode' = null → B.ib.root' ≠ W64 0 →
    treeKeys v.pages B.ib.root'.toNat none none) ∧
  (∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null) ∧
  ∀ l r, B.ns !! l = some r → nodeKeys v B bnd l r

/-- The keys of the bucket `B`. -/
def bktKeys (v : View) (B : BRec) : Prop := ∃ bnd, bktKeysB v B bnd

/-! ## Nested buckets (old `bktNested`) -/

/-- `B`'s entry named `k` is a nested bucket with the value `v`: in one of its materialized
leaves, or on a page of one of its positions. -/
def entryIn (vw : View) (B : BRec) (k v : List w8) : Prop :=
  (∃ l r w, B.ns !! l = some r ∧ r.nv.isLeaf' = true ∧ w ∈ r.ws ∧ w.key = k ∧
    isBktFlag w.flags ∧ w.value = v) ∨
  (∃ c p pg i, posRoot B c ∧ ownHas vw.pages c p ∧ vw.pages !! p = some pg ∧
    pageFlags pg = leafPageFlag ∧ i < pageCount pg ∧ leafKey pg i = k ∧
    leafFlags pg i % 2 = bucketLeafFlag ∧ leafValue pg i = v)

/-- The buckets `B` opened are its entries'. -/
def bktNested (vw : View) (T : WTx) (B : BRec) : Prop :=
  ∀ k c, B.bm !! k = some c → ∃ C v, T.bs !! c = some C ∧ entryIn vw B k v ∧ 16 ≤ v.length ∧
    (inBucketRoot v = 0 → inlineGood (inlinePage v)) ∧
    C.ib.root' = (ibOf v).root' ∧ (C.bv.rootNode' = null → C.ib = ibOf v)

/-! ## Nodes' pages (old `txPg`) -/

/-- Before `Commit`, a branch node's entries are its page's (its children's page ids and, U6y's
F3, its keys: only `spill` and `rebalance` change a branch node) and a leaf's have no child page. -/
def nodePg (v : View) (root : w64) (r : NRec) : Prop :=
  (r.nv.isLeaf' = true → (∀ w ∈ r.ws, w.pgid = W64 0) ∧
    (root ≠ W64 0 → ∃ pg, v.pages !! r.nv.pgid'.toNat = some pg ∧
      pageFlags pg = leafPageFlag)) ∧
  (r.nv.isLeaf' = false → (r.key = wKey r.ws 0 ∧ ∀ pg, v.pages !! r.nv.pgid'.toNat = some pg →
      r.ws.map WEntry.key = (List.range (pageCount pg)).map (pageKey pg)) ∧
    ∃ pg, v.pages !! r.nv.pgid'.toNat = some pg ∧
    pageFlags pg = branchPageFlag ∧ r.ws.length = pageCount pg ∧
    ∀ i w, r.ws[i]? = some w → w.pgid = W64 (branchPgid pg i : Int))

/-- Every bucket's nodes and their pages. -/
def txPg (v : View) (bs : GMap Loc BRec) : Prop :=
  ∀ bl B, bs !! bl = some B → ∀ l r, B.ns !! l = some r → nodePg v B.ib.root' r

/-! ## `wOK` -/

/-- Every entry of the transaction's nodes within `bboltEntryMax` (D4, for `SpillFit`), and keys
non-empty; batch 37 (U9i): every entry, leaf or branch, a bucket entry too (the root bucket's: name
and header or inline value, `rootShape`; a branch key is a leaf key, by exact branch keys);
(item 3, batch 43.4) the root bucket's keys (bucket names, and branch keys: names too) at most
`MaxKeySize` (`rootShape`'s name bound; `CreateBucket`'s premise), the third conjunct. -/
def entriesBounded (X : WX) : Prop :=
  ∀ bl B, X.t.bs !! bl = some B → ∀ l r, B.ns !! l = some r → ∀ w ∈ r.ws,
    0 < w.key.length ∧ w.key.length + w.value.length ≤ bboltEntryMax ∧
      (bl = X.rl → w.key.length ≤ maxKeySize)

/-- The handles: each is a bucket of the transaction (current handles are in `buckets`'
caches, stale ones are dead objects). -/
def handlesOK (X : WX) : Prop :=
  ∀ b nm, X.handles !! b = some nm → (X.t.bobjs !! b).isSome

/-- Every node of every bucket is live (U8b's, moved here, batch 20: `liveOK`'s fourth clause). -/
def nsLive (X : WX) : Prop :=
  ∀ bl B l r, X.t.bs !! bl = some B → B.ns !! l = some r → l ∈ X.live

/-- The live nodes are node objects; the root bucket is live, and every bucket of `bs` (`liveB`,
batch 14), and every node of one (batch 12); no dead node is live (batch 12: what `dereference`
needs, `wOKR_derefPre`). -/
def liveOK (X : WX) : Prop :=
  X.rl ∈ X.liveB ∧ (∀ l, l ∈ X.live → (X.t.objs !! l).isSome) ∧
  (∀ bl B, X.t.bs !! bl = some B → bl ∈ X.liveB) ∧
  nsLive X ∧ ∀ l, (X.t.dead !! l).isSome → l ∉ X.live

/-- The node-location registry (round 4, N3): each live registered node is a node of its
bucket, read from the page id it records (U8 fix: a node `rebalance` or `DeleteBucket` removed is
dead, its entry kept). That every registered node is an object is `wtxHeap`'s `heapOK`. -/
def nlocOK (X : WX) : Prop :=
  ∀ n b p, X.nloc !! n = some (b, p) → n ∈ X.live → ∃ B r, X.t.bs !! b = some B ∧
    B.ns !! n = some r ∧ r.nv.pgid'.toNat = p

/-- **The writer's well-formedness before `Commit`** (design §3.2, §3.13): the old clean
invariant, keys, nested buckets and nodes' pages, entries bounded, and the handles, live set and
node registry consistent. -/
def wOK (X : WX) : Prop :=
  txClean X ∧ (∀ bl B, X.t.bs !! bl = some B → bktKeys X.v B ∧ bktNested X.v X.t B) ∧
  txPg X.v X.t.bs ∧ entriesBounded X ∧ handlesOK X ∧ liveOK X ∧ nlocOK X ∧ viewWF X.v

/-- A leaf node's entries have no child page (`nodePg`'s leaf part: what `spill` needs). -/
def nodePgLeaf (r : NRec) : Prop := r.nv.isLeaf' = true → ∀ w ∈ r.ws, w.pgid = W64 0

/-- Every bucket's leaf nodes have no child pages. -/
def txPgLeaf (bs : GMap Loc BRec) : Prop :=
  ∀ bl B, bs !! bl = some B → ∀ l r, B.ns !! l = some r → nodePgLeaf r

/-- **The writer's well-formedness after `rebalance`** (`spill`'s pre, U8 fix): `wOK` but for
`txPg`'s branch part (a merged branch node's entries are no longer its page's) and its leaves'
pages: only `txPgLeaf`. -/
def wOKR (X : WX) : Prop :=
  txClean X ∧ (∀ bl B, X.t.bs !! bl = some B → bktKeys X.v B ∧ bktNested X.v X.t B) ∧
  txPgLeaf X.t.bs ∧ entriesBounded X ∧ handlesOK X ∧ liveOK X ∧ nlocOK X ∧ viewWF X.v

theorem wOK_nsLive (X : WX) (h : wOK X) : nsLive X := h.2.2.2.2.2.1.2.2.2.1

theorem wOKR_nsLive (X : WX) (h : wOKR X) : nsLive X := h.2.2.2.2.2.1.2.2.2.1

theorem txPg_txPgLeaf (v : View) (bs : GMap Loc BRec) (h : txPg v bs) : txPgLeaf bs :=
  fun bl B hb l r hr hl => ((h bl B hb l r hr).1 hl).1

theorem wOK_wOKR (X : WX) (h : wOK X) : wOKR X :=
  ⟨h.1, h.2.1, txPg_txPgLeaf _ _ h.2.2.1, h.2.2.2⟩

end wtx

end bbolt
end EtcdGrove
end Perennial
