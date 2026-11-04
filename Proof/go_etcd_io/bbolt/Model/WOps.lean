/-
The writer's operations as relations on its records (U0b of `notes/bbolt-proof-plan.md`; design
§4.2, "the frozen shared contracts"): what the internal specs of the writer's functions
(`Spec/go_etcd_io/bbolt/{node,Bucket,Cursor,Tx}__*.lean`) say about the records `WX` before and
after, so that the unit proving a function and the units calling it share one statement.

- **Entries**: a node's entries by data (`wDat`), the search index (`wsIdx`), `node.put`'s and
  `node.del`'s effect (`wsPutAt`, `wsDelAt`), a page's entries with their sources (`pageWsAs`),
  a node's size (`insSize`).
- **Materialization** (`Bucket.node`): `nodeAdded`, its closure `matGrow`.
- **Logical stacks** (the writer's search, for any bucket of `X`, the root bucket included):
  `lPath`, `lRoutes`, `bktLocalOK`.
- **Frees** (`Bucket.free`, `node.free`): the logical tree's positions and extents.
- **Rebalance and spill** (`rebalOK`: rebalance's post, spill's pre; `spillOK`: spill's post);
  allocation (`allocRes`) and the freelist steps of a failed spill (`FLStep`).

The lemma statements at the end are proved by the units named in their docstrings.
-/
module

public import Proof.go_etcd_io.bbolt.Model.LTree
public import Proof.go_etcd_io.bbolt.Model.PageAt
public import Proof.go_etcd_io.bbolt.Model.Store

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wops
variable [GooseExts]

/-! ## Entries -/

/-- An entry's data: flags, page id, key, value (its sources left out). -/
def wDat (w : WEntry) : w32 × w64 × List w8 × List w8 := (w.flags, w.pgid, w.key, w.value)

/-- **The search index of `k`** in `ws` (`sort.Search` for the first key not below `k`; on
sorted entries, the number of keys below `k`). -/
def wsIdx (ws : List WEntry) (k : List w8) : Nat :=
  (ws.takeWhile fun w => decide (go.GoStringLt w.key k)).length

/-- `k` is at its search index in `ws` (`node.put`'s and `node.del`'s `exact`). -/
def wsFound (ws : List WEntry) (k : List w8) : Prop :=
  (ws[wsIdx ws k]?).map WEntry.key = some k

instance (ws : List WEntry) (k : List w8) : Decidable (wsFound ws k) := by
  unfold wsFound; infer_instance

/-- **`n.put(oldKey, …)`'s entries**: at the search index of `oldKey`, the entry `e` replaces
the one of key `oldKey`, or is inserted there. -/
def wsPutAt (ws : List WEntry) (ok : List w8) (e : WEntry) : List WEntry :=
  if wsFound ws ok then ws.take (wsIdx ws ok) ++ [e] ++ ws.drop (wsIdx ws ok + 1)
  else ws.take (wsIdx ws ok) ++ [e] ++ ws.drop (wsIdx ws ok)

/-- **`n.del(key)`'s entries**: the entry of key `k` at its search index removed, if any. -/
def wsDelAt (ws : List WEntry) (k : List w8) : List WEntry :=
  if wsFound ws k then ws.take (wsIdx ws k) ++ ws.drop (wsIdx ws k + 1) else ws

/-- The entries of page `pg` read with the source `src` (`node.read`: a page of the view is
`.view`, an inline page in a node's value is that value's source): keys and leaf values from
`src`, a branch element's (empty) value persistent. -/
def pageWsAs (pg : List w8) (src : Src) : List WEntry :=
  (pageWs pg).map fun w =>
    { w with ks := src, vs := if pageFlags pg = leafPageFlag then src else Src.own DFrac.discard }

/-- **A node's size** (`node.size`): the header, and per inode an element and its key and value
(the slices' lengths). -/
def insSize (ins : List Inode) : Nat :=
  16 + (ins.map fun it => 16 + it.key'.len.toNat + it.value'.len.toNat).sum

/-! ## Updates of records (what the specs' posts name; a multi-field update does not parse
inside `iprop`) -/

/-- A node's record with the inodes slice `s`, the inodes `ins` and the entries `ws`. -/
def NRec.withEnts (r : NRec) (s : GoSlice) (ins : List Inode) (ws : List WEntry) : NRec :=
  { r with nv := { r.nv with inodes' := s }, ins := ins, ws := ws }

/-- The same, and the `unbalanced` flag `u` (`node.del`). -/
def NRec.withEntsU (r : NRec) (s : GoSlice) (ins : List Inode) (ws : List WEntry) (u : Bool) :
    NRec :=
  { r with nv := { r.nv with inodes' := s, unbalanced' := u }, ins := ins, ws := ws }

/-- A node's struct after `n.read(p)` of the page `pg`: its page id and kind the header's, its
inodes the slice `s`, its key `k`. -/
def nodeAfterRead (nv : node) (pg : List w8) (s k : GoSlice) : node :=
  { nv with pgid' := (pageHdr pg).id', isLeaf' := decide (pageFlags pg = leafPageFlag),
            inodes' := s, key' := k }

/-- A page header after `node.write`: a leaf's or a branch's flags, `n` elements. -/
def hdrWritten (hdr : Page) (leaf : Bool) (n : Nat) : Page :=
  { hdr with flags' := W16 ((if leaf then leafPageFlag else branchPageFlag : Nat) : Int),
             count' := W16 (n : Int) }

/-! ## Updates of a bucket's records -/

/-- `X` with bucket `bl`'s record `B'`. -/
def WX.setBkt (X : WX) (bl : Loc) (B' : BRec) : WX :=
  { X with t := { X.t with bs := X.t.bs.insert bl B' } }

/-- `X` with node `l` of bucket `bl` holding the record `r` (unchanged if no such bucket). -/
def WX.setNode (X : WX) (bl l : Loc) (r : NRec) : WX :=
  match X.t.bs !! bl with
  | none => X
  | some B => X.setBkt bl { B with ns := B.ns.insert l r }

/-- The record of node `l` of bucket `bl`. -/
def WX.node (X : WX) (bl l : Loc) : Option NRec := (X.t.bs !! bl).bind fun B => B.ns !! l

/-! ## Materialization (`Bucket.node`) -/

/-- The source of the bytes of the page at position `pid` of `B` (`wpageAt`): the view, or for
an inline bucket its `page` field's (`isrc`). -/
def posSrc (B : BRec) : Src := if B.ib.root' = W64 0 then B.isrc else Src.view

/-- **`X'` is `X` with the node `l` of bucket `bl` materialized from position `pgid`**
(`b.node(pgid, parent)`, uncached case): read from the page `wpageAt X.v B pgid` (its entries
`pageWsAs pg (posSrc B)`, by data; its page id the header's; no children; neither unbalanced nor
spilled), cached at `pgid`, registered at `(bl, pgid)`, live, and made the bucket's root node
(`parent = null`) or appended to the branch node `parent`'s children; nothing else changes. -/
def nodeAdded (X X' : WX) (bl l : Loc) (pgid : w64) (parent : Loc) : Prop :=
  ∃ (B : BRec) (pa : Loc) (pg : List w8) (r : NRec) (ns' : GMap Loc NRec) (bv' : Bucket),
    X.t.bs !! bl = some B ∧ wpageAt X.v B pgid = some (pa, pg) ∧ B.nm !! pgid = none ∧
    l ≠ null ∧ (X.t.objs !! l).isNone ∧
    r.nv.bucket' = bl ∧ r.nv.parent' = parent ∧ r.nv.pgid' = (pageHdr pg).id' ∧
    r.nv.isLeaf' = decide (pageFlags pg = leafPageFlag) ∧ r.nv.unbalanced' = false ∧
    r.nv.spilled' = false ∧ r.cs = [] ∧ r.capOwn = true ∧
    r.ws.map wDat = (pageWsAs pg (posSrc B)).map wDat ∧ wsLive r.ws ∧
    r.key = wKey r.ws 0 ∧ r.ksrc ≠ Src.stale ∧
    ((parent = null ∧ bv' = { B.bv with rootNode' := l } ∧ ns' = B.ns.insert l r) ∨
     (parent ≠ null ∧ bv' = B.bv ∧ ∃ rp rp', B.ns !! parent = some rp ∧
        rp.nv.isLeaf' = false ∧ rp'.cs = rp.cs ++ [l] ∧ rp'.ws = rp.ws ∧ rp'.ins = rp.ins ∧
        rp'.key = rp.key ∧ rp'.ksrc = rp.ksrc ∧
        rp'.nv = { rp.nv with children' := rp'.nv.children' } ∧
        ns' = (B.ns.insert parent rp').insert l r)) ∧
    X' = { X with t := { X.t with bs := X.t.bs.insert bl { B with nm := B.nm.insert pgid l,
                                                                  ns := ns', bv := bv' } },
                  live := X.live.insert l (), nloc := X.nloc.insert l (bl, pgid.toNat) }

/-- **A position `nodeAdded` materializes** (U7 fix): the root page of a bucket with no root
node, or a child page its branch node `parent` has not materialized. -/
def matPos (X : WX) (bl : Loc) (pgid : w64) (parent : Loc) : Prop :=
  ∃ B, X.t.bs !! bl = some B ∧
    ((parent = null ∧ B.bv.rootNode' = null ∧ pgid = B.ib.root') ∨ ∃ i, pagePosAt B parent i pgid)

/-- **The new node is fresh in its bucket** (U7 fix; what `nodeAdded` needs to keep the logical
tree): no cached node of the bucket, and an inline bucket had no root node. `wOK` gives it
(`wOK_matFresh`). -/
def matFresh (X : WX) (bl l : Loc) : Prop :=
  ∀ B, X.t.bs !! bl = some B → (∀ c, B.nm !! c ≠ some l) ∧
    (B.ib.root' = W64 0 → B.bv.rootNode' = null)

/-- **Materializations in bucket `bl`** (`Cursor.node`, `childAt`): zero or more
`nodeAdded` steps. -/
inductive matGrow : WX → WX → Loc → Prop
  | refl (X : WX) (bl : Loc) : matGrow X X bl
  | step (X Y Z : WX) (bl l : Loc) (pgid : w64) (parent : Loc) :
      nodeAdded X Y bl l pgid parent → matPos X bl pgid parent → matGrow Y Z bl →
      matGrow X Z bl

/-- The page at position `pgid` of `B` can be materialized (`Bucket.node`'s uncached case): its
page is in the view (or the inline page, not stale), readable by `ReadInodeFromPage`, a leaf or
a branch, of header id `pgid` (`0` inline), not in the transaction's page cache, and its
location's page offsets within the address space. -/
def matReady (X : WX) (B : BRec) (pgid : w64) : Prop :=
  ∃ pa pg, wpageAt X.v B pgid = some (pa, pg) ∧ pageReadable pg ∧
    (pageFlags pg = leafPageFlag ∨ pageFlags pg = branchPageFlag) ∧
    pageElemsIn pg ∧ (pageHdr pg).id' = pgid ∧ X.t.pm !! pgid = none ∧
    (B.ib.root' = W64 0 → B.pst = PageSt.view ∨ ∃ dq, B.isrc = Src.own dq) ∧
    0 < pa.addr ∧ pa.addr + pg.length ≤ maxAddr ∧ ∀ i < pageCount pg, pa.addr + elemEnd pg i ≤ maxAddr

/-! ## Logical stacks (the writer's search) -/

/-- The stack element `e` refers to position `pid` of bucket `bl`: its materialized node
(`resolve`), or else its page (`wpageAt`), as `pageNode` returns them. -/
def refAt (X : WX) (bl : Loc) (pid : w64) (e : elemRef) : Prop :=
  ∃ B, X.t.bs !! bl = some B ∧
    match resolve B pid with
    | some l => e.node' = l
    | none => e.node' = null ∧ ∃ pg, wpageAt X.v B pid = some (e.page', pg)

/-- **A logical stack**: `els` (at positions `pids`) is a root-to-leaf path of bucket `bl`'s
logical tree in `X`; each branch element's index selects the next position. -/
def lPath (X : WX) (bl : Loc) (els : List elemRef) (pids : List w64) : Prop :=
  els ≠ [] ∧ pids.length = els.length ∧ pids.head? = some (X.rootPid bl) ∧
  ∀ (j : Nat) (e : elemRef) (pid : w64), els[j]? = some e → pids[j]? = some pid → refAt X bl pid e ∧
    ∃ lf ws, ltree X bl pid = some (lf, ws) ∧
      (j + 1 < els.length → lf = false ∧ ∃ w, ws[e.index'.toNat]? = some w ∧
        pids[j + 1]? = some w.pgid) ∧
      (j + 1 = els.length → lf = true)

/-- **The stack routes `k`** (`search`): each branch index is the last entry whose key is at
most `k` (or the first), and the leaf index is `k`'s search index. -/
def lRoutes (X : WX) (bl : Loc) (els : List elemRef) (pids : List w64) (k : List w8) : Prop :=
  ∀ (j : Nat) (e : elemRef) (pid : w64) (lf : Bool) (ws : List WEntry), els[j]? = some e → pids[j]? = some pid → ltree X bl pid = some (lf, ws) →
    (lf = false → e.index'.toNat < ws.length ∧
      (e.index'.toNat = 0 ∨ ∃ w, ws[e.index'.toNat]? = some w ∧ ¬ go.GoStringLt k w.key) ∧
      ∀ w, ws[e.index'.toNat + 1]? = some w → go.GoStringLt k w.key) ∧
    (lf = true → e.index'.toNat = wsIdx ws k)

/-- The leaf entries at the end of a logical stack. -/
def lLeaf (X : WX) (bl : Loc) (pids : List w64) : List WEntry :=
  match pids.getLast? with
  | some pid => match ltree X bl pid with
    | some (_, ws) => ws
    | none => []
  | none => []

/-- **Bucket `bl` can be searched** (and its nodes materialized): its record's clean, key and
leaf page facts (`wOK`'s, for this bucket alone, at the transaction's current high-water mark;
`txPgLeaf` only, which also holds after `rebalance`), and its location live. Holds for every bucket under `wOK`, and for a bucket `Bucket.spill` searches
after its children's spill. -/
def bktLocalOK (X : WX) (bl : Loc) : Prop :=
  bl ∈ X.live ∧ ∃ B, X.t.bs !! bl = some B ∧ bktClean X.v X.t.mv.pgid'.toNat bl B ∧
    bktKeys X.v B ∧ txPgLeaf (GMap.singleton bl B) ∧
    ∀ l r, B.ns !! l = some r → l ∈ X.live

/-- A searchable bucket's cached nodes are not nil (`bktClean`'s `B.nm` clause;
`Bucket.pageNode_w`'s premise). -/
theorem bktLocalOK_nm_nonnull (X : WX) (bl : Loc) (B : BRec) (h : bktLocalOK X bl)
    (hB : X.t.bs !! bl = some B) : ∀ c l, B.nm !! c = some l → l ≠ null := by
  obtain ⟨-, B', hB', hc, -⟩ := h
  rw [hB] at hB'; cases hB'
  exact fun c l hl => (hc.2.2.2.2.1 c l hl).1

/-- All the entries of bucket `bl` in order (its logical leaves'). -/
def WX.allEnts (X : WX) (bl : Loc) : List WEntry := (X.leaves bl).flatten

/-! ## Opening a nested bucket (`Bucket.Bucket`, writer) -/

/-- **`X'` is `X` with the nested bucket `name` of bucket `bl` opened at `c`** (`b.Bucket(name)`,
uncached case, `openBucket`): a new bucket record at the fresh `c`, from the value of `bl`'s
bucket entry `name` (its header copied, or the value cloned when unaligned: the page's bytes then
persistent heap bytes), with the transaction's `tx`, empty caches and no node, fill `0.5` (in
`fills`), cached in `bl`'s `buckets`, live, and the handle `(name, g)` registered. -/
def bktOpened (X X' : WX) (bl c : Loc) (name : List w8) (g : Nat) : Prop :=
  ∃ (B C : BRec) (w : WEntry), X.t.bs !! bl = some B ∧ w ∈ X.allEnts bl ∧ w.key = name ∧
    isBktFlag w.flags ∧ B.bm !! name = none ∧ c ≠ null ∧ (X.t.objs !! c).isNone ∧
    C.ib = ibOf w.value ∧ C.bv.tx' = B.bv.tx' ∧ C.bv.rootNode' = null ∧ C.nm = ∅ ∧
    C.bm = ∅ ∧ C.ns = ∅ ∧
    (inBucketRoot w.value = 0 →
      C.bv.page' ≠ null ∧ C.ipg = inlinePage w.value ∧
      ((w.vs = Src.view ∧ C.isrc = Src.view ∧ C.pst = PageSt.view) ∨
        (C.isrc = Src.own DFrac.discard ∧ C.pst = PageSt.none))) ∧
    (inBucketRoot w.value ≠ 0 → C.bv.page' = null ∧ C.pst = PageSt.none) ∧
    X' = { X with t := { X.t with bs := (X.t.bs.insert bl { B with bm := B.bm.insert name c }).insert c C },
                  live := X.live.insert c (), handles := X.handles.insert c (name, g) }

/-- The node `n` of `B` has the root `rt`: following `parent` within `B`'s nodes (`node.root`). -/
inductive nodeRootIn (B : BRec) : Loc → Loc → Prop
  | top (n : Loc) (r : NRec) : B.ns !! n = some r → r.nv.parent' = null → nodeRootIn B n n
  | up (n rt : Loc) (r : NRec) : B.ns !! n = some r → r.nv.parent' ≠ null →
      nodeRootIn B r.nv.parent' rt → nodeRootIn B n rt

/-! ## Frees (`Bucket.free`, `node.free`) -/

/-- The positions a walk of the logical tree visits from `pid`, in order (`_forEachPageNode`;
`fuel` bounds the depth). -/
def lposF (L : LTree) (bl : Loc) : Nat → w64 → List w64
  | 0, _ => []
  | n + 1, pid => pid :: match L bl pid with
    | some (false, ws) => ws.flatMap fun w => lposF L bl n w.pgid
    | _ => []

/-- The positions of bucket `bl`'s logical tree, in `forEachPageNode`'s order. -/
def WX.positions (X : WX) (bl : Loc) : List w64 := lposF (ltree X) bl X.fuel (X.rootPid bl)

/-- The page extent position `pid` of `bl` frees (`Free(txid, tx.page(id))`): its node's page
id, or the position's page; none for page id `0` (a node not read from a page). -/
def WX.posExtent (X : WX) (bl : Loc) (pid : w64) : Option (w64 × Nat) :=
  match X.t.bs !! bl with
  | none => none
  | some B =>
    let id := match resolve B pid with
      | some l => ((B.ns !! l).map fun r => r.nv.pgid').getD 0
      | none => pid
    if id = W64 0 then none
    else (X.v.pages !! id.toNat).map fun pg => (id, 1 + pageOverflow pg)

/-- The extents `Bucket.free` frees, in order. -/
def WX.extents (X : WX) (bl : Loc) : List (w64 × Nat) :=
  (X.positions bl).filterMap (X.posExtent bl)

/-- The freelist after freeing the extents `es` for `txid`, in order. -/
def FLPg.freeAll (fl : FLPg) (txid : w64) (es : List (w64 × Nat)) : FLPg :=
  es.foldl (fun f e => f.freePages txid e.1 e.2) fl

/-- The extents `es` can be freed in order for `txid`. -/
def FLPg.canFreeAll (fl : FLPg) (txid : w64) : List (w64 × Nat) → Prop
  | [] => True
  | e :: es => fl.canFree txid e.1 e.2 ∧ (fl.freePages txid e.1 e.2).canFreeAll txid es

/-- **`Bucket.free`'s records**: bucket `bl`'s header root page `0`, and each materialized node
its walk reached at page id `0`; nothing else changes. -/
def bktFreed (X X' : WX) (bl : Loc) : Prop :=
  ∃ B ns', X.t.bs !! bl = some B ∧
    X' = X.setBkt bl { B with ib := { B.ib with root' := W64 0 }, ns := ns' } ∧
    ∀ l, ns' !! l = (B.ns !! l).map fun r =>
      if ∃ pid ∈ X.positions bl, resolve B pid = some l
      then { r with nv := { r.nv with pgid' := W64 0 } } else r

/-! ## Allocation (`Tx.allocate`) -/

/-- `X` after a page of `count` slots at `id` was allocated at the buffer `p` (`tx.pages[id] =
p`, its bytes a zeroed header with the id and the overflow `count - 1`, the rest zero), and the
transaction's high-water mark `hwm`. -/
def WX.addPage (X : WX) (id : w64) (p : Loc) (count : Nat) (hwm : w64) : WX :=
  { X with t := { X.t with
      pm := X.t.pm.insert id p,
      bufs := X.t.bufs.insert id
        (encode (⟨id, W16 0, W16 0, W32 ((count - 1 : Nat) : Int)⟩ : Page) ++
          List.replicate (count * 4096 - 16) (W8 0)),
      mv := { X.t.mv with pgid' := hwm } } }

/-- A step of the freelist in a writer's spill: a free (of an extent) or an allocation. -/
inductive FLStep where
  | free (id : w64) (n : Nat)
  | alloc (id : w64) (n : Nat)

/-- The freelist after the steps `st` of the transaction `txid`. -/
def FLPg.applySteps (fl : FLPg) (txid : w64) (st : List FLStep) : FLPg :=
  st.foldl (fun f s => match s with
    | .free id n => f.freePages txid id n
    | .alloc id n => f.alloc txid id n) fl

/-! ## Rebalance (its post is spill's pre) and spill -/

/-- The depths of the leaves of the logical tree from `pid` (`fuel` bounds the depth). -/
def ldepthsF (L : LTree) (bl : Loc) : Nat → Nat → w64 → List Nat
  | 0, _, _ => []
  | n + 1, d, pid => match L bl pid with
    | some (true, _) => [d]
    | some (false, ws) => ws.flatMap fun w => ldepthsF L bl n (d + 1) w.pgid
    | none => []

/-- Every leaf of bucket `bl`'s logical tree at one depth. -/
def leafDepthOK (X : WX) (bl : Loc) : Prop :=
  ∃ d, ∀ x ∈ ldepthsF (ltree X) bl X.fuel 0 (X.rootPid bl), x = d

/-- Slot `s` is in the extent of a position of an opened bucket's logical tree, or of the base
tree of a bucket entry of the root that is not opened. -/
def lCovers (X : WX) (s : Nat) : Prop :=
  (∃ bl e, X.t.bs !! bl ≠ none ∧ e ∈ X.extents bl ∧ e.1.toNat ≤ s ∧ s < e.1.toNat + e.2) ∨
  (∃ n v, (n, v) ∈ rootEnts X ∧ bktLoc X n = none ∧ bucketHas X.v.pages v s)

/-- **`rebalance`'s post, which is `spill`'s pre** (design §4.2), from `X` (writer side `fl`)
to `X'` (`fl'`), for the writer's txid `txid`:
- `X'` is well-formed (`wOKR`: `wOK` but the branch nodes' pages; with its keys' bounds) and holds the same data, on the same view,
  with the same handles (the registry grown);
- no empty non-root node, every branch node of at least two entries, and every bucket's leaves at
  one depth (kept from `X`'s);
- the frees are `Free(txid, …)` steps of extents of the base view, and every base slot is still
  covered by the logical tree or pending. -/
def rebalOK (X X' : WX) (fl fl' : FLPg) (txid : w64) : Prop :=
  wOKR X' ∧ wtxData X' = wtxData X ∧ X'.v = X.v ∧ X'.handles = X.handles ∧ X'.rl = X.rl ∧
  (∀ x y, X.nloc !! x = some y → X'.nloc !! x = some y) ∧
  (∀ bl B, X'.t.bs !! bl = some B → ∀ l r, B.ns !! l = some r → l ∈ X'.live →
    (r.nv.parent' ≠ null → 0 < r.ws.length) ∧ (r.nv.isLeaf' = false → 2 ≤ r.ws.length)) ∧
  (∀ bl, X'.t.bs !! bl ≠ none → leafDepthOK X bl → leafDepthOK X' bl) ∧
  (∃ es : List (w64 × Nat), fl.canFreeAll txid es ∧ fl' = fl.freeAll txid es ∧
    ∀ e ∈ es, ∃ pg, X.v.pages !! e.1.toNat = some pg ∧ 1 + pageOverflow pg = e.2) ∧
  ∀ s, coversSlot X.v.pages s → lCovers X' s ∨ s ∈ pendSlots fl'

/-- **`spill`'s pre** (the part of `rebalOK`'s post about the records after it, `X`, and the
writer side's freelist `fl`): `X` well-formed; no empty non-root node, branch nodes of at least
two entries; every bucket's leaves at one depth; every base slot covered by the logical tree or
pending. -/
def spillPre (X : WX) (fl : FLPg) : Prop :=
  wOKR X ∧
  (∀ bl B, X.t.bs !! bl = some B → ∀ l r, B.ns !! l = some r → l ∈ X.live →
    (r.nv.parent' ≠ null → 0 < r.ws.length) ∧ (r.nv.isLeaf' = false → 2 ≤ r.ws.length)) ∧
  (∀ bl, X.t.bs !! bl ≠ none → leafDepthOK X bl) ∧
  ∀ s, coversSlot X.v.pages s → lCovers X s ∨ s ∈ pendSlots fl

/-! ## Reachability and dereference (the coverage contract) -/

/-- The buckets the code reaches from the root bucket through the `buckets` caches. -/
inductive bktReach (X : WX) : Loc → Prop
  | root : bktReach X X.rl
  | child (bl c : Loc) (B : BRec) (n : GoString) :
      X.t.bs !! bl = some B → B.bm !! n = some c → bktReach X bl → bktReach X c

/-- Node `d` is `n` or a descendant of it through `children` within `B`. -/
inductive descIn (B : BRec) : Loc → Loc → Prop
  | self (n : Loc) : descIn B n n
  | child (n c d : Loc) (r : NRec) : B.ns !! n = some r → c ∈ r.cs → descIn B c d → descIn B n d

/-- **The live objects are those the code reaches** (design §4.2's coverage contract): every live
bucket is reached from the root bucket, and every live node of a bucket descends from the root of
its root node's chain of parents (`b.rootNode.root()`, then `children`). -/
def liveReach (X : WX) : Prop :=
  (∀ bl B, X.t.bs !! bl = some B → bl ∈ X.live → bktReach X bl) ∧
  ∀ bl B l r, X.t.bs !! bl = some B → B.ns !! l = some r → l ∈ X.live →
    ∃ rt, nodeRootIn B B.bv.rootNode' rt ∧ descIn B rt l

/-- No live node holds a stale slice (what `dereference` copies from). -/
def liveFresh (X : WX) : Prop :=
  ∀ bl B l r, X.t.bs !! bl = some B → B.ns !! l = some r → l ∈ X.live →
    wsLive r.ws ∧ r.ksrc ≠ Src.stale

/-- The pages the writer's buffers hold (`tx.pages`' bytes, by id). -/
def WX.bufPages (X : WX) : Pages := GMap.ofList (X.t.bufs.toList.map fun e => (e.1.toNat, e.2))

/-- The root page of the root bucket's header (what `Commit` stores in the meta). -/
def WX.rootPage (X : WX) : Nat := ((X.t.bs !! X.rl).map fun B => B.ib.root'.toNat).getD 0

/-- **The committed state a successful spill leaves** (its tree; the metas and the freelist
page are `Commit`'s): the tree from the root bucket's new root page over the written buffers
and the base pages, at the transaction's high-water mark and txid. -/
def spillC (X' : WX) (base : Pages) : CommitSt :=
  { m0 := [], m1 := [], pages := treePages (X'.bufPages ∪ base) X'.rootPage,
    root := X'.rootPage, hwm := X'.t.mv.pgid'.toNat, txid := X'.t.mv.txid'.toNat, flpg := none }

/-- **`spill`'s post on success** (design §4.2, B6.2–3), from `X` (writer side `fl`, after
`rebalOK`) to `X'` (`fl'`), for the writer's txid `txid`, with `C` the base committed state
(`C.pages = X.v.pages`):
- the spilled tree `C' = spillC X' C.pages` is `treeOK` and holds the writer's data;
- every base page dropped from the tree is pending for `txid` (readers may still hold it);
- the tree's slots are base slots or allocated by the writer (`fl'` is `fl` after free and
  allocation steps, the high-water mark grown), and the allocated pages are written in
  `tx.pages` (the buffers; `C'`'s pages are theirs where they are not base pages);
- the base view's pages are unchanged (it may have been re-based by remaps). -/
def spillOK (X X' : WX) (C : CommitSt) (fl fl' : FLPg) (txid : w64) : Prop :=
  treeOK (spillC X' C.pages) ∧ treeData (spillC X' C.pages) = wtxData X ∧
  X'.v.pages = X.v.pages ∧ X.t.mv.pgid' ≤ X'.t.mv.pgid' ∧
  (∀ s ∈ treeSlots C, s ∉ treeSlots (spillC X' C.pages) → s ∈ pendSlots fl') ∧
  (∃ st : List FLStep, fl' = fl.applySteps txid st ∧
    ∀ s ∈ treeSlots (spillC X' C.pages), s ∈ treeSlots C ∨
      ((∃ id n, FLStep.alloc id n ∈ st ∧ id.toNat ≤ s ∧ s < id.toNat + n) ∨
        X.t.mv.pgid'.toNat ≤ s)) ∧
  ∀ id pg, (spillC X' C.pages).pages !! id = some pg →
    C.pages !! id = some pg ∨ X'.t.bufs !! W64 (id : Int) = some pg

/-! ## Readers' buckets and walks (the read path over a view's pages) -/

/-- The names of the nested buckets of the bucket whose value is `bv` (the root bucket's: its
header encoded), in order (`ForEachBucket`'s keys). -/
def bktNames (P : Pages) (bv : List w8) : List (List w8) :=
  (bktLeaves P bv).flatMap fun pg =>
    ((List.range (pageCount pg)).filter fun i => decide (leafFlags pg i % 2 = bucketLeafFlag)).map
      (leafKey pg)

/-- The bucket whose value is `bv` has the nested bucket `k` of value `cv`. -/
def bktEntry (P : Pages) (bv k cv : List w8) : Prop :=
  ∃ pg i, pg ∈ bktLeaves P bv ∧ i < pageCount pg ∧ leafKey pg i = k ∧
    leafFlags pg i % 2 = bucketLeafFlag ∧ leafValue pg i = cv

/-- The pages a walk visits (`forEachPageInternal`), in order, each with its stack of page ids
(root first; `fuel` bounds the depth). -/
def pageWalkF (P : Pages) : Nat → List Nat → List (Nat × List Nat)
  | 0, _ => []
  | n + 1, stk => match stk.getLast? with
    | none => []
    | some id => (id, stk) :: match P !! id with
      | some pg => if pageFlags pg = branchPageFlag
          then (List.range (pageCount pg)).flatMap fun i => pageWalkF P n (stk ++ [branchPgid pg i])
          else []
      | none => []

/-- The walk of the tree from page `root` (`tx.forEachPage(root, fn)`). -/
def pageWalk (P : Pages) (root : Nat) : List (Nat × List Nat) := pageWalkF P (P.size + 1) [root]

open Classical in
/-- **The ids `freepages` returns** for the committed state `C`: the slots in `[2, hwm)` no page
of its tree covers, increasing. -/
def freeIdsOf (C : CommitSt) : List w64 :=
  ((List.range' 2 (C.hwm - 2)).filter fun x => decide (¬ coversSlot C.pages x)).map
    fun (x : Nat) => W64 (x : Int)

/-! ## Lemma statements -/

/-- **`wOK` gives the freshness of a materialization** (U7). -/
theorem wOK_matFresh (X X' : WX) (bl l : Loc) (pgid : w64) (parent : Loc) (hok : wOK X)
    (h : nodeAdded X X' bl l pgid parent) (hpos : matPos X bl pgid parent) : matFresh X bl l := by
  sorry

/-- **`wOK`'s inline pages are leaves** (U7): an inline bucket's page, the one a materialization
reads, is a leaf page (`bktClean`'s `inlineGood`). -/
theorem wOK_inlineLeaf (X : WX) (bl : Loc) (pgid : w64) (hok : wOK X) :
    ∀ B pa pg, X.t.bs !! bl = some B → B.ib.root' = W64 0 →
      wpageAt X.v B pgid = some (pa, pg) → pageFlags pg = leafPageFlag := by
  sorry

/-- **Leaf and branch pages hold their elements** (`pageElemsIn`, for `matReady`). -/
theorem leafWF_elemsIn (pg : List w8) (len : Nat) (h : leafWF pg len)
    (hf : pageFlags pg = leafPageFlag) : pageElemsIn pg := by
  intro i hi
  have h1 := (h.2.2.1 i hi).1
  have h2 := h.1
  simp only [elemEnd, hf, ite_true]
  omega

theorem branchWF_elemsIn (pg : List w8) (len hwm : Nat) (h : branchWF pg len hwm)
    (hf : pageFlags pg = branchPageFlag) : pageElemsIn pg := by
  intro i hi
  have h1 := (h.2.2.2.1 i hi).1
  have h2 := h.2.1
  have hne : pageFlags pg ≠ leafPageFlag := by rw [hf]; decide
  simp only [elemEnd, hne, ite_false]
  omega

/-- **Materializing a page position keeps `wOK`** (the root page of a bucket with no root node,
or a child its branch node has not materialized). U7. -/
theorem wOK_nodeAdded (X X' : WX) (bl l : Loc) (pgid : w64) (parent : Loc)
    (hok : wOK X) (h : nodeAdded X X' bl l pgid parent) (hpos : matPos X bl pgid parent) :
    wOK X' := by
  sorry

/-- **The search finds a key iff the bucket has it** (U6's search lemma, which U7 and U9 use):
on a searchable bucket, a stack routing `k` ends at the leaf entry of key `k` if the bucket has
one, and at no entry of key `k` otherwise. -/
theorem lRoutes_found (X : WX) (bl : Loc) (els : List elemRef) (pids : List w64) (k : List w8)
    (hb : bktLocalOK X bl) (hp : lPath X bl els pids) (hr : lRoutes X bl els pids k) :
    (∃ w ∈ X.allEnts bl, w.key = k) ↔ wsFound (lLeaf X bl pids) k := by
  sorry

/-- **The routed leaf is where `k` lands** (`leafFor`, what `wtxData_put`/`_del` take): after
`Cursor.node` materialized the stack's path. U6. -/
theorem lRoutes_leafFor (X X' : WX) (bl l : Loc) (els : List elemRef) (pids : List w64)
    (k : List w8) (hok : wOK X) (hp : lPath X bl els pids) (hr : lRoutes X bl els pids k)
    (hg : matGrow X X' bl) (hl : ∃ B, X'.t.bs !! bl = some B ∧
      ∃ pid, pids.getLast? = some pid ∧ resolve B pid = some l) :
    leafFor X' bl k l := by
  sorry

end wops

end bbolt
end EtcdGrove
end Perennial
