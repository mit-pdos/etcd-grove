/-
# bbolt's internals: vocabulary for the mirror-the-code specs (batch 4c)

Not part of the client API. The specs of package `bbolt`'s unexported functions (and `TxStats`'s
counters) are stated over the resources below, which the proof's invariant design realizes (the
old `bbolt-inv/design.md`: the node cache's abstraction relation, the transaction registry, the
file's shares). Round 1 (review C8): every function of package `bbolt` with a proved spec in the
old tree has a spec here; they mirror the code.

## The model (transparent)

* `InodeR`, `NodeR`: a node of a write transaction's cache (`node.go`): leaf or branch, its flags,
  key, page id (`0`: new), parent and children (locations), inodes (flags, page id, key, value).
* `TxCore`: the write transaction's physical state: its txid, its meta's high-water mark and root,
  its node cache (`nodes`: every cached node's model, keyed by location; `bnodes`: the bucket
  handles' caches merged), the pages it allocated (`tx.pages`) and their buffers (`bufs`), the
  bucket handles it caches with their paths (`bkts`) and roots (`roots`), the snapshot's pages
  (`snap`) that the nodes not yet read stand for, and the view's non-physical parts (`managed`,
  `noSync`, `base`, `gen`), which the abstraction relation compares with the view's (verify-round
  A11 F9: without them `physRep T C` could not tell views apart that differ only there, and
  `wtxCore_view` would identify a managed transaction with an unmanaged one).
* `nodeSize`, `nodeInsIdx`, `NodeR.put`, `NodeR.del`, `minKeysOf`, `splitIdx`: the code's
  arithmetic on a node, transparent.
* `DbM`: the `DB` fields the open/mmap/grow path reads and writes: open or not, the page size, the
  file's size, the mapping's size, whether the current meta is valid, the high-water mark.

## Resources (opaque, internal)

* `wtxCore tx γ C` (exclusive): the write transaction's physical state `C`, all of its node cache
  (`boltTx tx γ 1 T` with `T.rw` is `∃ C, wtxCore tx γ C` with `physRep T C`: `wtxCore_view`).
* `physRep T C` (an opaque `Prop`): the abstraction relation, `C`'s cached handles and nodes over
  the snapshot's pages represent `T.cur` (each cached handle the bucket at its path; a bucket with
  no cached handle by its parent's stored value), and `C`'s non-physical parts are `T`'s
  (`physRep_meta`). Its laws (verify-round A11 F9) are the steps of the write path:
  `physRep_set`/`physRep_del` (`node.put`/`node.del` at the key's leaf, `keyLeaf`, give the view
  with the key set or removed), `physRep_delBkt` (`DeleteBucket`'s), `wtxCore_seq` (a handle's
  sequence); the internal posts that only rearrange the cache keep it (`repKept`: materializing a
  node, `node.free`, `Bucket.free`, `node.rebalance`, `node.spill`, the allocations).
* `keyLeaf C p k n` (an opaque `Prop`): the cached node `n` is the leaf of the bucket at `p`'s tree
  (its handle in `C`) where the key `k` belongs (the leaf its search path ends in). Stable under
  `node.put`/`node.del` (they neither split nor merge; `spill`/`rebalance` do, at the commit).
* `wtxAt tx γ T st`: the commit's stages (`CommitStage`), as before.
* `txPage tx γ id p bs` (persistent): page `id` of `tx`'s snapshot is at `p` (in the mapping or
  `tx.pages`), its bytes `bs` (4d's decoders give its meaning: `BboltCommon.hdrOf`, `pageItems`).
* `dbRaw db γ M` (exclusive): `db`'s fields as the open path and the writer see them (`DbM`), with
  the file's OsFs halves the open database holds; what `Open` builds and `isBolt`'s locks then
  share out (`rwlock`: the writer's, `mmaplock`'s writer side: the mapping).
* `curPath tx γ c p gs T k` (exclusive): the cursor's stack is the search path of `k` in the bucket
  at `p` (`Cursor.search`'s result): its leaf element is the first not below `k`, possibly past its
  leaf's end.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Api
public import SpecPlan.Spec.go_etcd_io.bbolt.internal.freelist.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

/-- (internal) The stages of a write transaction's commit. -/
inductive CommitStage where
  | nodes
  | spilled
  | flushed

section model
variable [GooseExts]

/-- (internal) An inode as a node holds it. -/
structure InodeR where
  flags : w32
  pgid : w64
  key : GoString
  value : GoString

/-- (internal) A node of the write transaction's cache. -/
structure NodeR where
  isLeaf : Bool
  unbalanced : Bool
  spilled : Bool
  key : GoString
  pgid : w64
  parent : Loc
  children : List Loc
  inodes : List InodeR

/-- (internal) The write transaction's physical state (`roots b`: the bucket handle `b`'s
`rootNode`, `none` while nil; integration I7, for `Bucket.inlineable`/`Bucket.write`). Verify-round
(A11 F9): `bufs id`, the buffer of the allocated page `id` (its location and bytes, while
`wtxCore` holds it: `wtxCore_buf`); `bkts b`, the path of the cached bucket handle `b` (the root's,
`tx.root`, at `[]`; the child caches'); `snap id`, the bytes of page `id` of the snapshot the
transaction began at (the mapping's, fixed for its life); `managed`, `noSync`, `base`, `gen`: the
view's non-physical parts. -/
structure TxCore where
  txid : w64
  hwm : w64
  root : w64
  nodes : Loc → Option NodeR
  pages : List w64
  roots : Loc → Option Loc
  bufs : w64 → Option (Loc × List w8)
  bkts : Loc → Option BPath
  snap : w64 → Option (List w8)
  managed : Bool
  noSync : Bool
  base : Data
  gen : BPath → Nat

/-- (internal) The cache with the node at `n` set to `N`. -/
def TxCore.setNode (C : TxCore) (n : Loc) (N : NodeR) : TxCore :=
  { C with nodes := fun x => if x = n then some N else C.nodes x }

/-- (internal) The generations of `p` and its ancestors in `C` (`TxView.gens`' counterpart). -/
def TxCore.gens (C : TxCore) (p : BPath) : List Nat :=
  (List.range (p.length + 1)).map (fun i => C.gen (p.take i))

/-- `common.PageHeaderSize` and the element size (both 16). -/
@[word_unfold] def hdrSize : Nat := 16
@[word_unfold] def elemSize : Nat := 16

/-- (internal) `node.size()`: the header plus each element and its key and value. -/
def nodeSize (N : NodeR) : Nat :=
  hdrSize + (N.inodes.map (fun i => elemSize + i.key.length + i.value.length)).sum

/-- (internal) `sort.Search` for the first inode not below `k`. -/
def nodeInsIdx (N : NodeR) (k : GoString) : Nat :=
  (N.inodes.takeWhile (fun i => decide (go.GoStringLt i.key k))).length

/-- (internal) `node.put(old, new, v, pgid, flags)`: the inode at `old` replaced, or a new one
inserted at its place. -/
def NodeR.put (N : NodeR) (old new v : GoString) (pg : w64) (fl : w32) : NodeR :=
  let i := nodeInsIdx N old
  let x : InodeR := ⟨fl, pg, new, v⟩
  if (N.inodes[i]?.map (·.key)) = some old then
    { N with inodes := N.inodes.set i x }
  else { N with inodes := N.inodes.take i ++ [x] ++ N.inodes.drop i }

/-- (internal) `node.del(k)`: the inode at `k` removed (and the node marked unbalanced), if any. -/
def NodeR.del (N : NodeR) (k : GoString) : NodeR :=
  let i := nodeInsIdx N k
  if (N.inodes[i]?.map (·.key)) = some k then
    { N with inodes := N.inodes.eraseIdx i, unbalanced := true }
  else N

/-- (internal) `node.minKeys()`. -/
def minKeysOf (N : NodeR) : Nat := if N.isLeaf then 1 else 2

/-- (internal) `node.splitIndex(threshold)`: the first index `i ≥ MinKeysPerPage` at which the
running size passes the threshold (at most `len - MinKeysPerPage - 1`), and the size before it. -/
def splitIdx (N : NodeR) (th : Nat) : Nat × Nat :=
  let rec go (i sz : Nat) (rest : List InodeR) (fuel : Nat) : Nat × Nat :=
    match fuel, rest with
    | 0, _ => (i, sz)
    | _, [] => (i, sz)
    | f + 1, x :: xs =>
      let el := elemSize + x.key.length + x.value.length
      if 2 ≤ i ∧ th < sz + el then (i, sz)
      else if f = 0 then (i, sz + el) else go (i + 1) (sz + el) xs f
  if N.inodes.length ≤ 2 then (0, hdrSize)
  else go 0 hdrSize N.inodes (N.inodes.length - 2)

/-- (internal) **A fresh page run** (`db.allocate`'s buffer): `cnt` pages of 4096 bytes (the page
size `OptsM.ok` fixes), its header the id `id`, no flags, no elements, `cnt - 1` overflow pages
(a pooled page is zeroed when returned to the pool, a larger one is `make`'s): what `node.write`'s
`nodeWritable` and `freelist.Write` need of it. -/
def freshPage (id cnt : w64) (bs : List w8) : Prop :=
  bs.length = sint.nat cnt * 4096 ∧
  BboltCommon.hdrOf bs = ⟨id, W16 0, W16 0, W32 (sint.Z cnt - 1)⟩

/-- (internal) A `DB`'s fields on the open, mmap and grow paths. -/
structure DbM where
  opened : Bool
  pageSize : Nat
  fileSz : Nat
  dataSz : Nat
  metaOk : Bool
  hwm : Nat

end model

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors}

/-- (internal) The write transaction `tx`, at view `T`, at the commit stage `st` (exclusive). -/
opaque wtxAt [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (γ : BoltName)
    (T : TxView) (st : CommitStage) : IProp GF := iprop(True)

/-- (internal) The write transaction's physical state `C` (exclusive). -/
opaque wtxCore [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (γ : BoltName)
    (C : TxCore) : IProp GF := iprop(True)

/-- (internal) The abstraction relation: `C` represents the view `T`. -/
opaque physRep (T : TxView) (C : TxCore) : Prop

/-- (internal) The cached node `n` is the leaf of the bucket at `p`'s tree where `k` belongs. -/
opaque keyLeaf (C : TxCore) (p : BPath) (k : GoString) (n : Loc) : Prop

/-- (internal) **`C'` represents every view `C` does** (the cache rearranged, the data the same). -/
def repKept (C C' : TxCore) : Prop := ∀ T, physRep T C → physRep T C'

/-- (internal) The key a cursor's state `st` is about at the view `T`: the sought key (`curPath`),
or the key of the entry it is at. -/
def curKey (T : TxView) (p : BPath) : Option Nat ⊕ GoString → GoString → Prop
  | .inr k, k' => k' = k
  | .inl (some i), k' => ∃ v, (T.ents p)[i]? = some (k', v)
  | .inl none, _ => False

/-- (internal) **`T'` differs from `T` only at and below the bucket `q`** (re-review N2:
`DeleteBucket`'s recursion deletes the nested buckets of the child `q`): the same kind, base and
mode, the bucket `q` still a bucket (its counter and entries any), the generations of `q` and
above unchanged. `dropBkt` of the parent's key `q`'s name agrees on both (`physRep_delBkt` then
gives the same view). -/
def TxView.sameAt (T T' : TxView) (q : BPath) : Prop :=
  T'.rw = T.rw ∧ T'.managed = T.managed ∧ T'.base = T.base ∧ T'.noSync = T.noSync ∧
  T.cur.bktAt q ∧
  (∃ (s : w64) (es : List (GoString × Ent)), T'.cur = T.cur.modAt q (fun _ => Ent.bkt s es)) ∧
  (∀ x, (q.isPrefixOf x && !(x == q)) = false → T'.gen x = T.gen x)

/-- (internal) No handle at or below `q` is cached in `C` (`DeleteBucket` dropped the deleted
bucket's handle from its parent's cache, its nested ones dropped by the recursion). -/
def bktDropped (C : TxCore) (q : BPath) : Prop :=
  ∀ b q', C.bkts b = some q' → q.isPrefixOf q' = false

/-- (internal) Page `id` of `tx`'s snapshot is at `p` with bytes `bs` (persistent). Its
realization keeps what 4d's page specs take (integration I7): `pageHeaderSize ≤ bs.length`, the
header's id is `id` and its flags valid (`Page.FastCheck`), a branch or leaf page is
`BboltCommon.pageLaidOut` (so `ReadInodeFromPage`'s `pageReadable`), each branch element's child
is again a page of the snapshot, the extent is mapped (or is `tx.pages`' buffer). -/
opaque txPage [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (γ : BoltName) (id : w64)
    (p : Loc) (bs : List w8) : IProp GF := iprop(True)

/-- (internal) `db`'s fields `M` and its file's share (exclusive). -/
opaque dbRaw [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (db : Loc) (γ : BoltName) (M : DbM) :
    IProp GF := iprop(True)

/-- (internal) The cursor's stack is the search path of `k` (exclusive). -/
opaque curPath [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (γ : BoltName) (c : Loc)
    (p : BPath) (gs : List Nat) (T : TxView) (k : GoString) : IProp GF := iprop(True)

end vocab

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- (internal) A write transaction is its physical state under the abstraction relation. -/
def wtxCore_view.spec [HasExt osFsExt] : Prop :=
  ∀ tx γ T, T.rw = true →
    (boltTx (GF := GF) tx γ 1 T ⊣⊢ ∃ C, wtxCore tx γ C ∗ ⌜physRep T C⌝)

/-- (internal) `txPage` is persistent. -/
def txPage_persistent.spec [HasExt osFsExt] : Prop :=
  ∀ tx γ id p bs, Persistent (txPage (GF := GF) tx γ id p bs)

end laws

/-! ## The freelist's side (integration I7)

The freelist (`db.freelist`, 4d's `Freelist.flOwn`/`flReaders`) lives in the opaque resources
above: `flOwn` in the writer's (`wtxCore`, `wtxAt`, `dbRaw` before the database is shared),
`flReaders` in `isBolt`'s `metalock` invariant (a `nil` freelist before `loadFreelist` publishes
it, while `Open` still owns the database). What those realizations keep, so that every
`Freelist.Interface.<M>` premise holds at bbolt's calls:

* **readers** (`readersOk`, `R.length < 2 ^ 62`): `R` is the txids of the registered read
  transactions, each a committed meta's txid: at least 1 (`fileHolds`: `init` writes txid 1 on its
  second meta, and the txid only grows) and at most the current txid, below `2 ^ 63` (the file's
  bound plus at most `2 ^ 62` commits, one receipt each, `Open`'s `ReceiptBoundLe`); one per
  `threadTok` (`2 ^ 29`).
* **counts** (`F.count < flMaxIds`): every free or pending id is below the high-water mark,
  at most `2 ^ 36`.
* **frees** (`canFree`, then `canRollback`): a page freed by the writer `txid` is a page of the
  base tree (a cached node with `pgid ≠ 0`, `node.free` setting it to `0`; a page `Bucket.free`
  walks; the base meta's freelist page in `Commit`), each extent freed at most once in a
  transaction; the base tree's pages are never free or pending (released pages are unreachable),
  and were allocated (run start in `allocs`, if at all) by a committed txid `< txid`. So every
  pending entry `txid` made has `alloc ≠ txid` (`canRollback`).
* **reloads** (4d's F1 premise, `req/go_etcd_io_bbolt_internal_freelist.md`, "from 4d"): **every
  free page is among the current meta's freelist ids (a synced freelist), or among the pages the
  current meta's tree does not reach (`freepages`)**, and none is pending: a free page is never in
  a committed tree; it was free at the last commit (written by its `freelist.Write`), or released
  since from a pending page that commit wrote, or reloaded. So the ids `Reload`/`NoSyncReload`
  get, the pending ones dropped, are empty only when no page is free.
-/

section freelist_vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors}

/-- (internal) The pages `ids` are exactly those from 2 to below the current meta's high-water
mark that the current meta's tree does not reach (`db.freepages()`'s result), as of `db`'s
current meta (exclusive; consumed by the reload it justifies). With the freelist's invariant
(every free page unreached and not pending) it gives 4d's F1 premise of `Init`/`NoSyncReload`. -/
opaque dbUnreached [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (db : Loc) (γ : BoltName)
    (ids : List go_etcd_io.bbolt.internal.common.Pgid) : IProp GF := iprop(True)

end freelist_vocab

/-! ## The pages' side (integration I7)

4d's `internal/common` model (`BboltCommon`: `InodeM`, `hdrOf`, `withHdr`, `writeNode`,
`nodeFits`, `pageItems`) as the node specs use it: a node's inodes as page items (`NodeR.itemsM`),
the header `node.write` stores (`nodeHdr`), the page it leaves (`nodePage`), what it needs of the
page and the node (`nodeWritable`: an empty header, fewer than `0xFFFF` inodes, 4d's `nodeFits`, a
branch's children not the page itself), and an inline bucket's root (`inlineOk`, what
`Bucket.inlineable` checks). `nodeSize N` is `pageHeaderSize + (nodeBody true N.itemsM).length`
(16 bytes per element of either kind). -/

section pages
variable [GooseExts]

/-- (internal) An inode of a node as 4d's page item. -/
def InodeR.toM (i : InodeR) : BboltCommon.InodeM := ⟨i.flags, i.pgid, i.key, i.value⟩

/-- (internal) A page item as a node's inode (`node.read`). -/
def InodeR.ofM (m : BboltCommon.InodeM) : InodeR := ⟨m.flags, m.pgid, m.key, m.value⟩

/-- (internal) A node's inodes as page items. -/
def NodeR.itemsM (N : NodeR) : List BboltCommon.InodeM := N.inodes.map InodeR.toM

/-- (internal) The header `n.write(p)` stores: the node's kind and its inodes' count. -/
def nodeHdr (h : go_etcd_io.bbolt.internal.common.Page) (N : NodeR) :
    go_etcd_io.bbolt.internal.common.Page :=
  { h with flags' := if N.isLeaf then BboltCommon.leafPageFlag else BboltCommon.branchPageFlag,
           count' := W16 (N.inodes.length : Int) }

/-- (internal) **The page `n.write(p)` leaves** in the bytes `bs`: the header store, then 4d's
`writeNode` of the inodes (nothing for an empty node: `writeNode bs []` is `bs`). -/
def nodePage (bs : List w8) (N : NodeR) : List w8 :=
  BboltCommon.writeNode (BboltCommon.withHdr bs (nodeHdr (BboltCommon.hdrOf bs) N)) N.itemsM

/-- (internal) What `n.write(p)` needs of the page's header `h` and of the node (its `Assert`s
and panics, and 4d's `WriteInodeToPage` premises). -/
def nodeWritable (h : go_etcd_io.bbolt.internal.common.Page) (N : NodeR) : Prop :=
  h.count' = W16 0 ∧ h.flags' = W16 0 ∧ N.inodes.length < 0xFFFF ∧
  BboltCommon.nodeFits N.itemsM ∧ (N.isLeaf = false → ∀ i ∈ N.inodes, i.pgid ≠ h.id')

/-- (internal) **A bucket's root node can be inlined** (`b.inlineable()`): a leaf of no nested
bucket (`BucketLeafFlag` clear), at most a quarter page (`maxInlineBucketSize`, 1024) written. -/
def inlineOk (N : NodeR) : Prop :=
  N.isLeaf = true ∧ nodeSize N ≤ 1024 ∧ ∀ i ∈ N.inodes, i.flags &&& BboltCommon.bucketLeafFlag = W32 0

/-- (internal) A new empty leaf (`&node{isLeaf: true}`, `CreateBucket`'s inline bucket's root). -/
def NodeR.emptyLeaf : NodeR := ⟨true, false, false, [], W64 0, Loc.null, [], []⟩

/-- (internal) The value `CreateBucket` stores for a new bucket (`Bucket.write` of its fresh local:
a zero header, then an empty leaf page). -/
def emptyBktVal : GoString :=
  BboltCommon.encInBucket ⟨W64 0, W64 0⟩ ++
    nodePage (List.replicate (nodeSize NodeR.emptyLeaf) (W8 0)) NodeR.emptyLeaf

/-- (internal) **What `node.put`'s flags and value store**, as an entry: a plain value (flags `0`),
or a new empty bucket (`BucketLeafFlag`, `emptyBktVal`). -/
def newEnt (fl : w32) (vb : GoString) (x : Ent) : Prop :=
  (fl = W32 0 ∧ x = Ent.val vb) ∨
  (fl = BboltCommon.bucketLeafFlag ∧ vb = emptyBktVal ∧ x = Ent.bkt (W64 0) [])

end pages

section pages_vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors}

/-- (internal) `b` is `CreateBucket`'s fresh local `Bucket`: a zero `InBucket`, a fresh
`NodeR.emptyLeaf` root, outside any transaction's node cache (exclusive). -/
opaque emptyBkt [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (b : Loc) : IProp GF := iprop(True)

/-- (internal) `v` is the value `tx`'s view stores for the bucket at `p` (persistent: 4d's
`encInBucket` of its header, then, when its root is 0, its inline leaf page; in the mapping or a
node of the writer), what `openBucket` reads through 4d's `inBucket_view` (`bucketHeaderSize ≤`
its length). -/
opaque bktVal [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (γ : BoltName) (p : BPath)
    (v : GoSlice) : IProp GF := iprop(True)

/-- (internal) A cursor's state between internal calls: positioned (`boltCur`, `.inl pos`) or the
search path of a key, possibly past its leaf's end (`curPath`, `.inr k`: after `seek`). -/
def curSt [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (γ : BoltName) (c : Loc)
    (p : BPath) (gs : List Nat) (T : TxView) : Option Nat ⊕ GoString → IProp GF
  | .inl pos => boltCur tx γ c p gs T pos
  | .inr k => curPath tx γ c p gs T k

/-- (internal) **What `c.seek(kb)` returns** (`k`, `v`, `fl`) in the bucket `p` of entries `es`:
`kb`'s entry if the bucket has it (its key; a value's bytes, or a bucket's stored value `bktVal`
with `BucketLeafFlag` set); else nil or some other key (the next entry in its leaf, if any). -/
def seekRaw [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (γ : BoltName) (p : BPath)
    (es : List CurEnt) (kb : GoString) (k v : GoSlice) (fl : w32) : IProp GF :=
  match es.find? (fun e => decide (e.1 = kb)) with
  | some (_, some vb) => iprop(⌜k ≠ slice.nil ∧ fl &&& BboltCommon.bucketLeafFlag = W32 0⌝ ∗
      txBytes tx γ k kb ∗ txBytes tx γ v vb)
  | some (_, none) => iprop(⌜k ≠ slice.nil ∧ fl &&& BboltCommon.bucketLeafFlag ≠ W32 0⌝ ∗
      txBytes tx γ k kb ∗ bktVal tx γ (p.child kb) v)
  | none => iprop(⌜k = slice.nil⌝ ∨ ∃ kb' : GoString, ⌜kb' ≠ kb⌝ ∗ txBytes tx γ k kb')

end pages_vocab

section pages_laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- (internal) **Every cached node's keys are non-empty** (`Put` and `CreateBucket` refuse an
empty key, a page's keys are non-empty by `pageReadable`, a parent's key is a child's first): what
gives 4d's `nodeFits` its key clause at `node.write`. -/
def wtxCore_keys.spec [HasExt osFsExt] : Prop :=
  ∀ tx γ C, wtxCore (GF := GF) tx γ C ⊢
    ⌜∀ n N, C.nodes n = some N → ∀ i ∈ N.inodes, i.key ≠ []⌝

/-- (internal) `bktVal` is persistent. -/
def bktVal_persistent.spec [HasExt osFsExt] : Prop :=
  ∀ tx γ p v, Persistent (bktVal (GF := GF) tx γ p v)

end pages_laws

/-! ## The abstraction relation's laws (verify-round A11 F9) -/

section rep_laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [common_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- (internal) **The abstraction relation pins the view's non-physical parts** to `C`'s, and the
view is a write transaction's, well-formed. -/
def physRep_meta.spec : Prop :=
  ∀ T C, physRep T C →
    T.rw = true ∧ T.managed = C.managed ∧ T.noSync = C.noSync ∧ T.base = C.base ∧ T.gen = C.gen ∧
    T.cur.wf

/-- (internal) **The writer's high-water mark is at least 2** (the two meta pages; `init` writes
4): `node.put`'s `pg < C.hwm` at `pg = 0` (`Put`, `CreateBucket*`; re-review N7). -/
def wtxCore_hwm.spec [HasExt osFsExt] : Prop :=
  ∀ tx γ C, wtxCore (GF := GF) tx γ C ⊢ ⌜2 ≤ uint.nat C.hwm⌝

/-- (internal) **`node.put` at the key's leaf sets the key** (`Bucket.Put`: a value, flags `0`;
`CreateBucket*`: a new inline bucket's value, `BucketLeafFlag`; `newEnt`), the key not a nested
bucket, within the bounds `Ent.wf` keeps. -/
def physRep_set.spec : Prop :=
  ∀ T C p k n N fl vb x, physRep T C → keyLeaf C p k n → C.nodes n = some N → newEnt fl vb x →
    (T.cur.atPath (p.child k)).any Ent.isBkt = false → k ≠ [] → k.length ≤ maxKeySize →
    (x.isBkt = false → k.length + vb.length ≤ bboltEntryMax) →
    physRep (T.setCur (T.cur.modAt p (fun e => e.setKey k (some x))))
      (C.setNode n (N.put k k vb (W64 0) fl))

/-- (internal) **`node.del` at the key's leaf removes the key** (`Bucket.Delete`, `Cursor.Delete`),
the key not a nested bucket. -/
def physRep_del.spec : Prop :=
  ∀ T C p k n N, physRep T C → keyLeaf C p k n → C.nodes n = some N →
    (T.cur.atPath (p.child k)).any Ent.isBkt = false →
    physRep (T.setCur (T.cur.modAt p (fun e => e.setKey k none))) (C.setNode n (N.del k))

/-- (internal) **`DeleteBucket`'s `node.del` removes the nested bucket** once no handle at or
below it is cached (`bktDropped`), with its path's generation bumped and those below reset
(`TxView.dropBkt`). The view `T` here is the one the cache represents once the deleted bucket's
handle is dropped (its contents as its parent's stored value has them: a realization step of
`DeleteBucket`'s own body, `delete(b.buckets, key)`, `child.nodes = nil`, `child.rootNode = nil`);
`dropBkt` of it is `dropBkt` of the view before (the bucket is gone either way). -/
def physRep_delBkt.spec : Prop :=
  ∀ T C p k n N s es, physRep T C → keyLeaf C p k n → C.nodes n = some N →
    T.cur.atPath (p.child k) = some (Ent.bkt s es) → bktDropped C (p.child k) →
    physRep (T.dropBkt p k) { C.setNode n (N.del k) with gen := (T.dropBkt p k).gen }

/-- (internal) **A page buffer `wtxCore` holds is lent out and back** (`node.spill` writes a node
into the page `tx.allocate` gave, `commitFreelist` the freelist; then `tx.write` writes them):
taken with its bytes, given back with any bytes. -/
def wtxCore_buf.spec [HasExt osFsExt] : Prop :=
  ∀ tx γ C id pg bs, C.bufs id = some (pg, bs) →
    (wtxCore (GF := GF) tx γ C ⊣⊢
      wtxCore tx γ { C with bufs := fun x => if x = id then none else C.bufs x } ∗
        bytesPointsto pg (DFrac.own 1) bs)

/-- (internal) **A current handle's sequence** (`SetSequence`, `NextSequence`), once its root is
materialized (`Bucket.node` at its root page with a nil parent: so `spill` writes its header): its
`InBucket`'s points-to holds the bucket's counter, and storing `v` there sets it. -/
def wtxCore_seq.spec [HasExt osFsExt] : Prop :=
  ∀ tx γ C T b p gs, physRep T C → T.gens p = gs → (C.roots b).isSome = true →
    wtxCore (GF := GF) tx γ C ∗ bktH tx γ b p gs ⊢
      ∃ (l : Loc) (ib : go_etcd_io.bbolt.internal.common.InBucket),
        structFieldRef go_etcd_io.bbolt.Bucket go!"InBucket" b ↦{DFrac.discard} l ∗ l ↦ ib ∗
        ⌜ib.sequence' = ((T.cur.atPath p).map Ent.seq).getD (W64 0)⌝ ∗
        ∀ v : w64, l ↦ ({ ib with sequence' := v } : go_etcd_io.bbolt.internal.common.InBucket) -∗
          ∃ C' : TxCore, wtxCore tx γ C' ∗
            ⌜physRep (T.setCur (T.cur.modAt p (fun e => e.setSeq v))) C'⌝

end rep_laws

end Bbolt
end EtcdGrove
end Perennial
