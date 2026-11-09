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
  handles' caches merged), the pages it allocated (`tx.pages`).
* `nodeSize`, `nodeInsIdx`, `NodeR.put`, `NodeR.del`, `minKeysOf`, `splitIdx`: the code's
  arithmetic on a node, transparent.
* `DbM`: the `DB` fields the open/mmap/grow path reads and writes: open or not, the page size, the
  file's size, the mapping's size, whether the current meta is valid, the high-water mark.

## Resources (opaque, internal)

* `wtxCore tx γ C` (exclusive): the write transaction's physical state `C`, all of its node cache
  (`boltTx tx γ 1 T` with `T.rw` is `∃ C, wtxCore tx γ C` with `physRep T C`: `wtxCore_view`).
* `physRep T C` (an opaque `Prop`): the abstraction relation, `C`'s nodes over the mapped pages
  represent `T.cur`.
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

public import Spec.go_etcd_io.bbolt.Api
public import Spec.go_etcd_io.bbolt.internal.freelist.Api

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
`rootNode`, `none` while nil; integration I7, for `Bucket.inlineable`/`Bucket.write`). -/
structure TxCore where
  txid : w64
  hwm : w64
  root : w64
  nodes : Loc → Option NodeR
  pages : List w64
  roots : Loc → Option Loc

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

end pages

section pages_vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors}

/-- (internal) `b` is `CreateBucket`'s fresh local `Bucket`: a zero `InBucket`, a fresh
`NodeR.emptyLeaf` root, outside any transaction's node cache (exclusive). -/
opaque emptyBkt [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (b : Loc) : IProp GF := iprop(True)

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

end pages_laws

end Bbolt
end EtcdGrove
end Perennial
