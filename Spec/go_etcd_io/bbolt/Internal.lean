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

/-- (internal) The write transaction's physical state. -/
structure TxCore where
  txid : w64
  hwm : w64
  root : w64
  nodes : Loc → Option NodeR
  pages : List w64

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

/-- (internal) Page `id` of `tx`'s snapshot is at `p` with bytes `bs` (persistent). -/
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

end Bbolt
end EtcdGrove
end Perennial
