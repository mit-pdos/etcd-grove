/-
# mvcc's internals (batch 3e): the vocabulary of the internal helpers' specs

Imported by mvcc's own spec files only (no other directory imports it): the key index and its
generations (`key_index.go`), the tree index (`index.go`), the revision encoding (`revision.go`),
the store's and its transactions' internal handles (`kvstore.go`, `kvstore_txn.go`), the hasher
(`hash.go`). The internal specs mirror their code (PRINCIPLES, "Scope": an internal helper's spec
may); the pure models are transparent, the resources opaque.

## Pure models

* `Rev` (a `Revision`'s main and sub), `Rev.gt` (`GreaterThan`), `revVal` (the Go value), `revBytes`
  (`BucketKeyToBytes`: 8 big-endian bytes of the main, `_`, 8 of the sub, `t` for a tombstone),
  `revOfBytes` (`BytesToBucketKey`'s parse, `none` where it panics).
* `Gen`, `KeyIndexM` (a key index's modified revision and generations), `kiPut`, `kiTombstone`
  (`none`: the last generation is empty, `ErrRevisionNotFound`), `kiRestore`, `kiRestoreTombstone`,
  `kiIsEmpty`, `kiFindGen`, `genWalk`, `kiGet`, `kiDoCompact` (the generation and revision index
  compaction keeps, and the revisions it marks available), `kiCompact`, `kiKeepDrop`; `kiWf` (every
  generation but the last non-empty, revisions increasing: what `put`'s and `doCompact`'s panics
  need).
* `IndexM` (key ↦ key index), `idxGet`, `idxPut`, `idxTombstone`, `idxCompact`, `idxKeep`,
  `idxRange` (a range of the index at a revision, the limit and total count as `treeIndex.Range`).

## Resources (opaque)

* `ownKi p k ki dq`: `p` is a `*keyIndex` of key `k` (its key slice read-only) at the model `ki`.
  `ownGenAt p g dq`: `p` points at a `generation` at `g`.
* `IdxName`; `isTreeIndex idx γi` (persistent): `idx` (the `index` value, a `*treeIndex`) with names
  `γi`, its lock's invariant holding the tree; `idxModel γi M` (exclusive, the store's invariant
  holds it): the index is `M`. `ownIdxPriv ti M` (exclusive): a tree index no other goroutine can
  reach (`restore` rebuilds a fresh one), its keys' pointers `M`'s; `idxShare` publishes it.
  `treeOwn ti dq M`: the tree's content, as the lock holder sees it (the unsafe helpers').
* `isStore s γ` (persistent): `s` is the `*store` of `γ` (the internal handle under `isMvcc`).
  `storeW s γ` (exclusive): `s.mu` held for writing (`Compact`, `Restore`, `Commit`, the barrier),
  with what it protects. `storeR s γ σ` (exclusive): `s.mu` held for reading at the state `σ` (a
  transaction).
* `storeTxnR t γ trace σ`, `storeTxnW t γ trace σ pend` (exclusive): `*storeTxnRead`/`*storeTxnWrite`
  at `t` (`storeTxnCommon` embedded); `mvccTxn` of their `metricsTxnWrite` wrappers is built from
  them (`newMetricsTxnRead`/`Write`).
* `compactJobRes s γ c prev` (exclusive): what a scheduled compaction job at `c` (previous
  compaction `prev`) runs with (the safe-range right, the storage's batch lock's resources, a
  reader slot, the job's receipts): `store.compact` schedules it.
* `isHasher h c r keep dq` (`kvHasher`'s fields), `isHashStorageAt hs s γ`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire
open go_etcd_io.etcd.server.v3.storage.mvcc
open Classical

section pure
variable [GooseExts]

/-! ## Revisions and their bytes -/

/-- `mvcc.Revision`: a main revision and a sub-revision. -/
structure Rev where
  main : w64
  sub : w64

/-- `Revision.GreaterThan`: lexicographic on `(main, sub)`, as signed integers. -/
def Rev.gt (a b : Rev) : Bool :=
  decide (sint.Z b.main < sint.Z a.main) || (decide (a.main = b.main) && decide (sint.Z b.sub < sint.Z a.sub))

def Rev.zero : Rev := ⟨W64 0, W64 0⟩

/-- The Go value of a revision. -/
def revVal (r : Rev) : Revision := { Main' := r.main, Sub' := r.sub }

def revOf (r : Revision) : Rev := ⟨r.Main', r.Sub'⟩

/-- Eight big-endian bytes (`binary.BigEndian.PutUint64`). -/
def u64Be (x : w64) : List w8 :=
  (List.range 8).reverse.map fun i => W8 ((uint.nat x / 256 ^ i) % 256)

/-- **`BucketKeyToBytes`** of a revision (`t` appended for a tombstone). -/
def revBytes (r : Rev) (tomb : Bool) : GoString :=
  u64Be r.main ++ [W8 95] ++ u64Be r.sub ++ (if tomb then [W8 116] else [])

/-- The integer eight big-endian bytes encode. -/
def beU64 (l : List w8) : w64 := W64 (l.foldl (fun acc b => acc * 256 + uint.nat b) 0)

/-- **`BytesToBucketKey`**'s parse: `none` where it panics (a length other than 17 or 18, no `_`,
a negative main or sub). -/
def revOfBytes (b : GoString) : Option (Rev × Bool) :=
  if (b.length = 17 ∨ b.length = 18) ∧ b[8]? = some (W8 95) then
    let r : Rev := ⟨beU64 (b.take 8), beU64 ((b.drop 9).take 8)⟩
    if 0 ≤ sint.Z r.main ∧ 0 ≤ sint.Z r.sub then some (r, decide (b.length = 18 ∧ b[17]? = some (W8 116)))
    else none
  else none

/-- `isTombstone`: an 18-byte key ending in `t`. -/
def isTombBytes (b : GoString) : Bool := decide (b.length = 18 ∧ b[17]? = some (W8 116))

/-! ## The key index (`key_index.go`) -/

/-- A generation: its version count, the revision it was created at, its revisions. -/
structure Gen where
  ver : w64
  created : Rev
  revs : List Rev

def Gen.empty : Gen := ⟨W64 0, Rev.zero, []⟩

/-- A key index's mutable part (its key is fixed): its last change and its generations. -/
structure KeyIndexM where
  modified : Rev
  gens : List Gen

def KeyIndexM.fresh : KeyIndexM := ⟨Rev.zero, []⟩

/-- `keyIndex.put(main, sub)` (`rev` above `modified`: `put` panics otherwise). -/
def kiPut (ki : KeyIndexM) (rev : Rev) : KeyIndexM :=
  let gens := if ki.gens = [] then [Gen.empty] else ki.gens
  let g := gens.getLastD Gen.empty
  let g' : Gen := { ver := g.ver + W64 1, created := if g.revs = [] then rev else g.created,
                    revs := g.revs ++ [rev] }
  { modified := rev, gens := gens.dropLast ++ [g'] }

/-- `keyIndex.isEmpty()`: one generation, empty. -/
def kiIsEmpty (ki : KeyIndexM) : Bool :=
  match ki.gens with
  | [g] => decide (g.revs = [])
  | _ => false

/-- The last generation is empty. -/
def kiLastEmpty (ki : KeyIndexM) : Bool := decide ((ki.gens.getLastD Gen.empty).revs = [])

/-- `keyIndex.tombstone(main, sub)` on a non-empty key index: `none` (`ErrRevisionNotFound`) if its
last generation is empty, else a put and a new empty generation. -/
def kiTombstone (ki : KeyIndexM) (rev : Rev) : Option KeyIndexM :=
  if kiLastEmpty ki then none
  else let ki' := kiPut ki rev; some { ki' with gens := ki'.gens ++ [Gen.empty] }

/-- `keyIndex.restore(created, modified, ver)` on a key index with no generation. -/
def kiRestore (created modified : Rev) (ver : w64) : KeyIndexM :=
  ⟨modified, [⟨ver, created, [modified]⟩]⟩

/-- `keyIndex.restoreTombstone(main, sub)` on a key index with no generation. -/
def kiRestoreTombstone (rev : Rev) : KeyIndexM :=
  ⟨rev, [⟨W64 1, Rev.zero, [rev]⟩, Gen.empty]⟩

/-- `generation.walk(f)`: from the last revision back, the index of the first that `p` fails,
`-1` if none. -/
def genWalk (revs : List Rev) (p : Rev → Bool) : Int :=
  match revs.reverse.findIdx? (fun r => !p r) with
  | some i => (revs.length - 1 - i : Nat)
  | none => -1

/-- `keyIndex.findGeneration(rev)`, scanning from generation `cg` down (`fuel`). -/
def kiFindGenAux (gens : List Gen) (rev : w64) : Nat → Option Nat
  | 0 => none
  | cg + 1 =>
    let g := gens.getD cg Gen.empty
    if g.revs = [] then kiFindGenAux gens rev cg
    else if cg ≠ gens.length - 1 ∧ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z rev then none
    else if sint.Z (g.revs.headD Rev.zero).main ≤ sint.Z rev then some cg
    else kiFindGenAux gens rev cg

/-- `keyIndex.findGeneration(rev)`: the index of the generation the key is in at `rev`, if any. -/
def kiFindGen (ki : KeyIndexM) (rev : w64) : Option Nat := kiFindGenAux ki.gens rev ki.gens.length

/-- **`keyIndex.get(atRev)`** on a non-empty key index: the key's revision at `atRev`, its
generation's creation revision and its version there; `none` (`ErrRevisionNotFound`) if absent. -/
def kiGet (ki : KeyIndexM) (atRev : w64) : Option (Rev × Rev × w64) :=
  match kiFindGen ki atRev with
  | none => none
  | some gi =>
    let g := ki.gens.getD gi Gen.empty
    let n := genWalk g.revs (fun r => decide (sint.Z atRev < sint.Z r.main))
    if g.revs = [] ∨ n = -1 then none
    else some (g.revs.getD n.toNat Rev.zero, g.created,
      g.ver - W64 (g.revs.length - n.toNat - 1))

/-- `generation.isRecreatedAt(rev)`. -/
def genRecreatedAt (g : Gen) (rev : w64) : Bool :=
  decide (g.revs ≠ [] ∧ (g.revs.headD Rev.zero).main = rev)

/-- `doCompact`'s generation: the first that is the last, or whose tombstone is above `atRev`, or
at `atRev` with the next one not recreated there (`fuel`: from `i`). -/
def kiCompactGen (gens : List Gen) (atRev : w64) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
    if i + 1 < gens.length then
      let tomb := ((gens.getD i Gen.empty).revs.getLastD Rev.zero).main
      if sint.Z atRev < sint.Z tomb then i
      else if tomb = atRev ∧ !genRecreatedAt (gens.getD (i + 1) Gen.empty) atRev then i
      else kiCompactGen gens atRev fuel (i + 1)
    else i

/-- **`keyIndex.doCompact(atRev, available)`**: the generation index and revision index compaction
keeps from, and the revisions it marks available (those of that generation at or below `atRev`
from the walk's stop on: the walk adds the first it stops at). -/
def kiDoCompact (ki : KeyIndexM) (atRev : w64) : Nat × Int × List Rev :=
  let gi := kiCompactGen ki.gens atRev ki.gens.length 0
  let g := ki.gens.getD gi Gen.empty
  let n := genWalk g.revs (fun r => decide (sint.Z atRev < sint.Z r.main))
  (gi, n, if n = -1 then [] else [g.revs.getD n.toNat Rev.zero])

/-- **`keyIndex.compact(atRev, available)`**: the generations before the kept one dropped, the kept
one's revisions before the kept index dropped. -/
def kiCompact (ki : KeyIndexM) (atRev : w64) : KeyIndexM :=
  let (gi, n, _) := kiDoCompact ki atRev
  let gens := ki.gens.drop gi
  match gens with
  | g :: rest => { ki with gens := (if g.revs ≠ [] ∧ n ≠ -1 then { g with revs := g.revs.drop n.toNat } else g) :: rest }
  | [] => { ki with gens := [] }

/-- **`keyIndex.keep(atRev, available)`**: `doCompact`'s available revision, but dropped again when
it is a tombstone (the last of a generation that is not the last). -/
def kiKeep (ki : KeyIndexM) (atRev : w64) : List Rev :=
  if kiIsEmpty ki then []
  else
    let (gi, n, av) := kiDoCompact ki atRev
    let g := ki.gens.getD gi Gen.empty
    if g.revs ≠ [] ∧ n = (g.revs.length - 1 : Nat) ∧ gi ≠ ki.gens.length - 1 then [] else av

/-- **A well-formed key index**: every generation but the last non-empty, revisions strictly
increasing across them, `modified` the last revision. -/
def kiWf (ki : KeyIndexM) : Prop :=
  (∀ i, i + 1 < ki.gens.length → (ki.gens.getD i Gen.empty).revs ≠ []) ∧
  (ki.gens.flatMap Gen.revs).Pairwise (fun a b => Rev.gt b a = true) ∧
  (∀ r ∈ ki.gens.flatMap Gen.revs, Rev.gt r ki.modified = false)

/-! ## The index (`index.go`) -/

/-- The index: each key's key index. -/
abbrev IndexM := GoString → Option KeyIndexM

def idxGet (M : IndexM) (k : GoString) : Option KeyIndexM := M k

/-- `treeIndex.Put(key, rev)`. -/
def idxPut (M : IndexM) (k : GoString) (rev : Rev) : IndexM :=
  fun k' => if k' = k then some (kiPut ((M k).getD KeyIndexM.fresh) rev) else M k'

/-- `treeIndex.Tombstone(key, rev)`: `none` (`ErrRevisionNotFound`) for a key with no key index or
an empty last generation. -/
def idxTombstone (M : IndexM) (k : GoString) (rev : Rev) : Option IndexM :=
  match M k with
  | none => none
  | some ki => (kiTombstone ki rev).map fun ki' => fun k' => if k' = k then some ki' else M k'

/-- `treeIndex.Compact(rev)`: each key index compacted, the empty ones removed. -/
def idxCompact (M : IndexM) (rev : w64) : IndexM :=
  fun k => match M k with
    | none => none
    | some ki => let ki' := kiCompact ki rev; if kiIsEmpty ki' then none else some ki'

/-- The revisions `treeIndex.Compact(rev)` marks available. -/
def idxCompactAvail (M : IndexM) (rev : w64) (r : Rev) : Prop :=
  ∃ k ki, M k = some ki ∧ r ∈ (kiDoCompact ki rev).2.2

/-- The revisions `treeIndex.Keep(rev)` returns. -/
def idxKeep (M : IndexM) (rev : w64) (r : Rev) : Prop :=
  ∃ k ki, M k = some ki ∧ r ∈ kiKeep ki rev

/-- **`treeIndex.Range(key, end, atRev, limit, withTotalCount)`** (and `Revisions`,
`CountRevisions`): the keys of the range present at `atRev` in key order, with their revision,
creation revision and version (`l`), cut at a positive `limit`; the total: every one with
`withTotalCount`, else as many as returned. `end` `nil`: the key alone. -/
def idxRange (M : IndexM) (rg : MRange) (atRev : w64) (limit : Int) (withTotal : Bool)
    (out : List (GoString × Rev × Rev × w64)) (total : Nat) : Prop :=
  ∃ all : List (GoString × Rev × Rev × w64),
    all.Pairwise (fun a b => go.GoStringLt a.1 b.1) ∧
    (∀ x, x ∈ all ↔ rg.mem x.1 ∧ ∃ ki, M x.1 = some ki ∧ kiGet ki atRev = some x.2) ∧
    (if rg.endNil then out = all ∧ total = all.length
     else
      out = (if 0 < limit ∧ limit < all.length then all.take limit.toNat else all) ∧
      total = (if withTotal then all.length else out.length))

end pure

/-! ## Resources -/

/-- An index's ghost names (opaque). -/
opaque IdxName : Type := Unit

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- `p` is a `*keyIndex` of key `k` at the model `ki` (fraction `dq`; its key slice read-only). -/
opaque ownKi (p : Loc) (k : GoString) (ki : KeyIndexM) (dq : DFrac) : IProp GF := iprop(True)

/-- `p` points at a `generation` at `g` (fraction `dq`). -/
opaque ownGenAt (p : Loc) (g : Gen) (dq : DFrac) : IProp GF := iprop(True)

/-- `idx` is a tree index (persistent), its lock's invariant holding the tree. -/
opaque isTreeIndex (idx : GoInterface) (γi : IdxName) : IProp GF := iprop(True)

/-- **The index is `M`** (exclusive; the store's invariant holds it). -/
opaque idxModel (γi : IdxName) (M : IndexM) : IProp GF := iprop(True)

/-- A tree index `ti` no other goroutine reaches, its key indexes at the pointers `P` (exclusive). -/
opaque ownIdxPriv (ti : Loc) (P : GoString → Option (Loc × KeyIndexM)) : IProp GF := iprop(True)

/-- The tree's content, as its lock holder sees it (fraction `dq`). -/
opaque treeOwn (ti : Loc) (dq : DFrac) (M : IndexM) : IProp GF := iprop(True)

/-- `s` is the `*store` of `γ` (persistent). -/
opaque isStore (s : Loc) (γ : MvccName) : IProp GF := iprop(True)

/-- `s.mu` held for writing, with what it protects (exclusive). -/
opaque storeW (s : Loc) (γ : MvccName) : IProp GF := iprop(True)

/-- `s.mu` held for reading at the state `σ` (exclusive: a transaction's). -/
opaque storeR (s : Loc) (γ : MvccName) (σ : MvccState) : IProp GF := iprop(True)

/-- A `*storeTxnRead` at `t`, at `σ` (exclusive). -/
opaque storeTxnR (t : Loc) (γ : MvccName) (trace : Loc) (σ : MvccState) : IProp GF := iprop(True)

/-- A `*storeTxnWrite` at `t`, begun at `σ`, its events `pend` (exclusive). -/
opaque storeTxnW (t : Loc) (γ : MvccName) (trace : Loc) (σ : MvccState) (pend : List Event) :
    IProp GF := iprop(True)

/-- What a compaction job at `c` (the previous compaction `prev`) runs with (exclusive). -/
opaque compactJobRes (s : Loc) (γ : MvccName) (c prev : w64) : IProp GF := iprop(True)

/-- A `kvHasher` at `h` hashing the revisions `(c, r]` but the compaction's (`keep`). -/
opaque isHasher (h : Loc) (c r : w64) : IProp GF := iprop(True)

/-- `hs` is the `*hashStorage` of the store `s` (persistent). -/
opaque isHashStorageAt (hs : Loc) (s : Loc) (γ : MvccName) : IProp GF := iprop(True)

/-- A tree index's keys' pointers, read-only (the models of `P`). -/
def privModel (P : GoString → Option (Loc × KeyIndexM)) : IndexM := fun k => (P k).map Prod.snd

end vocab

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def internal_persistent.spec : Prop :=
  (∀ idx γi, Persistent (isTreeIndex (GF := GF) idx γi)) ∧ (∀ s γ, Persistent (isStore (GF := GF) s γ)) ∧
  (∀ hs s γ, Persistent (isHashStorageAt (GF := GF) hs s γ)) ∧
  (∀ p k ki, Persistent (ownKi (GF := GF) p k ki DFrac.discard))

/-- **Publish a private index**: its lock is free, so its invariant can be allocated. -/
def idxShare.spec : Prop :=
  ∀ (ti : Loc) P, ownIdxPriv (GF := GF) ti P ={⊤}=∗ ∃ γi,
    isTreeIndex (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti) γi ∗ idxModel γi (privModel P)

/-- A private index's key index, lent to its owner (`restoreIntoIndex` mutates it in place). -/
def ownIdxPriv_lookup.spec : Prop :=
  ∀ (ti : Loc) P k p ki, ⌜P k = some (p, ki)⌝ ∗ ownIdxPriv (GF := GF) ti P ⊢
    ownKi p k ki (DFrac.own 1) ∗
    (∀ ki', ownKi p k ki' (DFrac.own 1) -∗ ownIdxPriv ti (fun k' => if k' = k then some (p, ki') else P k'))

/-- The store's internal handle under the client's. -/
def isMvcc_store.spec : Prop :=
  ∀ (s : Loc) γ, isMvcc (GF := GF) (interface.mkOk (go.GoType.PointerType store.ty) #s) γ ⊢ isStore s γ

end laws

end Mvcc
end EtcdGrove
end Perennial
