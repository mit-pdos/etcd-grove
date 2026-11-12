/-
# mvcc's index internals (batch 3e): what the index's specs add to `Internal.lean`

* `idxN`: the index's invariant namespace (inside `mvccN`; the store's invariant lives elsewhere in
  `mvccN`, so a store's update can be fired inside the index's atomic step).
* `idxAt γi M c` (exclusive, the store's invariant holds it): **the index is `M`, compacted at the
  floor `c`**. `M` is the *logical* index (every put and tombstone since the index was published);
  the tree itself is `M` with its key indexes compacted at revisions up to `c` (and the emptied ones
  removed), which answers every query at a revision at least `c` as `M` does. This replaces
  `Internal.lean`'s `idxModel γi M`, which cannot be the index's linearizable state: `Compact`
  compacts key by key, each under the tree lock, so a reader between two keys sees a tree that is
  neither `M` nor `idxCompact M rev`; it answers as both at revisions `≥ rev`, which is all a
  reader asks once the store has raised its compaction revision (readers check it under `s.mu`).
  `idxShareC` publishes a private index at it.
* `idxEnts M key e l`: the key indexes of `M` from `key` (below `e` when `e` is non-empty), in key
  order (`unsafeVisit`'s traversal).
* `idxNonEmpty M`: every key index of `M` is non-empty and well formed (the tree's invariant: a put
  makes a key index non-empty, `Compact` removes the emptied ones).
* `availAt m A` (exclusive): the Go map `m` (`map[Revision]struct{}`) holds exactly the revisions
  `A` (`compact`, `keep`, `doCompact` write it; `Compact`/`Keep` return it).
* `keepAvail A ki atRev`: `keyIndex.keep`'s effect on `available` (`doCompact`'s addition, deleted
  again for a generation-ending tombstone that is not the last generation's).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel
open go_etcd_io.etcd.server.v3.storage.mvcc
open Classical

/-- The index's invariant namespace. -/
def idxN : Namespace := mvccN .@ "idx"

section pure
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- `unsafeVisit(key, end, …)`'s traversal: `M`'s key indexes from `key`, below `e` when `e` is
non-empty, in key order. -/
def idxEnts (M : IndexM) (key e : GoString) (l : List (GoString × KeyIndexM)) : Prop :=
  l.Pairwise (fun a b => go.GoStringLt a.1 b.1) ∧
  ∀ x, x ∈ l ↔ (go.GoStringLe key x.1 ∧ (e = [] ∨ go.GoStringLt x.1 e) ∧ M x.1 = some x.2)

/-- Every key index non-empty and well formed. -/
def idxNonEmpty (M : IndexM) : Prop := ∀ k ki, M k = some ki → kiIsEmpty ki = false ∧ kiWf ki

/-- The answer of `treeIndex.Get`/`unsafeGet`. -/
def idxGetRes (M : IndexM) (k : GoString) (atRev : w64) : Option (Rev × Rev × w64) :=
  (M k).bind fun ki => kiGet ki atRev

/-- The result values of a get: the revisions and version, or zeros and the error `e`. -/
def getVal (res : Option (Rev × Rev × w64)) (e : GoInterface) : val :=
  match res with
  | some (m, c, v) => PairV (PairV (PairV #(revVal m) #(revVal c)) #v) #(GoInterface.nil)
  | none => PairV (PairV (PairV #(revVal Rev.zero) #(revVal Rev.zero)) #(W64 0)) #e

/-- `keyIndex.doCompact`/`compact`'s effect on `available`: its revision added. -/
def compactAvail (A : Rev → Prop) (ki : KeyIndexM) (atRev : w64) : Rev → Prop :=
  fun r => A r ∨ r ∈ (kiDoCompact ki atRev).2.2

/-- `keyIndex.keep`'s effect on `available`: nothing for an empty key index; else `doCompact`'s
revision added, then deleted again when it ends a generation that is not the last (Go's `delete`
removes it even if it was there before). -/
def keepAvail (A : Rev → Prop) (ki : KeyIndexM) (atRev : w64) : Rev → Prop :=
  if kiIsEmpty ki then A
  else
    let (gi, n, av) := kiDoCompact ki atRev
    let g := ki.gens.getD gi Gen.empty
    if g.revs ≠ [] ∧ n = ((g.revs.length - 1 : Nat) : Int) ∧ gi ≠ ki.gens.length - 1
    then fun r => (A r ∨ r ∈ av) ∧ r ∉ av
    else fun r => A r ∨ r ∈ av

/-- `BucketKeyToBytes`'s bytes over a 17- or 18-byte slice whose bytes past the 17th are `rest`. -/
def bucketKeyBytes (r : Rev) (tomb : Bool) (rest : List w8) : List w8 :=
  revBytes r false ++ (if tomb then [W8 116] else rest)

end pure

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The index is `M`, compacted at the floor `c`** (exclusive; see the header). -/
opaque idxAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γi : IdxName) (M : IndexM) (c : Int) : IProp GF := iprop(True)

/-- The Go map `m` holds exactly the revisions `A` (exclusive). -/
opaque availAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (m : Loc) (A : Rev → Prop) : IProp GF := iprop(True)

end vocab

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def idxAt_timeless.spec : Prop := ∀ γi M c, Timeless (idxAt (GF := GF) γi M c)

def idxAt_excl.spec : Prop := ∀ γi M M' c c',
  idxAt (GF := GF) γi M c ∗ idxAt γi M' c' ⊢ iprop(False)

/-- The index's key indexes are non-empty and well formed. -/
def idxAt_wf.spec : Prop := ∀ γi M c, idxAt (GF := GF) γi M c ⊢ ⌜idxNonEmpty M⌝

/-- **Publish a private index** (in place of `idxShare`): its lock is free, so its invariant can be
allocated; its key indexes non-empty and well formed (as `restoreIntoIndex` builds them). -/
def idxShareC.spec : Prop :=
  ∀ (ti : Loc) P, ⌜idxNonEmpty (privModel P)⌝ ∗ ownIdxPriv (GF := GF) ti P ={⊤}=∗ ∃ γi,
    isTreeIndex (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti) γi ∗
    idxAt γi (privModel P) 0

end laws

end Mvcc
end EtcdGrove
end Perennial
