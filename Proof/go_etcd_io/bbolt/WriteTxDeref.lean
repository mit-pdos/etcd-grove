/-
A write transaction's objects across a remap (pure).

`Tx.allocate` may grow the file past the mapping; `db.mmap` then calls the writer's
`root.dereference()` (before unmapping), which copies the key and value bytes of the nodes it
reaches (each bucket's node tree, from the top of its root node's parent chain down the
children lists, and the buckets in the bucket caches) to the heap.

- `derefReady T rl`: what `dereference` of the root bucket `rl` needs: every bucket
  reachable from it through the bucket caches; in each bucket, the root node's parent chain ends
  (`topOf`), the children lists below the top form a tree (`kidsTree`: each node listed once),
  each node of it holds its entries' bytes (`derefOK`); each cached child bucket is one of the
  transaction's.
- `derefRel T T'`: what it does: the same buckets and their structs; the nodes of the trees
  kept, their entries the same bytes, now heap copies (`ownFresh`), the other nodes dropped
  (they are no longer used: spilled nodes no tree reaches); an inline page in the view becomes
  stale. Then nothing refers to the view (`noView`), and the transaction stands over a view at
  another location.
- `freshPage id count ps`: what `Tx.allocate(count)` returns: `count` zeroed pages but for the
  header's `id` and `overflow` (`make`, or the page pool, whose buffers `Tx.write` zeroes).
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section deref
variable [ext : FfiSyntax]

/-- The nodes `S` are the tree of children lists from `l`, each listed once. -/
inductive kidsTree (ns : GMap Loc NRec) : Loc → List Loc → Prop
  | mk (l : Loc) (r : NRec) (subs : List (List Loc)) :
      ns !! l = some r → List.Forall₂ (kidsTree ns) r.cs subs → (l :: subs.flatten).Nodup →
      kidsTree ns l (l :: subs.flatten)

/-- `t` is the last node of the parent chain from `l` (`node.root`). -/
inductive topOf (ns : GMap Loc NRec) : Loc → Loc → Prop
  | self (l : Loc) (r : NRec) : ns !! l = some r → r.nv.parent' = null → topOf ns l l
  | up (l : Loc) (r : NRec) (t : Loc) : ns !! l = some r → r.nv.parent' ≠ null →
      topOf ns r.nv.parent' t → topOf ns l t

/-- The node (record `r`) of the bucket `bl` holds what `node.dereference` needs (`derefPre`). -/
def derefOK (bl : Loc) (r : NRec) : Prop :=
  r.nv.bucket' = bl ∧ r.ins.length = r.ws.length ∧
  (∀ w ∈ r.ws, w.ks ≠ Src.stale ∧ w.vs ≠ Src.stale ∧ 0 < w.key.length) ∧
  (r.nv.key' = slice.nil ∨ (r.ksrc ≠ Src.stale ∧ (r.nv.pgid' = W64 0 ∨ 0 < r.key.length)))

/-- The live nodes of the bucket `B`: those of its root node's tree. -/
def liveNodes (B : BRec) (S : List Loc) : Prop :=
  ∃ top, topOf B.ns B.bv.rootNode' top ∧ kidsTree B.ns top S

/-- The bucket `bl` is the bucket `rl` or cached under one reachable from it. -/
inductive bktReach (T : WTx) (rl : Loc) : Loc → Prop
  | root : bktReach T rl rl
  | child (bl : Loc) (B : BRec) (name : GoString) (c : Loc) : bktReach T rl bl →
      T.bs !! bl = some B → B.bm !! name = some c → bktReach T rl c

/-- What `dereference` of the root bucket `rl` needs (see the module doc): every bucket is
reachable from it. -/
def derefReady (T : WTx) (rl : Loc) : Prop :=
  (∀ bl, (T.bs !! bl).isSome → bktReach T rl bl) ∧
  ∀ bl B, T.bs !! bl = some B →
    (B.bv.rootNode' = null ∨ ∃ S, liveNodes B S ∧ ∀ l ∈ S, ∃ r, B.ns !! l = some r ∧ derefOK bl r) ∧
    ∀ name c, B.bm !! name = some c → (T.bs !! c).isSome

/-- An entry whose bytes are heap copies. -/
def ownFresh (w : WEntry) : WEntry := { w with ks := Src.own (DFrac.own 1), vs := Src.own (DFrac.own 1) }

/-- The node `r'` is `r` dereferenced (see the module doc). -/
def derefNode (r r' : NRec) : Prop :=
  r'.nv = { r.nv with inodes' := r'.nv.inodes', key' := r'.nv.key' } ∧ r'.ws = r.ws.map ownFresh ∧
  r'.cs = r.cs ∧ r'.key = r.key ∧ (r.nv.key' = slice.nil ↔ r'.nv.key' = slice.nil) ∧
  r'.ksrc = Src.own (DFrac.own 1)

/-- An inline page in the view is stale after a remap. -/
def staleOf : Src → Src
  | .view => Src.stale
  | s => s

/-- The bucket `B'` is `B` dereferenced. -/
def derefBkt (B B' : BRec) : Prop :=
  B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.nm = B.nm ∧ B'.bm = B.bm ∧ B'.ipg = B.ipg ∧
  B'.isrc = staleOf B.isrc ∧
  (∀ l r', B'.ns !! l = some r' → ∃ r, B.ns !! l = some r ∧ derefNode r r') ∧
  (B.bv.rootNode' ≠ null → ∀ S, liveNodes B S → ∀ l ∈ S, (B'.ns !! l).isSome)

/-- `T'` is `T` dereferenced (its `NodeDeref` statistic grown). -/
def derefRel (T T' : WTx) : Prop :=
  T'.t = { T.t with stats' := T'.t.stats' } ∧ T'.mv = T.mv ∧ T'.pm = T.pm ∧ T'.bufs = T.bufs ∧
  (∀ bl, (T.bs !! bl).isSome ↔ (T'.bs !! bl).isSome) ∧
  ∀ bl B B', T.bs !! bl = some B → T'.bs !! bl = some B' → derefBkt B B'

/-- No byte the transaction keeps is in the view. -/
def noView (T : WTx) : Prop :=
  ∀ bl B, T.bs !! bl = some B → B.isrc ≠ Src.view ∧
    ∀ l r, B.ns !! l = some r → (∀ w ∈ r.ws, w.ks ≠ Src.view ∧ w.vs ≠ Src.view) ∧
      r.ksrc ≠ Src.view

/-- `count` pages of `ps` bytes, zero but for the header's `id` and `overflow` (`count - 1`). -/
def freshPage (id : w64) (count ps : Nat) : List w8 :=
  leBytes 8 (uint.Z id) ++ leBytes 4 0 ++ leBytes 4 (((count - 1 : Nat) : Int)) ++
    List.replicate (count * ps - 16) 0

end deref

end bbolt
end EtcdGrove
end Perennial
