/-
`b.DeleteBucket(key)` (`bucket.go`): deletes the nested bucket and everything in it.

**Users.** `Tx.DeleteBucket` (the root's: the backend's `UnsafeDeleteBucket`, `batch_tx.go:148`,
which accepts `ErrBucketNotFound` by `errors.Is` and is fatal on any other error). Snippets:
`ReqDeleteBucketNotFound`, `ReqNested`.

**Proof sketch.** Not writable: `ErrTxNotWritable`; `seek`; not the key: `ErrBucketNotFound`; a
value: `ErrIncompatibleValue` (also the empty name in an empty bucket: `seek` returns a nil key,
which `bytes.Equal` matches); else open the child, delete its nested buckets recursively
(`ForEachBucket`), drop it from the child cache, free its pages (`Bucket.free`: 4d's
`freelist.Free` of each page as pending for this txid; the inline bucket none,
`issues/bbolt-deletebucket-nested-leak.md` is a page-accounting leak, not a data one), `node.del`.
The generation of `p.child key` is bumped: its handles, and its descendants', are stale.

**Changes.** Over paths; the read transaction's error; the empty-name case exactly (was a
disjunction).
**Proof sketch, the success arm in the internal vocabulary** (verify-round, A11 F9). `seek`
(a bucket); `Bucket.Bucket` (the child's handle, cached: `C.bkts child = some (p.child kb)`); the
recursion, each nested bucket's `DeleteBucket` (its post `T'.dropBkt (p.child kb) k'`; the nested
handles dropped), through `Bucket.ForEachBucket.spec_del` (re-review N2: the loop's view is any
`T.sameAt T' (p.child kb)`, `I i T'`: the names `ks` from `i` on are still buckets at `T'`, so
every callback succeeds; Go may skip some, etcd-io/bbolt#1305, which the view does not see: the
whole child goes at `node.del`, and `dropBkt` of `T'` is `dropBkt` of `T`); then, in the body, `delete(b.buckets, key)`, `child.nodes = nil`,
`child.rootNode = nil`: a realization step of `wtxCore` (the child and everything below it no
longer cached: `bktDropped C (p.child kb)`; the cache then represents the view whose child is what
its parent's stored value holds); `Bucket.free` (its premise `C.bkts child = none`; `repKept`);
`Cursor.node` (`keyLeaf`); `node.del`; `physRep_delBkt` gives `physRep` of that view's `dropBkt p kb`,
which is `T.dropBkt p kb` (the child is removed either way, and `dropBkt` resets the generations
below `p.child kb`, so the recursion's bumps there are forgotten: `TxView.dropBkt`'s
verify-round change).
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.DeleteBucket(key)`: on a write transaction (all of it), deletes the bucket `key` of the
bucket at `p` with its contents (its handles are no longer current); errors: not writable, no such
key (`ErrBucketNotFound`), `key` holds a value or is the empty name in an empty bucket
(`ErrIncompatibleValue`). -/
def Bucket.DeleteBucket.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (gs : List Nat) (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ bktH tx γ b p gs ∗ key ↦*{dk} kb ∗ ⌜T.gens p = gs ∧ (T.rw = true → q = 1)⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"DeleteBucket")) (Val #key))
  {{ (err : GoInterface), RET #err; key ↦*{dk} kb ∗
      (if T.rw = false then
         iprop(boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrTxNotWritable err)
       else match T.cur.atPath (p.child kb) with
         | some (Ent.bkt _ _) => iprop(⌜err = GoInterface.nil⌝ ∗ boltTx tx γ q (T.dropBkt p kb))
         | some (Ent.val _) => iprop(boltTx tx γ q T ∗
             isErr go_etcd_io.bbolt.errors.ErrIncompatibleValue err)
         | none =>
           if kb.length = 0 ∧ T.ents p = [] then
             iprop(boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrIncompatibleValue err)
           else iprop(boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrBucketNotFound err)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
