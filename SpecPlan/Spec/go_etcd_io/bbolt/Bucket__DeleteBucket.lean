/-
`b.DeleteBucket(key)` (`bucket.go`): deletes the nested bucket and everything in it.

**Users.** `Tx.DeleteBucket` (the root's: the backend's `UnsafeDeleteBucket`, `batch_tx.go:148`,
which accepts `ErrBucketNotFound` by `errors.Is` and is fatal on any other error). Snippets:
`ReqDeleteBucketNotFound`, `ReqNested`.

**Proof sketch.** Not writable: `ErrTxNotWritable`; `seek`; not the key: `ErrBucketNotFound`; a
value: `ErrIncompatibleValue`; the empty name (no entry has it) gives either error: `seek("")`
ends at the first leaf, whose first key, or nil if the transaction emptied that leaf, `bytes.Equal`
compares with `""` (`nonissues/bbolt-deletebucket-empty-name/`); else open the child, delete its nested buckets recursively
(`ForEachBucket`), drop it from the child cache, free its pages (`Bucket.free`: 4d's
`freelist.Free` of each page as pending for this txid; the inline bucket none,
`issues/bbolt-deletebucket-nested-leak.md` is a page-accounting leak, not a data one), `node.del`.
The tokens of `p.child key` and of every bucket below it are consumed: no handle of them survives.

**Changes.** Over paths; the read transaction's error; the empty-name case exactly (was a
disjunction).
**Proof sketch, the success arm in the internal vocabulary** (verify-round, A11 F9). `seek`
(a bucket); `Bucket.Bucket` with the child's whole token (the child's handle, cached:
`C.bkts child = some (p.child kb)`); the recursion, each nested bucket's `DeleteBucket` with the
tokens of its subtree, carried by the loop's `I` (its post `T'.dropBkt (p.child kb) k'`; the nested
tokens consumed), through `Bucket.ForEachBucket.spec_del` (re-review N2: the loop's view is any
`T.sameAt T' (p.child kb)`, `I i T'`: the names `ks` from `i` on are still buckets at `T'`, so
every callback succeeds; Go may skip some, etcd-io/bbolt#1305, which the view does not see: the
whole child goes at `node.del`, and `dropBkt` of `T'` is `dropBkt` of `T`); then, in the body, `delete(b.buckets, key)`, `child.nodes = nil`,
`child.rootNode = nil`: a realization step of `wtxCore` (the child and everything below it no
longer cached: `bktDropped C (p.child kb)`, the child's token consumed with its ghost entry; the
cache then represents the view whose child is what its parent's stored value holds); `Bucket.free` (its premise `C.bkts child = none`; `repKept`);
`Cursor.node` (`keyLeaf`); `node.del`; `physRep_delBkt` gives `physRep` of that view's `dropBkt p kb`,
which is `T.dropBkt p kb` (the child is removed either way).
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** The parent's handle premise
`bktUse` in place of `bktH … gs` and the generation check, given back; a write transaction gives up
the whole tokens of the deleted bucket and of every bucket below it (`Ent.bktsUnder`); `dropBkt`
only changes the data. The empty name gives either error, the transaction unchanged (was:
`ErrIncompatibleValue` only in an empty bucket, false once the transaction empties the first leaf;
the ledger's second 2026-11-12 entry) (the per-path generation counter it replaces was unobservable
state, redundant with ownership).
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
bucket at `p` with its contents (its tokens, and those of every bucket below it, consumed); errors:
not writable, no such key (`ErrBucketNotFound`), `key` holds a value (`ErrIncompatibleValue`), the
empty name (either). The error arms lose no token: `bktsUnder` is empty on each, by definition for
no such key and a value, and for the empty name because well-formed data has no empty key
(`boltTx_wf`); a read transaction gives none. -/
def Bucket.DeleteBucket.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (qb : Qp) (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ bktUse tx γ T.rw b p qb ∗ key ↦*{dk} kb ∗ ⌜T.rw = true → q = 1⌝ ∗
      (if T.rw then iprop([∗list] d ∈ T.cur.bktsUnder (p.child kb), ∃ o, bktOwn tx γ d o 1)
       else iprop(emp)) }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"DeleteBucket")) (Val #key))
  {{ (err : GoInterface), RET #err; bktUse tx γ T.rw b p qb ∗ key ↦*{dk} kb ∗
      (if T.rw = false then
         iprop(boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrTxNotWritable err)
       else if kb.length = 0 then
         iprop(boltTx tx γ q T ∗ (isErr go_etcd_io.bbolt.errors.ErrBucketNotFound err ∨
           isErr go_etcd_io.bbolt.errors.ErrIncompatibleValue err))
       else match T.cur.atPath (p.child kb) with
         | some (Ent.bkt _ _) => iprop(⌜err = GoInterface.nil⌝ ∗ boltTx tx γ q (T.dropBkt p kb))
         | some (Ent.val _) => iprop(boltTx tx γ q T ∗
             isErr go_etcd_io.bbolt.errors.ErrIncompatibleValue err)
         | none => iprop(boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrBucketNotFound err)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
