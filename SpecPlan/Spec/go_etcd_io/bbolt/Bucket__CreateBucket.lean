/-
`b.CreateBucket(key)` (`bucket.go`): a new empty nested bucket (inline until it grows).

**Users.** `Tx.CreateBucket` (the root's: the bank, `bbolttest.go:236`), nested-bucket clients.
Snippets: `ReqBank`, `ReqNested`.

**Proof sketch.** Checks (not writable, empty name); `seek`; an existing key: `ErrBucketExists` (a
bucket) or `ErrIncompatibleValue`; else `bucket.write()` of an empty inline bucket (`Bucket.write.spec`
with `fresh`: the local is `emptyBkt`; 4d's `encInBucket` of a zero header, then `nodePage` of
`NodeR.emptyLeaf`: a leaf page of no element), `node.put` with the bucket flag, then `Bucket.Bucket.spec`.

**Changes.** New for nested buckets; the root's old spec took a write transaction (now: the read
transaction's error). Kept: names within `maxKeySize` (Go checks no length,
`nonissues/bbolt-bucket-name-length-unchecked.md`; the page bound needs it: a scope restriction).
**Proof sketch, the success arm in the internal vocabulary** (verify-round, A11 F9). `seek`
(absent), `Bucket.write` of the fresh local (`emptyBktVal`), `Cursor.node` (`repKept`,
`keyLeaf`), `node.put kb kb emptyBktVal 0 BucketLeafFlag`, `physRep_set` with `newEnt`'s bucket
case (`kb.length ≤ maxKeySize`: the premise); then `Bucket.Bucket` opens the child from that value and
caches it (no handle was cached at the absent key: `DeleteBucket` removes the entry), the new
token's ghost entry allocated at `some c` with the map write (`wtxCore_bktOwn`).
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** The parent's handle premise
`bktUse` in place of `bktH … gs` and the generation check, given back; the new bucket's whole token
`bktOwn … (some c) 1` in place of its `bktH` (the per-path generation counter it replaces was
unobservable state, redundant with ownership).
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

/-- `b.CreateBucket(key)`: on a write transaction (all of it), a new empty bucket `key` in the
bucket at `p`, and its handle; errors: not writable, empty name, the key exists (a bucket:
`ErrBucketExists`; a value: `ErrIncompatibleValue`). -/
def Bucket.CreateBucket.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (qb : Qp) (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ bktUse tx γ T.rw b p qb ∗ key ↦*{dk} kb ∗
      ⌜(T.rw = true → q = 1) ∧ kb.length ≤ maxKeySize⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"CreateBucket")) (Val #key))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err); bktUse tx γ T.rw b p qb ∗ key ↦*{dk} kb ∗
      (if T.rw = false then
         iprop(⌜c = Loc.null⌝ ∗ boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrTxNotWritable err)
       else if kb.length = 0 then
         iprop(⌜c = Loc.null⌝ ∗ boltTx tx γ q T ∗
           isErr go_etcd_io.bbolt.errors.ErrBucketNameRequired err)
       else match T.cur.atPath (p.child kb) with
         | some (Ent.bkt _ _) => iprop(⌜c = Loc.null⌝ ∗ boltTx tx γ q T ∗
             isErr go_etcd_io.bbolt.errors.ErrBucketExists err)
         | some (Ent.val _) => iprop(⌜c = Loc.null⌝ ∗ boltTx tx γ q T ∗
             isErr go_etcd_io.bbolt.errors.ErrIncompatibleValue err)
         | none => iprop(⌜err = GoInterface.nil ∧ c ≠ Loc.null⌝ ∗
             boltTx tx γ q (T.setCur (T.cur.modAt p (fun e => e.setKey kb (some (Ent.bkt (W64 0) []))))) ∗
             bktOwn tx γ (p.child kb) (some c) 1)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
