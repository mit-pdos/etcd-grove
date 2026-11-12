/-
`tx.DeleteBucket(name)` (`tx.go`): the root's.

**Users.** The backend's `UnsafeDeleteBucket` (`batch_tx.go:148`: `errors.Is(err,
ErrBucketNotFound)` is accepted, any other error fatal). Snippet: `ReqDeleteBucketNotFound`.
**Proof sketch.** `Bucket.DeleteBucket.spec` at the root. **Changes.** As
`Bucket.DeleteBucket.spec`.
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** A write transaction gives up
the whole tokens of the deleted bucket and of every bucket below it (`Ent.bktsUnder`); the empty
name gives either error, the transaction unchanged (the ledger's second 2026-11-12 entry); as
`Bucket.DeleteBucket.spec` (the per-path generation counter it replaces was unobservable state,
redundant with ownership).
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

/-- `tx.DeleteBucket(name)`: deletes the top-level bucket `name` (see `Bucket.DeleteBucket.spec`).
The error arms lose no token: `bktsUnder` is empty on each, by definition for no such key and a
value, and for the empty name because well-formed data has no empty key (`boltTx_wf`). -/
def Tx.DeleteBucket.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ key ↦*{dk} kb ∗ ⌜T.rw = true → q = 1⌝ ∗
      (if T.rw then iprop([∗list] d ∈ T.cur.bktsUnder [kb], ∃ o, bktOwn tx γ d o 1)
       else iprop(emp)) }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"DeleteBucket")) (Val #key))
  {{ (err : GoInterface), RET #err; key ↦*{dk} kb ∗
      (if T.rw = false then
         iprop(boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrTxNotWritable err)
       else if kb.length = 0 then
         iprop(boltTx tx γ q T ∗ (isErr go_etcd_io.bbolt.errors.ErrBucketNotFound err ∨
           isErr go_etcd_io.bbolt.errors.ErrIncompatibleValue err))
       else match T.cur.atPath [kb] with
         | some (Ent.bkt _ _) => iprop(⌜err = GoInterface.nil⌝ ∗ boltTx tx γ q (T.dropBkt [] kb))
         | some (Ent.val _) => iprop(boltTx tx γ q T ∗
             isErr go_etcd_io.bbolt.errors.ErrIncompatibleValue err)
         | none => iprop(boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrBucketNotFound err)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
