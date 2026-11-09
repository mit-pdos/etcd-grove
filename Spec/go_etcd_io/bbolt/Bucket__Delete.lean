/-
`b.Delete(key)` (`bucket.go`).

**Users.** The backend's `UnsafeDelete` (`batch_tx.go:238`; a failure is fatal), also of a key
this very transaction returned (mvcc's compaction deletes the keys its range returned,
`kvstore_compaction.go:58-71`: the key's points-to is then read against a share of `txLive`, not
of `boltTx`, so all of `boltTx` is still the caller's: integration Y, I6's request). Snippets:
`ReqBackendBatch`, `ReqReadOnlyPut`.

**Proof sketch.** Not writable: `ErrTxNotWritable`; `seek`; absent: nil, no change; a nested
bucket's key: `ErrIncompatibleValue`; else `node.del` on the materialized leaf (all of the
transaction).

**Changes.** Over paths; read transactions' error; `ErrIncompatibleValue`.
-/
module

public import Spec.go_etcd_io.bbolt.Api

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

/-- `b.Delete(key)`: on a write transaction (all of it), removes `key` from the bucket at `p` (no
change if absent); errors: not writable, `key` is a nested bucket. -/
def Bucket.Delete.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (gs : List Nat) (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ bktH tx γ b p gs ∗ key ↦*{dk} kb ∗ ⌜T.gens p = gs ∧ (T.rw = true → q = 1)⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Delete")) (Val #key))
  {{ (err : GoInterface), RET #err; key ↦*{dk} kb ∗
      (if T.rw = false then
         iprop(boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrTxNotWritable err)
       else if (T.cur.atPath (p.child kb)).any Ent.isBkt then
         iprop(boltTx tx γ q T ∗ isErr go_etcd_io.bbolt.errors.ErrIncompatibleValue err)
       else iprop(⌜err = GoInterface.nil⌝ ∗
         boltTx tx γ q (T.setCur (T.cur.modAt p (fun e => e.setKey kb none))))) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
