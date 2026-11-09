/-
`(*storeTxnWrite).delete(key)` (`kvstore_txn.go:308`): a tombstone for a key present in the store
the transaction sees. Internal (`deleteRange`, which calls it for each key the index finds).

**Proof sketch**: `BucketKeyToBytes` of `⟨R, |pend|⟩` with the tombstone mark; `proto.Marshal` of
`KeyValue{Key: key}`; `UnsafeSeqPut(Key, …)` on the batch; `treeIndex.Tombstone.spec`: the key's
last generation is not empty (the key is present: the premise), so no `ErrRevisionNotFound` and no
`lg.Fatal`; the record appended; the lessor's `GetLease` (`storeItems`' value) and, if a lease,
`Detach` (live: 3c's law; an error would only be logged).

**Changes** from `specs-ref`'s file: over `storeTxnW`, W0's events and 3c's writer token (`delLs`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalTxn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The delete's event appended (the key present: `lg.Fatal` otherwise). -/
def storeTxnWrite.delete.spec : Prop :=
  ∀ (t : Loc) (γ : MvccName) (γl : Lease.Names) (trace : Loc) (σ : MvccState) (pend : List Event)
    (key : GoSlice) (kk : Bytes) (n : Nat) (ls : Lease.LessorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      storeTxnW t γ trace σ pend ∗ mvccLessorIs γ γl ∗ key ↦*□ kk ∗
      ⌜(txnStore σ pend kk).isSome⌝ ∗ Lease.lessorState γl n ls }}
    (App (Val (t @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"delete")) (Val #key))
  {{ RET #(); storeTxnW t γ trace σ (pend ++ [.delete kk]) ∗
      ∃ n' : Nat, Lease.lessorState γl n' (delLs ls kk) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
