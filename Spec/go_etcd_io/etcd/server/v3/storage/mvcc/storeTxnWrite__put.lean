/-
`(*storeTxnWrite).put(key, value, leaseID)` (`kvstore_txn.go:223`): the put's event appended.
Internal (`Put`).

**Proof sketch**: `treeIndex.Get.spec` at `beginRev + 1` (the key's create revision and version in
the store the transaction sees, `txnStore σ pend`; absent: `R`, `0`); if present, the lessor's
`GetLease` (the lessor state's item of the key); `proto.Marshal` of the
record `putRec R prev v l` (2a's boundary: marshalable, a fresh encoding); `UnsafeSeqPut(Key,
revBytes ⟨R, |pend|⟩, d)` on the batch (`kbLocked`); `treeIndex.Put.spec` (the index's key index
gets the revision: above its `modified`, the transaction being the only writer); the record
appended to `changes`; then the lease (`putLs`): unchanged, or `Detach` of the old one (an error
only logged) and `Attach` of the new one (live: the premise; `Attach` panics on an error). The trace
steps.

**Changes** from `specs-ref`'s file: over `storeTxnW`, W0's records and the lessor's state
(`Lease.lessorState`, `putLs`).
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

/-- The put's event (`putEv`) appended; the lessor moved by `putLs`. -/
def storeTxnWrite.put.spec : Prop :=
  ∀ (t : Loc) (γ : MvccName) (γl : Lease.Names) (trace : Loc) (σ : MvccState) (pend : List Event)
    (key value : GoSlice) (kk vv : Bytes) (lid : w64) (n : Nat) (ls : Lease.LessorState),
  let ev := putEv σ pend kk vv (sint.Z lid)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      storeTxnW t γ trace σ pend ∗ mvccLessorIs γ γl ∗ traceOwn trace ∗ key ↦*□ kk ∗ value ↦*□ vv ∗
      Lease.lessorState γl n ls ∗ ⌜sint.Z lid = 0 ∨ ls.leases (sint.Z lid) ≠ none⌝ }}
    (App (App (App (Val (t @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"put")) (Val #key))
      (Val #value)) (Val #lid))
  {{ RET #(); storeTxnW t γ trace σ (pend ++ [ev]) ∗ traceOwn trace ∗
      ∃ n' : Nat, Lease.lessorState γl n' (putLs ls (txnStore σ pend kk).isSome kk (sint.Z lid)) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
