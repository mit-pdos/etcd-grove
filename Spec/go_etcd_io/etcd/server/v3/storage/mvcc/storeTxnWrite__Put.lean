/-
`(*storeTxnWrite).Put(key, value, lease)` (`kvstore_txn.go:204`): `put`, then `beginRev + 1`.
Internal (`Txn.Put.contract` through `metricsTxnWrite.Put`, 3f's `watchableStoreTxnWrite`). Proof
sketch: `put.spec`.

**Changes** from `specs-ref`'s file: over `storeTxnW`, W0's records and `Lease.lessorState`.
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

/-- `put`'s, returning the revision written. -/
def storeTxnWrite.Put.spec : Prop :=
  ∀ (t : Loc) (γ : MvccName) (γl : Lease.Names) (trace : Loc) (σ : MvccState) (pend : List Event)
    (key value : GoSlice) (kk vv : Bytes) (lid : w64) (n : Nat) (ls : Lease.LessorState),
  let ev := putEv σ pend kk vv (sint.Z lid)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      storeTxnW t γ trace σ pend ∗ mvccLessorIs γ γl ∗ traceOwn trace ∗ key ↦*□ kk ∗ value ↦*□ vv ∗
      Lease.lessorState γl n ls ∗ ⌜sint.Z lid = 0 ∨ ls.leases (sint.Z lid) ≠ none⌝ }}
    (App (App (App (Val (t @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"Put")) (Val #key))
      (Val #value)) (Val #lid))
  {{ RET #(W64 (σ.rev + 1) : w64); storeTxnW t γ trace σ (pend ++ [ev]) ∗ traceOwn trace ∗
      ∃ n' : Nat, Lease.lessorState γl n' (putLs ls (txnStore σ pend kk).isSome kk (sint.Z lid)) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
