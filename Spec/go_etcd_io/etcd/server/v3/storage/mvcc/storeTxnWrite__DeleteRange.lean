/-
`(*storeTxnWrite).DeleteRange(key, end)` (`kvstore_txn.go:197`): `deleteRange`; its number and
`beginRev + 1` if the transaction now has a change, else `0` and `beginRev`. Internal
(`Txn.DeleteRange.contract` through `metricsTxnWrite`, 3f's `watchableStoreTxnWrite`, the lessor's
`Revoke` through the range deleter).

**Changes** from `specs-ref`'s file: over `storeTxnW`, `rangeKeys` (W0's store) and the lessor's state (`delsLs`).
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

/-- The deletes appended; their number and the revision written. -/
def storeTxnWrite.DeleteRange.spec : Prop :=
  ∀ (t : Loc) (γ : MvccName) (γl : Lease.Names) (trace : Loc) (σ : MvccState) (pend : List Event)
    (key endk : GoSlice) (kk e : Bytes) (dk de : DFrac) (n : Nat) (ls : Lease.LessorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      storeTxnW t γ trace σ pend ∗ mvccLessorIs γ γl ∗ key ↦*{dk} kk ∗ endk ↦*{de} e ∗
      Lease.lessorState γl n ls }}
    (App (App (Val (t @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"DeleteRange")) (Val #key))
      (Val #endk))
  {{ (nd rev : w64), RET (PairV #nd #rev); key ↦*{dk} kk ∗ endk ↦*{de} e ∗
      ∃ (ds : List Key) (n' : Nat),
      ⌜rangeKeys (txnStore σ pend) (mrange kk endk e) ds⌝ ∗
      storeTxnW t γ trace σ (pend ++ ds.map .delete) ∗
      Lease.lessorState γl n' (delsLs ls ds) ∗
      ⌜nd = W64 ds.length ∧ rev = W64 (if pend ++ ds.map .delete = [] then σ.rev else σ.rev + 1)⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
