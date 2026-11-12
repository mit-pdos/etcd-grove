/-
`(*storeTxnWrite).deleteRange(key, end)` (`kvstore_txn.go:293`): the range's present keys (the
index at the transaction's revision, `treeIndex.Range.spec`) each deleted (`delete.spec`, in key
order); their number. Internal (`DeleteRange`).

**Changes** from `specs-ref`'s file: over `storeTxnW`, `rangeKeys` (W0's store) and the lessor's state (`delsLs`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalTxn

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

/-- The deletes of the range's present keys appended; their number. -/
def storeTxnWrite.deleteRange.spec : Prop :=
  ∀ (t : Loc) (γ : MvccName) (γl : Lease.Names) (trace : Loc) (σ : MvccState) (pend : List Event)
    (key endk : GoSlice) (kk e : Bytes) (dk de : DFrac) (n : Nat) (ls : Lease.LessorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      storeTxnW t γ trace σ pend ∗ mvccLessorIs γ γl ∗ key ↦*{dk} kk ∗ endk ↦*{de} e ∗
      Lease.lessorState γl n ls }}
    (App (App (Val (t @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"deleteRange")) (Val #key))
      (Val #endk))
  {{ (nd : w64), RET #nd; key ↦*{dk} kk ∗ endk ↦*{de} e ∗ ∃ (ds : List Key) (n' : Nat),
      ⌜rangeKeys (txnStore σ pend) (mrange kk endk e) ds ∧ nd = W64 ds.length⌝ ∗
      storeTxnW t γ trace σ (pend ++ ds.map .delete) ∗
      Lease.lessorState γl n' (delsLs ls ds) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
