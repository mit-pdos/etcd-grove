/-
`(*storeTxnWrite).Changes()` (`kvstore_txn.go:348`): the `changes` slice. Internal: the length for
`Txn.Changes.contract` (through `metricsTxnWrite`), the records themselves for 3f's
`watchableStoreTxnWrite.End` (it builds an event per record and writes a delete's `ModRevision`).
The records stay in the transaction; a caller that needs them takes them with
`storeTxnW_changes` (`changesSl t chs`: then only `End`, which takes `storeTxnWNC`, follows).

**Changes** from `specs-ref`'s file: over `storeTxnW`, `changesSl` and `changesM` (W0's events).
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

/-- The change slice: one record per event (`storeTxnW_changes` hands them out). -/
def storeTxnWrite.Changes.spec : Prop :=
  ∀ (t : Loc) (γ : MvccName) (trace : Loc) (σ : MvccState) (pend : List Event),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      storeTxnW t γ trace σ pend }}
    (App (Val (t @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"Changes")) (Val #()))
  {{ (chs : GoSlice), RET #chs; storeTxnW t γ trace σ pend ∗ changesSl t chs ∗
      ⌜uint.nat chs.len = pend.length ∧ 0 ≤ sint.Z chs.len⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
