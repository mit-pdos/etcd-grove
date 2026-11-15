/-
`(*storeTxnRead).End()` (`kvstore_txn.go:161`): `tx.RUnlock()` (`keyBackend`: the storage slot
back), `s.mu.RUnlock()`. Internal (`txnReadWrite.End` through `metricsTxnWrite.End`:
`Txn.End.contract`'s read arm). The reader token is rebuilt from the two slots.

**Changes** from `specs-ref`'s file: over `storeTxnR`; gives back the reader token.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalTxn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The read transaction ended: its reader token back. -/
def storeTxnRead.End.spec : Prop :=
  ∀ (t : Loc) (γ : MvccName) (trace : Loc) (σ : MvccState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      storeTxnR t γ trace σ }}
    (App (Val (t @!! go.GoType.PointerType storeTxnRead.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvccReaders γ 1 }}

end spec
end Mvcc
end EtcdGrove
end Perennial
