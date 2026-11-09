/-
`(*storeTxnWrite).Rev()` (`kvstore_txn.go:187`): `beginRev`. Internal (`Txn.Rev.contract` through
`metricsTxnWrite`).

**Changes** from `specs-ref`'s file: over `storeTxnW`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalTxn

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

/-- The revision the transaction began at. -/
def storeTxnWrite.Rev.spec : Prop :=
  ∀ (t : Loc) (γ : MvccName) (trace : Loc) (σ : MvccState) (pend : List EtcdModel.Event),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      storeTxnW t γ trace σ pend }}
    (App (Val (t @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"Rev")) (Val #()))
  {{ RET #(W64 σ.rev : w64); storeTxnW t γ trace σ pend }}

end spec
end Mvcc
end EtcdGrove
end Perennial
