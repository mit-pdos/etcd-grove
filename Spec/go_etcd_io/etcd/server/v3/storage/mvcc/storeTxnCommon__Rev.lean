/-
`(*storeTxnCommon).Rev()` (`kvstore_txn.go:67`): the `rev` field. Internal (promoted to
`storeTxnRead`; `storeTxnWrite` has its own `Rev`).

**Changes** from `specs-ref`'s file: over `txnCommon` (`InternalTxn.lean`).
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

/-- A read transaction's revision; a write transaction's field `0` (its `Rev` is `beginRev`). -/
def storeTxnCommon.Rev.spec : Prop :=
  ∀ (c : Loc) (γ : MvccName) (trace : Loc) (k : MTxn),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      txnCommon c γ trace k }}
    (App (Val (c @!! go.GoType.PointerType storeTxnCommon.ty @!! go!"Rev")) (Val #()))
  {{ RET #(match k with
      | .read σ => (W64 σ.rev : w64)
      | .write _ _ => (W64 0 : w64)); txnCommon c γ trace k }}

end spec
end Mvcc
end EtcdGrove
end Perennial
