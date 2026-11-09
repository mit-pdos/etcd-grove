/-
`NewReadOnlyTxnWrite(txn)` (`kv.go:103`): a read transaction as a `TxnWrite` whose writes panic.

**Users**: `txn.Txn`'s read-only path (`txn/txn.go:69`), the tester (`mvccrand.go:475, 626`). Snippet
`ReqReadOnlyTxn`.

**Proof sketch**: allocate `&txnReadWrite{txn}`; its `mvccTxn` at `.read σ` wraps the inner one (the
`txnReadWrite` methods are the inner's, promoted, or the write methods no `.read` transaction may
call).

**Changes** from `specs-ref`'s `NewReadOnlyTxnWrite.lean`: the result's type named.

**Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

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

/-- `NewReadOnlyTxnWrite(t)` of a read transaction: a `*txnReadWrite`, the same transaction. -/
def NewReadOnlyTxnWrite.spec : Prop :=
  ∀ (t : GoInterface) (γ : MvccName) (trace : Loc) (σ : MvccState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvccTxn (GF := GF) t γ trace (.read σ) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewReadOnlyTxnWrite)) (Val #t))
  {{ (p : Loc), RET #(interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #p);
      mvccTxn (interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #p) γ trace (.read σ) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
