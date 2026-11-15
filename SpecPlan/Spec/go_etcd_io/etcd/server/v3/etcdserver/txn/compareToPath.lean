/-
`compareToPath(rv, rt)` (`txn.go`), internal (`Txn`): mirrors the code (`txnPathOf` at the view's
current store; every comparison, nested ones included, read at the view:
`nonissues/etcd-txn-nested-compare-snapshot.md`). Old spec: same over the log. Round 1: 3e's API.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `compareToPath(rv, rt)`: a fresh slice of `txnPathOf t` at the transaction's current store. -/
def compareToPath.spec : Prop :=
  ∀ (rv : GoInterface) (γ : Mvcc.MvccName) (tr : Loc) (k : Mvcc.MTxn) (rt : Loc) (dq : DFrac)
    (t : TxnReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ TraceUtil.traceOwn tr ∗ Mvcc.mvccTxn rv γ tr k ∗ txnReqOwn rt dq t }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.compareToPath)) (Val #rv)) (Val #rt))
  {{ (sl : GoSlice), RET #sl; TraceUtil.traceOwn tr ∗ Mvcc.mvccTxn rv γ tr k ∗ txnReqOwn rt dq t ∗
      sl ↦* txnPathOf t k.readHist.store }}

end spec
end Txn
end EtcdGrove
end Perennial
