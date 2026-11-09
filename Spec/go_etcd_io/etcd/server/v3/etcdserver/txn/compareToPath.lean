/-
`compareToPath(rv, rt)` (`txn.go`), internal (`Txn`): mirrors the code (`txnPathOf` at the view's
pending store; every comparison, nested ones included, read at the view:
`nonissues/etcd-txn-nested-compare-snapshot.md`). Old spec: same over the log.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

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

/-- `compareToPath(rv, rt)`: a fresh slice of `txnPathOf t` at the view's pending store. -/
def compareToPath.spec : Prop :=
  ∀ (rv : GoInterface) (γ : MvccName) (k : TxKind) (h : KVHist) (evs : List Event) (rt : Loc)
    (dq : DFrac) (t : TxnReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ mvccTxn rv γ k h evs ∗ txnReqOwn rt dq t }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.compareToPath)) (Val #rv)) (Val #rt))
  {{ (sl : GoSlice), RET #sl; mvccTxn rv γ k h evs ∗ txnReqOwn rt dq t ∗
      sl ↦* txnPathOf t (h.store.applyEvents evs) }}

end spec
end Txn
end EtcdGrove
end Perennial
