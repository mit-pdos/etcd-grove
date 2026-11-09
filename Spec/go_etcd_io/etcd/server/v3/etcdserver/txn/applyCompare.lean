/-
`applyCompare(rv, c)` (`txn.go`), internal: the view's `Range` of the comparison's range at revision
`0` (3e's `Txn.Range`; `mkGteRange`), then W0's `Compare.holds` (a value comparison of no key fails,
the others compare the zero key-value). Old spec: same over the log. Round 1: 3e's API.
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

open Classical in
/-- `applyCompare(rv, c)`: W0's `Compare.holds` at the transaction's current store. -/
def applyCompare.spec : Prop :=
  ∀ (rv : GoInterface) (γ : Mvcc.MvccName) (tr : Loc) (k : Mvcc.MTxn) (c : Loc) (dq : DFrac)
    (cm : EtcdModel.Compare),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ TraceUtil.traceOwn tr ∗ Mvcc.mvccTxn rv γ tr k ∗ compareOwn c dq cm }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.applyCompare)) (Val #rv)) (Val #c))
  {{ RET #(decide (cm.holds k.readHist.store)); TraceUtil.traceOwn tr ∗ Mvcc.mvccTxn rv γ tr k ∗
      compareOwn c dq cm }}

end spec
end Txn
end EtcdGrove
end Perennial
