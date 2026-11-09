/-
`applyCompare(rv, c)` (`txn.go`), internal: the view's `Range` of the comparison's range at revision
`0` (3e; `mkGteRange`), then W0's `Compare.holds` (a value comparison of no key fails, the others
compare the zero key-value). Old spec: same over the log.
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
/-- `applyCompare(rv, c)`: W0's `Compare.holds` at the view's pending store. -/
def applyCompare.spec : Prop :=
  ∀ (rv : GoInterface) (γ : MvccName) (k : TxKind) (h : KVHist) (evs : List Event) (c : Loc)
    (dq : DFrac) (cm : EtcdModel.Compare),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ mvccTxn rv γ k h evs ∗ compareOwn c dq cm }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.applyCompare)) (Val #rv)) (Val #c))
  {{ RET #(decide (cm.holds (h.store.applyEvents evs))); mvccTxn rv γ k h evs ∗ compareOwn c dq cm }}

end spec
end Txn
end EtcdGrove
end Perennial
