/-
`applyCompares(rv, cmps)` (`txn.go`), internal: mirrors the code (`cmpsHold`). Old spec: same.
Round 1: 3e's API.
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

/-- `applyCompares(rv, cmps)`: every comparison holds at the transaction's current store. -/
def applyCompares.spec : Prop :=
  ∀ (rv : GoInterface) (γ : Mvcc.MvccName) (tr : Loc) (k : Mvcc.MTxn) (cs : GoSlice) (dq : DFrac)
    (cl : List EtcdModel.Compare),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ TraceUtil.traceOwn tr ∗ Mvcc.mvccTxn rv γ tr k ∗ msgsOwn compareOwn cs dq cl }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.applyCompares)) (Val #rv)) (Val #cs))
  {{ RET #(cmpsHold cl k.readHist.store); TraceUtil.traceOwn tr ∗ Mvcc.mvccTxn rv γ tr k ∗
      msgsOwn compareOwn cs dq cl }}

end spec
end Txn
end EtcdGrove
end Perennial
