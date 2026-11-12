/-
## `IsTxnReadonly(r)` (`txn.go`)

**Users.** `EtcdServer.Txn` (`v3_server.go:326`: a read-only transaction is served locally); `Txn`
itself (`txn.go:34`). Snippet: `examples/specreq/txn/helpers.go` (`ReqReadonlyKinds`).

**Proof sketch.** The two loops over `Success` and `Failure` (`txnReqOwn`'s unfold law, W0), each
`GetRequestRange()` (3h's getter: non-`nil` exactly for a range operation).

**Changes.** Unchanged in substance (W0's `TxnReq.readonly` for the old `txnReadonly`).

**Margin.** None.
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

open Classical in
/-- `IsTxnReadonly(r)`: whether every operation of both branches is a range (W0's
`TxnReq.readonly`; a nested transaction is not). -/
def IsTxnReadonly.spec : Prop :=
  ∀ (rt : Loc) (dq : DFrac) (t : TxnReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ txnReqOwn rt dq t }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.IsTxnReadonly)) (Val #rt))
  {{ RET #(decide t.readonly); txnReqOwn rt dq t }}

end spec
end Txn
end EtcdGrove
end Perennial
