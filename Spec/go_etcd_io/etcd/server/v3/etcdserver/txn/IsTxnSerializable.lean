/-
## `IsTxnSerializable(r)` (`txn.go`)

**Users.** `EtcdServer.Txn` (`v3_server.go:345`: a serializable read-only transaction skips the read
index). Snippet: `examples/specreq/txn/helpers.go` (`ReqReadonlyKinds`).

**Proof sketch.** As `IsTxnReadonly`, reading each range's `Serializable`.

**Changes.** Unchanged in substance (W0's `TxnReq.serializable`; true of the empty transaction:
`issues/etcd-txn-empty-serializable.md`).

**Margin.** None.
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
/-- `IsTxnSerializable(r)`: whether every operation of both branches is a serializable range (W0's
`TxnReq.serializable`). -/
def IsTxnSerializable.spec : Prop :=
  ∀ (rt : Loc) (dq : DFrac) (t : TxnReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ txnReqOwn rt dq t }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.IsTxnSerializable)) (Val #rt))
  {{ RET #(decide t.serializable); txnReqOwn rt dq t }}

end spec
end Txn
end EtcdGrove
end Perennial
