/-
`v3rpc.checkTxnRequest` (`server/etcdserver/api/v3rpc/`).

Users: `kvServer.Txn`, `checkRequestOp` (nested transactions).

Proof sketch: the operation count against `n`, the comparisons' keys, `checkRequestOp.spec` of each operation at `n - opc`; together with `checkIntervals` and the server's `--max-txn-ops` (`kvServerAt`), the law `txnCheck_checked` turns `nil` into 2c's `txnChecked t` and the depth bound.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/checkTxnRequest.lean`: over `txnReqOwn` and `txnCheck`; the depth fact moved to the law `txnCheck_checked` (`notes/irr-depth.md`).

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto EtcdServer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `checkTxnRequest(r, n)`: `nil`, or the `ErrGRPC*` of `txnCheck n t`. -/
def checkTxnRequest.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (t : TxnReq) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ txnReqOwn p dq t }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkTxnRequest)) (Val #p)) (Val #n))
  {{ (err : GoInterface), RET #err; txnReqOwn p dq t ∗ (⌜txnCheck (sint.Z n) t = none ∧ err = GoInterface.nil⌝ ∨
       ∃ e, ⌜txnCheck (sint.Z n) t = some e⌝ ∗ statusErr err (Rpctypes.code e) (Rpctypes.desc e)) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
