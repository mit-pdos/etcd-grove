/-
`v3rpc.checkRequestOp` (`server/etcdserver/api/v3rpc/`).

Users: `checkTxnRequest` (this package, mutually recursive).

Proof sketch: the oneof's dynamic type (W0's `requestOneof`): each case's check, `checkTxnRequest.spec` for a nested transaction (the recursion, on a smaller model), `ErrGRPCKeyNotFound` for an empty operation.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/checkRequestOp.lean`: over `requestOpOwn` and `opCheck`.

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

/-- `checkRequestOp(u, n)`: `nil`, or the `ErrGRPC*` of `opCheck n op`. -/
def checkRequestOp.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (op : RequestOp) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ requestOpOwn p dq op }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkRequestOp)) (Val #p)) (Val #n))
  {{ (err : GoInterface), RET #err; requestOpOwn p dq op ∗ (⌜opCheck (sint.Z n) op = none ∧ err = GoInterface.nil⌝ ∨
       ∃ e, ⌜opCheck (sint.Z n) op = some e⌝ ∗ statusErr err (Rpctypes.code e) (Rpctypes.desc e)) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
