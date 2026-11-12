/-
`v3rpc.checkPutRequest` (`server/etcdserver/api/v3rpc/`).

Users: `kvServer.Put`, `checkRequestOp`.

Proof sketch: the fields' checks (W0's `PutReq.invalid` mirrors them).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/checkPutRequest.lean`: over `putReqOwn` and `PutReq.invalid`.

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

/-- `checkPutRequest(r)`: `nil`, or the `ErrGRPC*` of `r.invalid`. -/
def checkPutRequest.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (r : PutReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ putReqOwn p dq r }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkPutRequest)) (Val #p))
  {{ (err : GoInterface), RET #err; putReqOwn p dq r ∗ (⌜r.invalid = none ∧ err = GoInterface.nil⌝ ∨
       ∃ e, ⌜r.invalid = some e⌝ ∗ statusErr err (Rpctypes.code e) (Rpctypes.desc e)) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
