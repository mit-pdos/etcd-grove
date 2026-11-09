/-
`v3rpc.checkDeleteRequest` (`server/etcdserver/api/v3rpc/`).

Users: `kvServer.DeleteRange`, `checkRequestOp`.

Proof sketch: the key's length.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/checkDeleteRequest.lean`.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

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

/-- `checkDeleteRequest(r)`: `nil`, or `ErrGRPCEmptyKey`. -/
def checkDeleteRequest.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (r : DeleteReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ deleteReqOwn p dq r }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkDeleteRequest)) (Val #p))
  {{ (err : GoInterface), RET #err; deleteReqOwn p dq r ∗ (⌜deleteCheck r = none ∧ err = GoInterface.nil⌝ ∨
       ∃ e, ⌜deleteCheck r = some e⌝ ∗ statusErr err (Rpctypes.code e) (Rpctypes.desc e)) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
