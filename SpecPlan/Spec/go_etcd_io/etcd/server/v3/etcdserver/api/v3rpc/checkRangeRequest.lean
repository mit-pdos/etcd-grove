/-
`v3rpc.checkRangeRequest` (`server/etcdserver/api/v3rpc/`).

Users: `kvServer.Range`, `checkRangeStreamRequest`, `checkRequestOp` (this package).

Proof sketch: the key's length; the sort order and target looked up in the generated enum maps (3h's init law: `0..2`, `0..4`, W0's `RangeReq.validSort`); the error variables (`Rpctypes.init.spec`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/checkRangeRequest.lean`: over W0's `rangeReqOwn` and the model's `rangeCheck`.

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

/-- `checkRangeRequest(r)`: `nil`, or the `ErrGRPC*` of `rangeCheck r`. -/
def checkRangeRequest.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (r : RangeReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ rangeReqOwn p dq r }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkRangeRequest)) (Val #p))
  {{ (err : GoInterface), RET #err; rangeReqOwn p dq r ∗
      (⌜rangeCheck r = none ∧ err = GoInterface.nil⌝ ∨
       ∃ e, ⌜rangeCheck r = some e⌝ ∗ statusErr err (Rpctypes.code e) (Rpctypes.desc e)) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
