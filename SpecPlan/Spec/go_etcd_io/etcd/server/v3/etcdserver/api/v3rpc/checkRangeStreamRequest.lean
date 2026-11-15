/-
`v3rpc.checkRangeStreamRequest` (`server/etcdserver/api/v3rpc/`).

Users: `kvServer.RangeStream` (this package).

Proof sketch: `checkRangeRequest.spec`; `txn.IsDefaultOrdering`, `txn.HasRevisionFilters` (3b's pure functions, W0's `isDefaultOrdering`, `hasRevFilters`); `status.Errorf(codes.Unimplemented, ...)` (`Grpc.Errorf.spec`).

Changes: new.

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

/-- `checkRangeStreamRequest(r)`: `checkRangeRequest`'s error, or `Unimplemented` (a message no
etcd error has) for a custom order or a revision filter, or `nil`. -/
def checkRangeStreamRequest.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (r : RangeReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ rangeReqOwn p dq r }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkRangeStreamRequest)) (Val #p))
  {{ (err : GoInterface), RET #err; rangeReqOwn p dq r ∗
      ((∃ e, ⌜rangeCheck r = some e⌝ ∗ statusErr err (Rpctypes.code e) (Rpctypes.desc e)) ∨
       (⌜rangeCheck r = none ∧ (¬ isDefaultOrdering r.sortTarget r.sortOrder ∨ r.hasRevFilters)⌝ ∗
         ∃ msg, statusErr err cUnimplemented msg ∗ ⌜indefMsg msg⌝) ∨
       ⌜rangeCheck r = none ∧ isDefaultOrdering r.sortTarget r.sortOrder ∧ ¬ r.hasRevFilters ∧
         err = GoInterface.nil⌝) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
