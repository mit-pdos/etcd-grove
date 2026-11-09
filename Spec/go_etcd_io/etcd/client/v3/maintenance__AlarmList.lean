/-
`(*clientv3.maintenance).AlarmList` (`client/v3/maintenance.go`).

Users: snippet `clientv3client/maint.go` (`ReqAlarmDisarm`); `AlarmDisarm` of every alarm; etcdctl.

Proof sketch: the request `Alarm(GET, 0, NONE)` (`reqOwn _ _ .alarmList`), `m.remote.Alarm`
(`maintHandle`: `remoteMaintAt`, repeatable: persistent update), `ContextError` on an error.

Changes: new (no old spec).

Margin: none.

Round 1: the call's principal per call (W0's `ctxPrin who ctx p`); the handle records its client,
ready (`clientReady`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `mt.AlarmList(ctx)`: the raised alarms, linearized by the caller's persistent update. -/
def maintenance.AlarmList.spec : Prop :=
  ∀ (mt c : Loc) (γ : Cluster) (who : Principal),
  Call.Triple (mt @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.maintenance.ty @!! go!"AlarmList")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ maintHandle mt c γ who ∗ clientReady c) γ who [] .alarmList

end spec

end ClientV3
end EtcdGrove
end Perennial
