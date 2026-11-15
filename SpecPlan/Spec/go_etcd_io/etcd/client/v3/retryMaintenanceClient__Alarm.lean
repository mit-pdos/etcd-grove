/-
`(*clientv3.retryMaintenanceClient).Alarm` (`client/v3/retry.go`).

Users: `maintenance.AlarmList`, `maintenance.AlarmDisarm` (through `remoteMaintAt`); a caller
activating an alarm through the stub (`Alarm(ACTIVATE)`, W0's `Req.alarmActivate`: the
`Maintenance` interface has no method for it; etcd's own corruption checker and the functional
tests do).

Proof sketch: appends `withRepeatablePolicy()` (`callOptsOk_append`) and calls the stub over the
connection it was made with (`pb.NewMaintenanceClient(conn)`: `connOk`, 2a/3h).

Changes: new (no old spec).

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiClient

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

/-- `r.Alarm`: the wire contract at an alarm request (list, activate or disarm). -/
def retryMaintenanceClient.Alarm.spec : Prop :=
  ∀ (r c : Loc) (γ : Cluster) (who : Principal) (rq : Req), reqIsMaint rq →
  RemoteCallTriple (fun s => r @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryMaintenanceClient.ty @!! s)
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryMaintHandle r c γ who ∗ clientReady c) γ who rq

end spec

end ClientV3
end EtcdGrove
end Perennial
