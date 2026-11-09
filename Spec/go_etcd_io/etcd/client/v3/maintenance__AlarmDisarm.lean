/-
`(*clientv3.maintenance).AlarmDisarm` (`client/v3/maintenance.go`).

Users: snippet `clientv3client/maint.go` (`ReqAlarmDisarm`); etcdctl (`alarm disarm`, which passes
`AlarmMember{}`: every alarm, out of this spec's scope).

Proof sketch: `am`'s fields read (read-only); not `(0, NONE)`: the request `Alarm(DEACTIVATE, mid, t)`
(`reqOwn _ _ (.alarmDisarm ..)`), `m.remote.Alarm` (repeatable: persistent update), `ContextError`.

Changes: new (no old spec).

Margin: the "disarm every alarm" call (`MemberID = 0`, `Alarm = NONE`) is a list then one disarm per
alarm, several requests: not specified (no user in scope). Round 5: any other type is the model's
`AlarmKind.other` (`alarmKindOf`), no longer a scope restriction.

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

/-- `mt.AlarmDisarm(ctx, am)`: one alarm disarmed, linearized by the caller's persistent update. -/
def maintenance.AlarmDisarm.spec : Prop :=
  ∀ (mt c : Loc) (γ : Cluster) (who : Principal),
  Maint.AlarmDisarmTriple (fun s => mt @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.maintenance.ty @!! s) iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ maintHandle mt c γ who ∗ clientReady c) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
