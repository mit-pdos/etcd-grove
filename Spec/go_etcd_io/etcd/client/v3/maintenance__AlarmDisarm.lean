/-
`(*clientv3.maintenance).AlarmDisarm` (`client/v3/maintenance.go`).

Users: snippet `clientv3client/maint.go` (`ReqAlarmDisarm`); etcdctl (`alarm disarm`, which passes
`AlarmMember{}`: every alarm, out of this spec's scope).

Proof sketch: `am`'s fields read (read-only); not `(0, NONE)`: the request `Alarm(DEACTIVATE, mid, t)`
(`reqOwn _ _ (.alarmDisarm ..)`), `m.remote.Alarm` (repeatable: persistent update), `ContextError`.

Changes: new (no old spec).

Margin: the "disarm every alarm" call (`MemberID = 0`, `Alarm = NONE`) is a list then one disarm per
alarm, several requests: not specified (no user in scope); a `NONE` alarm with a member is not a
model alarm (`alarmKindM`): a scope restriction.
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
  ∀ (mt : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (am : Loc) (mid : w64) (t : w32)
    (k : AlarmKind),
  alarmKindM t = some k →
  CallTriple (App (App (Val (mt @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.maintenance.ty @!! go!"AlarmDisarm")) (Val #ctx)) (Val #am))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ maintHandle mt γ who ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗
      am.[go_etcd_io.etcd.api.v3.etcdserverpb.AlarmMember, go!"MemberID"] ↦□ mid ∗
      am.[go_etcd_io.etcd.api.v3.etcdserverpb.AlarmMember, go!"Alarm"] ↦□ t)
    iprop(True) γ who (.alarmDisarm { memberId := uint.nat mid, kind := k }) true ansReply

end spec

end ClientV3
end EtcdGrove
end Perennial
