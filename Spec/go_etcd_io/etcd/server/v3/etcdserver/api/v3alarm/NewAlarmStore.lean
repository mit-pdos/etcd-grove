/-
## `NewAlarmStore(lg, be)` (`alarms.go:42-50`): names only

**Users.** `EtcdServer.restoreAlarms` (`NewServer`). **Why it is true.** A store whose `restore`
creates the bucket, reads every alarm (`GetAllAlarms`: an error returned, with the store), adds each
to the map (a set: one per member and type), force-commits. **Changes** (from `specs-ref`'s
`NewAlarmStore.lean`): the view of the bucket. **Margin.** On an error the view is not stated.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Api
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3alarm

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Assumptions]

/-- **An alarm store** whose view is the backend's alarms (or an error). -/
def NewAlarmStore.spec : Prop :=
  ∀ (lg : Loc) (ab : GoInterface) (al : List Alarm),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ alarmBe ab al }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.NewAlarmStore)) (Val #lg)) (Val #ab))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); ∃ γ : AlarmNames, isAlarmStore a γ ∗
      ((⌜err = GoInterface.nil⌝ ∗ alarmSt γ al) ∨ ⌜err ≠ GoInterface.nil⌝) }}

end spec

end V3alarm
end EtcdGrove
end Perennial
