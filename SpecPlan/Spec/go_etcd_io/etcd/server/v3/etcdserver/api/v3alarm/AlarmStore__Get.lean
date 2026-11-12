/-
## `(*AlarmStore).Get(at)` (`alarms.go:97-113`): translated

**Users.** 3a's appliers (`NOSPACE`, `CORRUPT` checks), the server's `Alarms()` (2a's alarm list),
`v3rpc`'s maintenance. **Proof sketch.** Under the lock, the map's pointers (read-only once stored)
appended to a fresh slice: a read of the view. **Changes**: from `specs-ref`'s
`AlarmStore__Get.lean`: the view's read. **Margin.** The order is a map's.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Api
public import SpecPlan.Spec.go_uber_org.zap.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.Api

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

/-- **The alarms of type `at`** (all for `NONE`). -/
def AlarmStore.Get.spec : Prop :=
  ∀ (a : Loc) (γ : AlarmNames) (at' : w32) (Q : List Alarm → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm ∗ isAlarmStore a γ ∗
      (AU <{ ∃∃ (al : List Alarm), alarmSt γ al }> @ ⊤, ∅ <{ alarmSt γ al, COMM Q al }>) }}
    (App (Val (a @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore.ty @!! go!"Get")) (Val #at'))
  {{ (sl : GoSlice), RET #sl; ∃ (al : List Alarm) (ps : List Loc) (l : List Alarm), Q al ∗
      sl ↦* ps ∗ ([∗list] pa ∈ ps.zip l, alarmMemberRO pa.1 pa.2) ∗
      ⌜ps.length = l.length ∧ l.Perm (getOf al at')⌝ }}

end spec

end V3alarm
end EtcdGrove
end Perennial
