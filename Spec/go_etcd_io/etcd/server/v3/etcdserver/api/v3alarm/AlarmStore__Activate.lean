/-
## `(*AlarmStore).Activate(id, at)` (`alarms.go:62-74`): names only

**Users.** 3a's alarm applier (an `AlarmRequest` `ACTIVATE` committed: `EnvStep.alarm`).
**Why it is true.** Under the lock: the alarm added to the map unless present (then the stored one
returned), else saved to the backend (`MustPutAlarm`) and returned. **Changes**: new.
**Margin.** Exact.
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

/-- **Raises alarm `(id, at)`**; returns the stored alarm. -/
def AlarmStore.Activate.spec : Prop :=
  ∀ (a : Loc) (γ : AlarmNames) (id : w64) (at' : w32) (k : AlarmKind) (Q : IProp GF),
  kindOf at' = some k →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm ∗ isAlarmStore a γ ∗ ⌜ServerStorage.diskOk⌝ ∗
      (AU <{ ∃∃ (al : List Alarm), alarmSt γ al }> @ ⊤, ∅
        <{ alarmSt γ (raise al ⟨uint.nat id, k⟩), COMM Q }>) }}
    (App (App (Val (a @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore.ty @!! go!"Activate")) (Val #id)) (Val #at'))
  {{ (p : Loc), RET #p; Q ∗ alarmMemberRO p ⟨uint.nat id, k⟩ }}

end spec

end V3alarm
end EtcdGrove
end Perennial
