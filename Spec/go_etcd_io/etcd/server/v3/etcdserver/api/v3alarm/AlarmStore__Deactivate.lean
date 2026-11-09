/-
## `(*AlarmStore).Deactivate(id, at)` (`alarms.go:76-95`): names only

**Users.** 3a's alarm applier (`DEACTIVATE`: the client's `AlarmDisarm`, a `Step`).
**Why it is true.** Under the lock: the alarm removed from the map and the backend
(`MustDeleteAlarm`) if present, returned; else `nil`. **Changes**: new. **Margin.** Exact.
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

/-- **Clears alarm `(id, at)`**; returns it, or `nil` if it was not raised. -/
def AlarmStore.Deactivate.spec : Prop :=
  ∀ (a : Loc) (γ : AlarmNames) (id : w64) (at' : w32) (k : AlarmKind) (Q : List Alarm → IProp GF),
  kindOf at' = some k →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm ∗ isAlarmStore a γ ∗ ⌜ServerStorage.diskOk⌝ ∗
      (AU <{ ∃∃ (al : List Alarm), alarmSt γ al }> @ ⊤, ∅
        <{ alarmSt γ (clear al ⟨uint.nat id, k⟩), COMM Q al }>) }}
    (App (App (Val (a @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore.ty @!! go!"Deactivate")) (Val #id)) (Val #at'))
  {{ (p : Loc), RET #p; ∃ al : List Alarm, Q al ∗
      ((⌜p = null ∧ ¬ ∃ b ∈ al, sameAlarm ⟨uint.nat id, k⟩ b⌝) ∨
       (⌜∃ b ∈ al, sameAlarm ⟨uint.nat id, k⟩ b⌝ ∗ alarmMemberRO p ⟨uint.nat id, k⟩)) }}

end spec

end V3alarm
end EtcdGrove
end Perennial
