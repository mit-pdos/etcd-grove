/-
## `(*AlarmStore).Recover(be)` (`alarms.go:52-60`): translated

**Users.** 2d's `applySnapshot` (the alarms of the installed snapshot's backend).
**Proof sketch.** Under the lock: the backend replaced, the map emptied, `restore` (names only:
the bucket's alarms added, a force-commit; a read error is `diskOk`'s). The view becomes the new
bucket's. **Changes** (from `specs-ref`'s `AlarmStore__Recover.lean`): the view's update.
**Margin.** None.
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

/-- **Reloads the alarms** from the new backend. -/
def AlarmStore.Recover.spec : Prop :=
  ∀ (a : Loc) (γ : AlarmNames) (ab : GoInterface) (al' : List Alarm) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm ∗ isAlarmStore a γ ∗ alarmBe ab al' ∗ ⌜ServerStorage.diskOk⌝ ∗
      (AU <{ ∃∃ (al : List Alarm), alarmSt γ al }> @ ⊤, ∅ <{ alarmSt γ al', COMM Q }>) }}
    (App (Val (a @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore.ty @!! go!"Recover")) (Val #ab))
  {{ RET #GoInterface.nil; Q }}

end spec

end V3alarm
end EtcdGrove
end Perennial
