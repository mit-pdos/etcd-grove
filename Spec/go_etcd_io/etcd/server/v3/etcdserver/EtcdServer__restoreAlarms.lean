/-
## `(*EtcdServer).restoreAlarms()` (`server.go:2424-2433`)

**Users.** `NewServer` (`server.go:384`).

**Proof sketch.** `schema.NewAlarmBackend(s.lg, s.be)` (4b: `V3alarm.beAlarms be al` becomes
`alarmBe ab al`), `V3alarm.NewAlarmStore.spec` (the store's view at the bucket's alarms, or an
error), then the field written.

**Changes** (from `specs-ref`'s `EtcdServer__restoreAlarms.lean`): over the alarm store's view.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Builds the alarm store** over the backend's alarm bucket. -/
def EtcdServer.restoreAlarms.spec : Prop :=
  ∀ (s lg : Loc) (be : GoInterface) (old : Loc) (al : List Alarm),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ Zap.isLogger lg ∗
      typedPointsto (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"lg" s) lg DFrac.discard ∗
      typedPointsto (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"be" s) be DFrac.discard ∗
      typedPointsto (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"alarmStore" s) old (DFrac.own 1) ∗
      V3alarm.beAlarms be al }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"restoreAlarms")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ a : Loc,
      typedPointsto (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"alarmStore" s) a (DFrac.own 1) ∗
      (⌜err = GoInterface.nil⌝ ∗ ∃ γa, V3alarm.isAlarmStore a γa ∗ V3alarm.alarmSt γa al ∨
       ⌜err ≠ GoInterface.nil⌝) }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
