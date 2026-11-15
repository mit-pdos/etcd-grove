/-
`(*uberApplier).restoreAlarms()` (`uber_applier.go:70-80`): the chain re-chosen from the alarm store: the base, capped if a `NOSPACE` alarm, corrupt if a `CORRUPT` one.

**Users.** `NewUberApplier`, `uberApplier.Alarm`.

**Proof sketch.** 2e's `AlarmStore.Get` twice (its update fired on `alarmSt` inside `stAt`, the state unchanged: `V3alarm.getOf`); `newApplierV3Capped.spec`, `newApplierV3Corrupt.spec` over `applyV3base`.

**Changes** from `specs-ref`'s file of the same name: restated over the new vocabulary (`beAt`, `stAt`, `applierAt`, the model state); one spec for every mode.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Apply

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The chain the alarms select.** -/
def uberApplier.restoreAlarms.spec : Prop :=
  ∀ (p b aa : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (ls : List Layer),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ uberAt p b aa mc γ γc R ∗ uberChain p ls ∗ stAt b σ }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier.ty @!! go!"restoreAlarms")) (Val #()))
  {{ RET #(); uberChain p (chainLayers σ) ∗ stAt b σ }}

end spec

end Apply
end EtcdGrove
end Perennial
