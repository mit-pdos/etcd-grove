/-
`(*uberApplier).Alarm(ar)` (`uber_applier.go:214-222`): the chain's `Alarm` (the backend's, promoted), then, for an activation or a deactivation, the chain re-chosen (`restoreAlarms`).

**Users.** `uberApplier.dispatch`.

**Proof sketch.** `applierV3backend.Alarm.spec` (through the outer layers: an alarm is never refused); `uberApplier.restoreAlarms.spec`.

**Changes** from `specs-ref`'s file of the same name: restated over the new vocabulary (`beAt`, `stAt`, `applierAt`, the model state); one spec for every mode.

**Margin.** The alarm list's order (`resMatch`).
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

/-- **An alarm action**, the chain at the new alarms. -/
def uberApplier.Alarm.spec : Prop :=
  ∀ (p b aa q : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (act : AlarmAct) (m : Nat) (at' : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ uberAt p b aa mc γ γc R ∗ uberChain p (chainLayers σ) ∗ stAt b σ ∗
      reqMsgAt q (.alarm act m at') ∗ ⌜(IrrOp.alarm act m at').ok⌝ ∗ threadTok }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier.ty @!! go!"Alarm")) (Val #q))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      ∃ σ' res res', ⌜alarmStep σ act m at' σ' res ∧ resMatch (.alarm act m at') false res res'⌝ ∗
        uberChain p (chainLayers σ') ∗ stAt b σ' ∗
        replyAt γ (.alarm act m at') res' (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.api.v3.etcdserverpb.AlarmResponse.ty) #resp) err }}

end spec

end Apply
end EtcdGrove
end Perennial
