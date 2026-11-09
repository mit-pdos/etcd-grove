/-
`(*applierV3backend).Alarm(r)` (`backend.go:109-136`): `GET`: the alarm store's `Get`; `ACTIVATE` (not `NONE`): `Activate`; `DEACTIVATE`: `Deactivate`.

**Users.** `uberApplier.dispatch` through the chain (promoted methods of the outer layers).

**Proof sketch.** 2e's `AlarmStore.Get`/`Activate`/`Deactivate` (their atomic updates fired on `alarmSt` inside `stAt`; the `Get` list a permutation: the result's `resMatch`); the gauge (`alarms`, names only).

**Changes** from `specs-ref`'s `applierV3backend__Alarm.lean`: the old triple over the chain's `AEnv`, the mvcc log and the write tokens (`putPre`, `kvPostF`, `mPostW`, ...) restated over the model state (`stAt`, `layersStep`): any auth mode, leases, compaction

**Margin.** The alarm list in the store's map order (`resMatch`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult

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

/-- **`Alarm` at the applierV3backend layer**: the layers' step (the result `resMatch`). -/
def applierV3backend.Alarm.spec : Prop :=
  ∀ (p : Loc) (b aa : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (rq : Loc) (op : IrrOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty) #p) [Layer.backend] p aa ∗
      beAt p mc γ γc R ∗
      stAt p σ ∗
      reqMsgAt rq op ∗ ⌜(∃ a m t, op = .alarm a m t) ∧ op.ok⌝ ∗
      R ∗
      threadTok }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty @!! go!"Alarm")) (Val #rq))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      R ∗ threadTok ∗ ∃ σ' res res', ⌜layersStep mc σ [] 0 op [Layer.backend] σ' res ∧ resMatch op false res res'⌝ ∗
      stAt p σ' ∗ replyAt γ op res' (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.AlarmResponse.ty) #resp) err }}

end spec

end Apply
end EtcdGrove
end Perennial
