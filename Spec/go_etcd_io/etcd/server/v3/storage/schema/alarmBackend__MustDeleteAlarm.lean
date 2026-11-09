/-
## `(*alarmBackend).MustDeleteAlarm(am)`: assumed (names only)

**Users.** The alarm store (2e: `NewAlarmStore` creates the bucket and reads every alarm;
`Activate`/`Deactivate` put and delete on the apply thread; `Recover`). Snippet: `examples/specreq/schema/schema.go`
(`ReqAlarmPutGet`).

**Assumed** (`alarm.go`): `be.BatchTx()`, `LockInsideApply()`, `proto.Marshal(am)` (deterministic: the stored key), `UnsafeDelete(Alarm, bytes)`, `Unlock()`. The bucket's records are as `alarmBkt` says (its realization in the
API's header). The lock calls' `ETCD_VERIFY` checks (`backend/verify.go`) hold at etcd's call sites:
that is 4a's environment premise, carried by `alarmBkt`'s and `applyHook`'s realization.

**Changes.** New (the old alarm store's backend calls were inside its trusted specs).
**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Schema

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **Removes the alarm** (the post-lock hook run). -/
def alarmBackend.MustDeleteAlarm.spec : Prop :=
  ∀ (ab lg : Loc) (be : GoInterface) (al : List EtcdModel.Alarm) (am : Loc) (dq : DFrac) (c : Proto.Content) (a : EtcdModel.Alarm) (Pre Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (ab ↦□ (go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.mk lg be) : IProp GF) ∗ alarmBkt be (some al) ∗ Proto.msgAt go_etcd_io.etcd.api.v3.etcdserverpb.AlarmMember.ty am dq c ∗ ⌜alarmMemberIs c a⌝ ∗ applyHook be Pre Q ∗ Pre }}
    (App (Val (ab @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.ty @!! go!"MustDeleteAlarm")) (Val #am))
  {{ RET #(); alarmBkt be (some (alarmsDel al a)) ∗ Proto.msgAt go_etcd_io.etcd.api.v3.etcdserverpb.AlarmMember.ty am dq c ∗ Q }}

end spec
end Schema
end EtcdGrove
end Perennial
