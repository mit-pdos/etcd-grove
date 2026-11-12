/-
## `(*alarmBackend).CreateAlarmBucket()`: assumed (names only)

**Users.** The alarm store (2e: `NewAlarmStore` creates the bucket and reads every alarm;
`Activate`/`Deactivate` put and delete on the apply thread; `Recover`). Snippet: `examples/specreq/schema/schema.go`
(`ReqAlarmPutGet`).

**Assumed** (`alarm.go`): `be.BatchTx()`, `LockOutsideApply()`, `UnsafeCreateBucket(Alarm)`, `Unlock()`. The bucket's records are as `alarmBkt` says (its realization in the
API's header). The lock calls' `ETCD_VERIFY` checks (`backend/verify.go`) hold at etcd's call sites:
that is 4a's environment premise, carried by `alarmBkt`'s and `applyHook`'s realization.

**Changes.** New (the old alarm store's backend calls were inside its trusted specs).
**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

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

/-- **Creates `Alarm`** (if absent). -/
def alarmBackend.CreateAlarmBucket.spec : Prop :=
  ∀ (ab lg : Loc) (be : GoInterface) (al : Option (List EtcdModel.Alarm)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (ab ↦□ (go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.mk lg be) : IProp GF) ∗ alarmBkt be al }}
    (App (Val (ab @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.ty @!! go!"CreateAlarmBucket")) (Val #()))
  {{ RET #(); alarmBkt be (some (al.getD [])) }}

end spec
end Schema
end EtcdGrove
end Perennial
