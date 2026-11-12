/-
## `(*alarmBackend).GetAllAlarms()`: assumed (names only)

**Users.** The alarm store (2e: `NewAlarmStore` creates the bucket and reads every alarm;
`Activate`/`Deactivate` put and delete on the apply thread; `Recover`). Snippet: `examples/specreq/schema/schema.go`
(`ReqAlarmPutGet`).

**Assumed** (`alarm.go`): `be.ReadTx()`, `RLock()` (a reader slot: the caller's thread token, given back at `RUnlock`), `UnsafeForEach(Alarm, f)` (`f` unmarshals each key: the bucket's keys are marshalled alarms, so no error), `RUnlock()`. The read transaction sees the bucket as its only writer left it. The bucket's records are as `alarmBkt` says (its realization in the
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

/-- **Every alarm**, fresh messages (in key order); no error. -/
def alarmBackend.GetAllAlarms.spec : Prop :=
  ∀ (ab lg : Loc) (be : GoInterface) (al : List EtcdModel.Alarm),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (ab ↦□ (go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.mk lg be) : IProp GF) ∗ alarmBkt be (some al) ∗ threadTok }}
    (App (Val (ab @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.ty @!! go!"GetAllAlarms")) (Val #()))
  {{ (ms : GoSlice) (err : GoInterface), RET (PairV #ms #err); alarmBkt be (some al) ∗ threadTok ∗ ⌜err = GoInterface.nil⌝ ∗ ∃ (l : List EtcdModel.Alarm) (ps : List Loc), ⌜l.Perm al⌝ ∗ ms ↦* ps ∗ [∗list] p; a ∈ ps; l, ∃ c, Proto.msgAt go_etcd_io.etcd.api.v3.etcdserverpb.AlarmMember.ty p (DFrac.own 1) c ∗ ⌜alarmMemberIs c a⌝ }}

end spec
end Schema
end EtcdGrove
end Perennial
