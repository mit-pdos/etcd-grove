/-
# The alarm store (`etcdserver/api/v3alarm`): vocabulary (batch 2e)

A member's **applied view of the cluster's alarms** (W0's `State.alarms`): the apply thread raises
and clears them (`Activate`, `Deactivate`: batch 3a's alarm applier, at an `AlarmRequest`'s commit:
an `EnvStep.alarm` through `envUpd`, or the client's `AlarmDisarm` `Step`), reloads them after a
snapshot (`Recover`, 2d's `applySnapshot`), and the request path and the appliers read them (`Get`:
the quota and corruption appliers, `Alarms()`). Translated: `Get`, `Recover`; the rest names only
(trusted, `alarms.go`).

## Vocabulary

* `kindOf at` (transparent): the model's alarm kind of `pb.AlarmType` `at` (`1`: `NOSPACE`, `2`:
  `CORRUPT`; `NONE` and others: none).
* `AlarmNames` (opaque), `isAlarmStore a γ` (persistent): `a` is an `*AlarmStore` whose view is
  named `γ`. Intended realization: its mutex's invariant holding the `types` map (each
  `*pb.AlarmMember` read-only once stored), the authoritative half of a ghost variable of the view,
  and the backend's alarm bucket through `alarmBe`.
* `alarmSt γ al` (exclusive, timeless): **the view is `al`** (as a set: no duplicates). Every
  method takes an atomic update over it.
* `alarmBe ab al` (exclusive): **provisional, batch 4b's** (`schema.AlarmBackend`): the alarm
  bucket of the backend behind `ab` holds `al`. The store owns it while `ab` is its backend;
  `Recover` takes the new backend's.
* `alarmMemberRO p a` (persistent): a read-only `*pb.AlarmMember` holding `a`.

## Laws

`isAlarmStore_persistent`, `alarmSt_timeless`, `alarmSt_excl`, `alarmMemberRO_persistent`.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.Model
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3alarm

open Iris Iris.BI EtcdModel Classical

/-- The model's kind of a `pb.AlarmType`. -/
def kindOf (at' : w32) : Option AlarmKind :=
  if at' = W32 1 then some .nospace else if at' = W32 2 then some .corrupt else none

/-- Whether `a` and `b` are the same alarm (member and kind). -/
def sameAlarm (a b : Alarm) : Prop := a.memberId = b.memberId ∧ a.kind = b.kind

/-- The alarms of kind `k` in `al` (all of them for `none`: `Get(NONE)`). -/
def ofKind (al : List Alarm) (k : Option AlarmKind) : List Alarm :=
  match k with
  | none => al
  | some k => al.filter (fun b => decide (b.kind = k))

/-- A view's ghost names (opaque). -/
opaque AlarmNames : Type := Unit

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext]

/-- `a` is an alarm store whose view is named `γ` (persistent). -/
opaque isAlarmStore (a : Loc) (γ : AlarmNames) : IProp GF := iprop(True)

/-- **The view is `al`** (exclusive). -/
opaque alarmSt (γ : AlarmNames) (al : List Alarm) : IProp GF := iprop(True)

/-- **Provisional (batch 4b):** the alarm bucket behind `ab` holds `al` (exclusive). -/
opaque alarmBe (ab : GoInterface) (al : List Alarm) : IProp GF := iprop(True)

/-- **Provisional (batch 4b):** the alarm bucket of the open backend `be` holds `al`
(exclusive); `schema.NewAlarmBackend(lg, be)` turns it into `alarmBe ab al` of its result. -/
opaque beAlarms (be : GoInterface) (al : List Alarm) : IProp GF := iprop(True)

/-- A read-only `*pb.AlarmMember` holding `a` (persistent). -/
opaque alarmMemberRO (p : Loc) (a : Alarm) : IProp GF := iprop(True)

def isAlarmStore_persistent.spec : Prop := ∀ a γ, Persistent (isAlarmStore (GF := GF) a γ)
def alarmSt_timeless.spec : Prop := ∀ γ al, Timeless (alarmSt (GF := GF) γ al)
def alarmSt_excl.spec : Prop := ∀ γ al al',
  alarmSt (GF := GF) γ al ∗ alarmSt γ al' ⊢ iprop(False)
def alarmMemberRO_persistent.spec : Prop := ∀ p a, Persistent (alarmMemberRO (GF := GF) p a)

end res

end V3alarm
end EtcdGrove
end Perennial
