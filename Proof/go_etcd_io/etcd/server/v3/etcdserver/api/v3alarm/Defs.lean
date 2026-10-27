/-
etcd's alarm store (`server/etcdserver/api/v3alarm/alarms.go`): the shared vocabulary of
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3alarm/AlarmStore__*.lean`. Lean-first (no
Rocq counterpart).

An `AlarmStore` keeps its alarms in `a.types`, a map from an alarm type to the set of the
members that raised it (an `alarmSet`, a map from a member id to its `*AlarmMember`), under the
mutex `a.mu`. `isAlarmStore a` (persistent) is that mutex with its lock invariant
`alarmLockInv a`: the map `a.types` and every set in it, owned (`Activate`/`Deactivate`, out of
scope, change them under the lock), and (D22 receiver epochs, S7c, 2026-10-23) half of the
store's backend `a.be`, whose other half is its user's (`alarmBeOn a d`: the server's apply
thread, the only caller of `Activate`, `Deactivate` and `Recover`): `Recover` (since the fork's
`8fd98af04`, `applySnapshot` recovers the store in place) holds both under the lock to replace it,
so the user's half names the backend the store's writes go to. What the alarms are is not
modelled (the apply thread only tests whether there is one).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `a.mu`. -/
abbrev alarmMuAddr (a : Loc) : Loc := structFieldRef v3alarm.AlarmStore go!"mu" a

/-- The address of `a.types`. -/
abbrev alarmTypesAddr (a : Loc) : Loc := structFieldRef v3alarm.AlarmStore go!"types" a

/-- The address of `a.be`. -/
abbrev alarmBeAddr (a : Loc) : Loc := structFieldRef v3alarm.AlarmStore go!"be" a

/-- The address of the schema alarm backend `abl`'s backend field. -/
abbrev alarmBkBeAddr (abl : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.storage.schema.alarmBackend go!"be" abl

/-- The address of the schema alarm backend `abl`'s logger field. -/
abbrev alarmBkLgAddr (abl : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.storage.schema.alarmBackend go!"lg" abl

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The lock invariant of `a.mu`: the map `a.types` (from an alarm type to its set) and each
set (from a member id to its alarm), owned; half of `a.be` (S7c). -/
def alarmLockInv (a : Loc) : IProp GF :=
  iprop(∃ (tm : GoMap) (gm : GMap w32 GoMap) (ab : GoInterface),
    alarmTypesAddr a ↦ tm ∗ tm ↦$ gm ∗
    ([∗map] _k ↦ t ∈ gm, ∃ im : GMap w64 Loc, t ↦$ im) ∗
    alarmBeAddr a ↦{DFrac.own (1 : Qp).half} ab)

/-- The schema alarm backend `*alarmBackend` `abl` as an interface value. -/
abbrev alarmBkIface (abl : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.ty)
    #abl

/-- **The alarm store `a` is on the real backend at `be`** (D22 receiver epochs, S7c, 2026-10-23;
not persistent): its user's half of `a.be`, a schema alarm backend over `be` with a logger (both
read-only). The store's writes and its `Recover` take it (`apply.isAlarmStore`'s write right,
`NewAlarmStore`'s contract): with the lock's half it names the backend they write to. -/
def alarmBeOn (a be : Loc) : IProp GF :=
  iprop(∃ (abl lg : Loc), ⌜lg ≠ null⌝ ∗
    alarmBeAddr a ↦{DFrac.own (1 : Qp).half} alarmBkIface abl ∗
    alarmBkBeAddr abl ↦□ (interface.mkOk
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #be :
        GoInterface) ∗
    alarmBkLgAddr abl ↦□ lg)

/-- `a` is an alarm store (persistent): its mutex, with the lock invariant. -/
def isAlarmStore (a : Loc) : IProp GF :=
  iprop(sync.isMutex (alarmMuAddr a) (alarmLockInv a))

instance isAlarmStore_persistent (a : Loc) : Persistent (isAlarmStore (GF := GF) a) := by
  unfold isAlarmStore; infer_instance

end defs

end EtcdGrove
end Perennial
