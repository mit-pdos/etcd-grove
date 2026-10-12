/-
etcd's alarm store (`server/etcdserver/api/v3alarm/alarms.go`): the shared vocabulary of
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3alarm/AlarmStore__*.lean`. Lean-first (no
Rocq counterpart).

An `AlarmStore` keeps its alarms in `a.types`, a map from an alarm type to the set of the
members that raised it (an `alarmSet`, a map from a member id to its `*AlarmMember`), under the
mutex `a.mu`. `isAlarmStore a` (persistent) is that mutex with its lock invariant
`alarmLockInv a`: the map `a.types` and every set in it, owned (`Activate`/`Deactivate`, out of
scope, change them under the lock). What the alarms are is not modelled (the apply thread only
tests whether there is one).
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
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `a.mu`. -/
abbrev alarmMuAddr (a : Loc) : Loc := structFieldRef v3alarm.AlarmStore go!"mu" a

/-- The address of `a.types`. -/
abbrev alarmTypesAddr (a : Loc) : Loc := structFieldRef v3alarm.AlarmStore go!"types" a

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The lock invariant of `a.mu`: the map `a.types` (from an alarm type to its set) and each
set (from a member id to its alarm), owned. -/
def alarmLockInv (a : Loc) : IProp GF :=
  iprop(∃ (tm : GoMap) (gm : GMap w32 GoMap),
    alarmTypesAddr a ↦ tm ∗ tm ↦$ gm ∗
    [∗map] _k ↦ t ∈ gm, ∃ im : GMap w64 Loc, t ↦$ im)

/-- `a` is an alarm store (persistent): its mutex, with the lock invariant. -/
def isAlarmStore (a : Loc) : IProp GF :=
  iprop(sync.isMutex (alarmMuAddr a) (alarmLockInv a))

instance isAlarmStore_persistent (a : Loc) : Persistent (isAlarmStore (GF := GF) a) := by
  unfold isAlarmStore; infer_instance

end defs

end EtcdGrove
end Perennial
