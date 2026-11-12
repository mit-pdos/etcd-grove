/-
`v3alarm.AlarmStore.Get` (`alarms.go`: it reads the alarms under the store's mutex). Lean-first
(no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3 go_etcd_io.etcd.pkg.v3 go_uber_org

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `a.Get(aty)` on an alarm store `a` returns some slice of the alarms of type `aty` (of
every type for `AlarmType_NONE`); (2026-11-01, J8a-5) with the store's user's half at no alarm
(`alarmEmpty a be`, for some `be`: `ob = some be`), an empty slice. -/
abbrev v3alarm.AlarmStore.Get.spec : Prop :=
  ∀ (a : Loc) (aty : w32) (ob : Option Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm ∗
      isAlarmStore a ∗ (match ob with | none => iprop(True) | some be => alarmEmpty a be) }}
    (App (Val (a @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore.ty @!! go!"Get")) (Val #aty))
  {{ (sl : GoSlice), RET #sl;
      (match ob with | none => iprop(True) | some be => alarmEmpty a be) ∗
      ⌜ob.isSome → sl.len = W64 0⌝ }}

end spec

end EtcdGrove
end Perennial
