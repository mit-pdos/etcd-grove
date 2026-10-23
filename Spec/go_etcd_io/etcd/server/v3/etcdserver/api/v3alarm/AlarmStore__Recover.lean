/-
`(*v3alarm.AlarmStore).Recover(be)` (`alarms.go`, since the fork's `8fd98af04`: `applySnapshot`
recovers the alarm store in place; D22 receiver epochs, S7c, 2026-10-23). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore__restore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Assumptions]

/-- **`a.Recover(ab)`**, by the store's user (its half of `a.be`, `alarmBeOn a be0`: the store on the
backend at `be0`), with a schema alarm backend `ab` over the real backend at `be` whose alarm bucket
is empty or absent: under the store's mutex, `a.be := ab`, `a.types` a fresh map, `restore`
(`AlarmStore.restore.spec`); no error, the store on the backend at `be` (`alarmBeOn a be`), the
alarm bucket created. -/
abbrev v3alarm.AlarmStore.Recover.spec : Prop :=
  ∀ (a be0 abl lg be : Loc) (γB : backend.BNames) (P : backend.BParams) (W Pk : IProp GF)
    (qo : Qp) (r : GMap GoString backend.BktData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm ∗
      isAlarmStore a ∗ alarmBeOn a be0 ∗
      alarmBkBeAddr abl ↦□ (interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #be :
          GoInterface) ∗
      alarmBkLgAddr abl ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
      backend.isBackend γB P W Pk be ∗ backend.bOpen γB qo ∗ backend.wbTok γB ∗
      backend.rbOwn γB r ∗ ⌜(r.lookup go!"alarm").getD ∅ = ∅⌝ }}
    (App (Val (a @!! go.GoType.PointerType v3alarm.AlarmStore.ty @!! go!"Recover"))
      (Val #(alarmBkIface abl)))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ alarmBeOn a be ∗
      backend.bOpen γB qo ∗ backend.rbOwn γB (r.insert go!"alarm" ∅) }}

end spec

end EtcdGrove
end Perennial
