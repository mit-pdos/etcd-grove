/-
`(*v3alarm.AlarmStore).restore()` (`alarms.go`): names-only, the trust boundary (D22 receiver
epochs, S7c, 2026-10-23: `Recover` calls it, translated). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

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

/-- **`a.restore()`** over a schema alarm backend `a.be` (at any fraction `dq`, read) wrapping the
real backend at `be` (`γB`, `P`, its contract `isBackend` at some `W`, `Pk`), whose alarm bucket is
empty or absent (the tracked buckets' client half `rbOwn γB r` says so): no error, the store's map
`a.types` as it was, the alarm bucket created (present and empty).

Why it is true of the Go code (`restore`, `schema.alarmBackend`'s `CreateAlarmBucket`,
`GetAllAlarms`, `ForceCommit`, at the etcd pin `188113160`): `a.be.CreateAlarmBucket()` is
`LockOutsideApply` (the backend open: a share of `bOpen`), `UnsafeCreateBucket(Alarm)` (the tracked
buckets' half: the alarm bucket created, empty if absent, `KBReal.P`'s `RB`), `Unlock` (one
write-back: the token); `GetAllAlarms` reads the bucket through a read transaction (`ReadTx`,
`UnsafeRange`: no record, so nothing to decode, no error, `restore` adds nothing to `a.types`);
`ForceCommit` commits (its own `Unlock` finds nothing pending: no write-back; its commit runs the
backend's hooks, `isBackend`); `restore` returns `GetAllAlarms`' error, `nil`. It reads `a.be` and
writes no field of `a`: whoever holds a fraction of `a.be` and the map may call it (`Recover` under
the store's mutex, `NewAlarmStore` on the fresh store). -/
abbrev v3alarm.AlarmStore.restore.spec : Prop :=
  ∀ (a abl lg be : Loc) (dq : DFrac) (γB : backend.BNames) (P : backend.BParams) (W Pk : IProp GF)
    (qo : Qp) (r : GMap GoString backend.BktData) (tm : GoMap) (gm : GMap w32 GoMap),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm ∗
      alarmBeAddr a ↦{dq} alarmBkIface abl ∗
      alarmBkBeAddr abl ↦□ (interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #be :
          GoInterface) ∗
      alarmBkLgAddr abl ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
      alarmTypesAddr a ↦ tm ∗ tm ↦$ gm ∗
      backend.isBackend γB P W Pk be ∗ backend.bOpen γB qo ∗ backend.wbTok γB ∗
      backend.rbOwn γB r ∗ ⌜(r.lookup go!"alarm").getD ∅ = ∅⌝ }}
    (App (Val (a @!! go.GoType.PointerType v3alarm.AlarmStore.ty @!! go!"restore")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗
      alarmBeAddr a ↦{dq} alarmBkIface abl ∗ alarmTypesAddr a ↦ tm ∗ tm ↦$ gm ∗
      backend.bOpen γB qo ∗ backend.rbOwn γB (r.insert go!"alarm" ∅) }}

end spec

end EtcdGrove
end Perennial
