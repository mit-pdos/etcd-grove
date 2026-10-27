/-
`v3alarm.NewAlarmStore(lg, be)` (`alarms.go`): names-only. Lean-first (no Rocq counterpart); the
server-construction unit, stage N0 (2026-10-16, D13: `notes/decisions.md`), for `NewServer`; an
axiom at the trust boundary since unit N4 (2026-10-17, D14d/D14f), why it is true of the Go code
below.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`NewAlarmStore(lg, ab)`** over schema's alarm backend `ab` wrapping the real backend `d`
(`NewAlarmBackend`'s result): an alarm store (its lock, `isAlarmStore`; the apply contract at the
backend's batch lock `Pk` and any frozen post-lock hook `f`, D14d, one write-back token per
write, the reader's open share lent, D14f), or an error (an undecodable stored alarm).

Why it is true of the Go code (`NewAlarmStore`, `restore`, `AlarmStore`'s methods, `schema`'s
`alarmBackend`, at the etcd pin): `restore` creates the alarm bucket (`LockOutsideApply`, `Unlock`:
one write-back, the token), reads every alarm (`GetAllAlarms`, a read transaction; a decoding
error is returned, no panic) into its map, and `ForceCommit`s (it commits first: no write-back).
`Get` reads the map under the store's mutex. `Activate`/`Deactivate` change the map under it and
put or delete the member's encoding in the alarm bucket (`MustPutAlarm`/`MustDeleteAlarm`:
`LockInsideApply`, the backend open, a share lent in `mvcc.bkRTx`, the frozen hook run under
`Pk`; the alarm bucket a hook bucket, the readers' view unchanged; `Unlock`, one write-back). The
put's key is not empty for an alarm type other than `NONE` (the contract's premise of `Activate`,
`issues/etcd-alarm-activate-none-zero-fatal.md`).

Over an empty alarm bucket (the tracked buckets' half `backend.rbOwn d.γB r` says so, D22,
2026-10-23; until then the opaque token `bkFresh d.γB "alarm"`, D14i, 2026-10-17: the creation
needs the half, given back with the bucket present and empty), `restore` loads no alarm: the map is empty, and stays so until `Activate`, which only the apply contract calls; so the
store is fresh (`alarmFresh a`), `Get` returning an empty slice under it, and the apply contract
is given up for the token. `Activate`/`Deactivate` write a tracked bucket: they take and give back
the tracked buckets' client half (`srvRestRW d.γB`, the contract's `RW`, D22).

(D22 receiver epochs, S7c, 2026-10-23) The store's lock holds half of `a.be` (`alarmLockInv`), the
caller gets the other (`alarmBeOn a d.be`: `ab` wraps `d.be`); `Activate`/`Deactivate` read `a.be`
under the lock, so they write to the backend the caller's half names: the contract
(`alarmApplyOk`) is for whichever backend that is, at its batch lock and frozen hook, given a write
right lending that half; `Recover` (proved, `AlarmStore__Recover.lean`) moves both halves to a new
backend under the lock. Until S7c the contract was for `d` only, which `Recover` falsifies. -/
abbrev v3alarm.NewAlarmStore.spec : Prop :=
  ∀ (lg : Loc) (ab : GoInterface) (abl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
    (r : GMap GoString backend.BktData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm ∗
      ⌜lg ≠ null⌝ ∗
      ⌜ab = interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.ty) #abl⌝ ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.alarmBackend go!"be" abl ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #d.be : GoInterface) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.alarmBackend go!"lg" abl ↦□ lg ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ backend.wbTok d.γB ∗
      backend.rbOwn d.γB r ∗ ⌜(r.lookup go!"alarm").getD ∅ = ∅⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.NewAlarmStore)) (Val #lg))
      (Val #ab))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); backend.bOpen d.γB qo ∗
      backend.rbOwn d.γB (r.insert go!"alarm" ∅) ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil ∧ a ≠ null⌝ ∗ isAlarmStore a ∗
        alarmBeOn a d.be ∗ alarmFresh a ∗ apply.alarmGetIs a (alarmFresh a) true ∗
        □ (alarmFresh a -∗ alarmApplyOk a)) }}

end spec

end EtcdGrove
end Perennial
