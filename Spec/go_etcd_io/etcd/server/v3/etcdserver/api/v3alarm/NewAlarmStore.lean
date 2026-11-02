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
write, the reader's open share lent, D14f), and no error (the alarm bucket is empty: no stored
alarm to decode).

Why it is true of the Go code (`NewAlarmStore`, `restore`, `AlarmStore`'s methods, `schema`'s
`alarmBackend`, at the etcd pin): `restore` creates the alarm bucket (`LockOutsideApply`, `Unlock`:
one write-back, the token), reads every alarm (`GetAllAlarms`, a read transaction; a decoding
error is returned, no panic) into its map, and `ForceCommit`s (it commits first: no write-back).
`Get` reads the map under the store's mutex. `Activate`/`Deactivate` change the map under it and
put or delete the member's encoding in the alarm bucket (`MustPutAlarm`/`MustDeleteAlarm`:
`LockInsideApply`, the backend open, a share lent in `mvcc.bkRTx`, the frozen hook run under
`Pk`; the alarm bucket a hook bucket, the readers' view unchanged; `Unlock`, one write-back). The
put's key is not empty for an alarm type other than `NONE` (the contract's premise of `Activate`,
`nonissues/etcd-alarm-activate-none-zero-fatal.md`).

Over an empty alarm bucket (a part of any bucket set `S` containing `alarm`,
`backend.rbPart d.γB S r`, says so; 2026-11-01, the backend-auth-split stage: until then the whole
writer's half `rbOwn`, and an error arm the empty bucket excludes), `restore` loads no alarm and
returns no error: `CreateAlarmBucket` (`LockOutsideApply`, the bucket created, empty if absent,
`Unlock`: after it the readers see the writer's contents on every bucket, the Go basis, so the
part comes back **idle**, `rbOwnIn`, at `r.insert "alarm" ∅`), then `GetAllAlarms` through one read
transaction (`RLock`…`RUnlock`, its slot borrowed from the pool by the caller's thread token:
`backend.bkRPool d.γB d.P d.be ∗ threadTok`, given back) sees it empty, unmarshals nothing, no
error (`TestBksNewAlarmStoreIdle`, `TestBks2RestoreEmptyNoError`), then `ForceCommit` (nothing
pending: still idle). The bucket is in the backend's table (`d.P.has mvcc.alarmBI`: schema's
`Alarm`, `bucket{id: 4, name: "alarm"}`, as `UnsafeCreateBucket` takes it; 2026-11-01, E: so the
created bucket is among the backend's ghost names `γ.rbD`, as `rbOwnIn` of the result needs). So
the map is empty (`alarmEmpty a d.be`, 2026-11-01, J8a-5: the user's half of `a.types` and of its
map at `∅`, under which `Get` returns no alarm, `Get.spec`; until then the opaque token
`alarmFresh a`, traded for the apply contract). The apply contract is given outright: `Activate`,
the only writer of the map, needs the user's half (`alarmBeOn`, which the contract's write right
lends), so it cannot run while the user holds `alarmEmpty`. `Activate`/`Deactivate` write a
tracked bucket: they take and give back the tracked buckets' client half (`srvRestRW d.γB`, the
contract's `RW`, D22).

(D22 receiver epochs, S7c, 2026-10-23) The store's lock holds half of `a.be` (`alarmLockInv`), the
caller gets the other (`alarmBeOn a d.be`: `ab` wraps `d.be`); `Activate`/`Deactivate` read `a.be`
under the lock, so they write to the backend the caller's half names: the contract
(`alarmApplyOk`) is for whichever backend that is, at its batch lock and frozen hook, given a write
right lending that half; `Recover` (proved, `AlarmStore__Recover.lean`) moves both halves to a new
backend under the lock. Until S7c the contract was for `d` only, which `Recover` falsifies. -/
abbrev v3alarm.NewAlarmStore.spec : Prop :=
  ∀ (lg : Loc) (ab : GoInterface) (abl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
    (S : GoString → Prop) (r : GMap GoString backend.BktData),
  S go!"alarm" → d.P.has mvcc.alarmBI →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm ∗
      ⌜lg ≠ null⌝ ∗
      ⌜ab = interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.ty) #abl⌝ ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.alarmBackend go!"be" abl ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #d.be : GoInterface) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.alarmBackend go!"lg" abl ↦□ lg ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ backend.wbTok d.γB ∗
      backend.bkRPool d.γB d.P d.be ∗ threadTok ∗
      backend.rbPart d.γB S r ∗ ⌜(r.lookup go!"alarm").getD ∅ = ∅⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.NewAlarmStore)) (Val #lg))
      (Val #ab))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); ⌜err = GoInterface.nil ∧ a ≠ null⌝ ∗
      backend.bOpen d.γB qo ∗ backend.bkRPool d.γB d.P d.be ∗ threadTok ∗
      backend.rbOwnIn d.γB S (r.insert go!"alarm" ∅) ∗
      isAlarmStore a ∗ alarmEmpty a d.be ∗ alarmApplyOk a }}

end spec

end EtcdGrove
end Perennial
