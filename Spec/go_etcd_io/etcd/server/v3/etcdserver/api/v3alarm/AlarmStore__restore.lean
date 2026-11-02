/-
`(*v3alarm.AlarmStore).restore()` (`alarms.go`): names-only, the trust boundary (D22 receiver
epochs, S7c, 2026-10-23: `Recover` calls it, translated). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RdPool
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`a.restore()`** over a schema alarm backend `a.be` (at any fraction `dq`, read) wrapping the
real backend at `be` (`γB`, `P`, its contract `isBackend` at some `W`, `Pk`), whose alarm bucket is
empty or absent (a part of any bucket set `S` containing `alarm`, `rbPart γB S r`, says so; the
bucket tracked, `P.RB "alarm" = true`, so that the part's contents are what bbolt stores there, and
in the backend's table, `P.has mvcc.alarmBI`, schema's `Alarm`, so that it is among the backend's
ghost names), with a pooled reader's resource and the caller's thread token (`backend.bkRPool γB P
be`, `threadTok`: `GetAllAlarms`' one read transaction): no error, the store's map `a.types` as it
was, the alarm bucket created (present and empty), **the part idle** (`rbOwnIn γB S`).

Why it is true of the Go code (`restore`, `schema.alarmBackend`'s `CreateAlarmBucket`,
`GetAllAlarms`, `ForceCommit`, at the etcd pin `188113160`): `a.be.CreateAlarmBucket()` is
`LockOutsideApply` (the backend open: a share of `bOpen`), `UnsafeCreateBucket(Alarm)` (the part:
the alarm bucket created, empty if absent; a tracked bucket of the table, `P.RB`, `P.has`),
`Unlock` (one write-back: the token; after it the readers see the writer's contents, the Go
basis); `GetAllAlarms` reads the bucket through one read transaction (`ReadTx`, `UnsafeRange`), its
slot borrowed from the pool by the caller's thread token (the idle part: no record, so nothing to
decode, no unmarshal error, `restore` adds nothing to `a.types`); `ForceCommit` commits (its own
`Unlock` finds nothing pending: no write-back, the part still idle; its commit runs the backend's
hooks, `isBackend`); `restore` returns `GetAllAlarms`' error, `nil`. It reads `a.be` and writes no
field of `a`: whoever holds a fraction of `a.be` and the map may call it (`Recover` under the
store's mutex, `NewAlarmStore` on the fresh store). (2026-11-01, the backend-auth-split stage:
until then the whole writer's half `rbOwn` and no reader resource. 2026-11-02, round 4: until then
no `P.RB` premise, false for a backend whose alarm bucket is untracked, whose part says nothing of
what bbolt stores there: Go loads the stored alarms or returns the unmarshal error,
`review-r4/alarmuntracked/alarm_test.go`.) -/
abbrev v3alarm.AlarmStore.restore.spec : Prop :=
  ∀ (a abl lg be : Loc) (dq : DFrac) (γB : backend.BNames) (P : backend.BParams) (W Pk : IProp GF)
    (qo : Qp) (S : GoString → Prop) (r : GMap GoString backend.BktData) (tm : GoMap)
    (gm : GMap w32 GoMap),
  S go!"alarm" → P.RB go!"alarm" = true → P.has mvcc.alarmBI →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm ∗
      alarmBeAddr a ↦{dq} alarmBkIface abl ∗
      alarmBkBeAddr abl ↦□ (interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #be :
          GoInterface) ∗
      alarmBkLgAddr abl ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
      alarmTypesAddr a ↦ tm ∗ tm ↦$ gm ∗
      backend.isBackend γB P W Pk be ∗ backend.bOpen γB qo ∗ backend.wbTok γB ∗
      backend.bkRPool γB P be ∗ threadTok ∗
      backend.rbPart γB S r ∗ ⌜(r.lookup go!"alarm").getD ∅ = ∅⌝ }}
    (App (Val (a @!! go.GoType.PointerType v3alarm.AlarmStore.ty @!! go!"restore")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗
      alarmBeAddr a ↦{dq} alarmBkIface abl ∗ alarmTypesAddr a ↦ tm ∗ tm ↦$ gm ∗
      backend.bOpen γB qo ∗ backend.bkRPool γB P be ∗ threadTok ∗
      backend.rbOwnIn γB S (r.insert go!"alarm" ∅) }}

end spec

end EtcdGrove
end Perennial
