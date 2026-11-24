/-
`(*v3alarm.AlarmStore).restore()` (`alarms.go`): translated with its body and proved
(prove-ps2-v3alarm, 2026-11-24; until then names-only, the trust boundary: D22 receiver epochs, S7c,
2026-10-23). Lean-first (no Rocq counterpart).
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
be`, `threadTok`: `GetAllAlarms`' one read transaction), the schema backend's pointer not nil (`ForceCommit`, a value method, loads `*abl`), **two write-back tokens** (`CreateAlarmBucket`'s
`Unlock` and `ForceCommit`'s commit each spend one) and **the alarm bucket's claim token**
(`rbClaimToks γB P (· = "alarm")`: the bucket unclaimed, so its readers see the writer's contents once its
part is idle, `backend.rtHeld_rbOwnIn_idle`; handed back): no error, the store's map `a.types` as it was,
the alarm bucket created (present and empty), **the part idle** (`rbOwnIn γB S`).

The body (proved, `Proof/.../v3alarm/AlarmStore__restore.lean`, over `schema.alarmBackend`'s methods,
translated with their bodies): `a.be.CreateAlarmBucket()` is `LockOutsideApply` (the backend open: a share
of `bOpen`), `UnsafeCreateBucket(Alarm)` (the alarm bucket created, empty if absent; a tracked bucket of the
table, `P.RB`, `P.has`), the deferred `Unlock` (one write-back token; the part idle after it);
`GetAllAlarms` reads the bucket through one read transaction (`ReadTx`, `RLock`, `UnsafeForEach`), its slot
borrowed from the pool by the caller's thread token, and sees it empty (the idle-read law: an idle
unclaimed bucket's readers' contents are the writer's), so no record to decode, no unmarshal error, and the
loop adds nothing to `a.types`; `ForceCommit` commits (the second write-back token; the part stays idle);
`restore` returns `nil`. It reads `a.be` and writes no
field of `a`: whoever holds a fraction of `a.be` and the map may call it (`Recover` under the
store's mutex, `NewAlarmStore` on the fresh store). (2026-11-01, the backend-auth-split stage:
until then the whole writer's half `rbOwn` and no reader resource. 2026-11-02, round 4: until then
no `P.RB` premise, false for a backend whose alarm bucket is untracked, whose part says nothing of
what bbolt stores there: Go loads the stored alarms or returns the unmarshal error,
`review-r4/alarmuntracked/alarm_test.go`. 2026-11-24, prove-ps2-v3alarm: until then one write-back
token, too few for the body's two write-backs, no claim token, without which the idle part says
nothing of what a reader sees, and no `abl ≠ null`; the ledger, 2026-11-24.) -/
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
      alarmBkLgAddr abl ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ ⌜abl ≠ null⌝ ∗
      alarmTypesAddr a ↦ tm ∗ tm ↦$ gm ∗
      backend.isBackend γB P W Pk be ∗ backend.bOpen γB qo ∗ backend.wbTok γB ∗ backend.wbTok γB ∗
      backend.bkRPool γB P be ∗ threadTok ∗
      backend.rbPart γB S r ∗ ⌜(r.lookup go!"alarm").getD ∅ = ∅⌝ ∗
      backend.rbClaimToks γB P (· = go!"alarm") }}
    (App (Val (a @!! go.GoType.PointerType v3alarm.AlarmStore.ty @!! go!"restore")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗
      alarmBeAddr a ↦{dq} alarmBkIface abl ∗ alarmTypesAddr a ↦ tm ∗ tm ↦$ gm ∗
      backend.bOpen γB qo ∗ backend.bkRPool γB P be ∗ threadTok ∗
      backend.rbOwnIn γB S (r.insert go!"alarm" ∅) ∗ backend.rbClaimToks γB P (· = go!"alarm") }}

end spec

end EtcdGrove
end Perennial
