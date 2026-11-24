/-
`(*alarmBackend).CreateAlarmBucket()` (`server/storage/schema/alarm.go:45`). Lean-first (no Rocq
counterpart); for `AlarmStore.restore` (prove-ps2-v3alarm, 2026-11-24).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RdPool
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`ab.CreateAlarmBucket()`** of the alarm backend `ab` over the real backend at `be` (`γ`, `P`, its
contract `isBackend` at some `W`, `Pk`), the alarm bucket tracked (`P.RB`), in the table (`P.has`, schema's
`Alarm`) and in a part of any bucket set `S` containing it (`rbPart γ S r`, at whatever `r` says of it), at
one write-back token and an open share: the alarm bucket present, empty if it was absent, and the part
**idle**. Go: `be.BatchTx()`, `LockOutsideApply`, `UnsafeCreateBucket(Alarm)` (bbolt's `CreateBucket`, or
`ErrBucketExists`, which the backend ignores), the deferred `Unlock` (a write-back: the token, and the
readers see the writer's contents on `S` after it). The SpecPlan's `alarmBackend.CreateAlarmBucket.spec`
over the backend's own vocabulary. -/
abbrev schema.alarmBackend.CreateAlarmBucket.spec : Prop :=
  ∀ (abl : Loc) (γ : backend.BNames) (P : backend.BParams) (W Pk : IProp GF) (be : Loc) (qo : Qp)
    (S : GoString → Prop) (r : GMap GoString backend.BktData),
  S go!"alarm" → P.RB go!"alarm" = true → P.has mvcc.alarmBI →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.alarmBackend go!"be" abl ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #be : GoInterface) ∗
      backend.isBackend γ P W Pk be ∗ backend.bOpen γ qo ∗ backend.wbTok γ ∗ backend.rbPart γ S r }}
    (App (Val (abl @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.ty @!! go!"CreateAlarmBucket")) (Val #()))
  {{ RET #(); backend.bOpen γ qo ∗
      backend.rbOwnIn γ S (r.insert go!"alarm" ((r.lookup go!"alarm").getD ∅)) }}

end spec

end EtcdGrove
end Perennial
