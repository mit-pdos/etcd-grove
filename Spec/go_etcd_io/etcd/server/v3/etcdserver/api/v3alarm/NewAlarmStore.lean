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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
`issues/etcd-alarm-activate-none-zero-fatal.md`). -/
abbrev v3alarm.NewAlarmStore.spec : Prop :=
  ∀ (lg : Loc) (ab : GoInterface) (abl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm ∗
      ⌜lg ≠ null⌝ ∗
      ⌜ab = interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.ty) #abl⌝ ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.alarmBackend go!"be" abl ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #d.be : GoInterface) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.alarmBackend go!"lg" abl ↦□ lg ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ backend.wbTok d.γB }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.NewAlarmStore)) (Val #lg))
      (Val #ab))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); backend.bOpen d.γB qo ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil ∧ a ≠ null⌝ ∗ isAlarmStore a ∗
        □ (∀ (γ : mvcc.StoreNames) (f : GoFunc), ⌜γ.kb = some d⌝ -∗ backend.plHookRO d.γB f -∗
          ⌜f ≠ func.nil⌝ -∗ apply.isAlarmStore a γ Pk #f)) }}

end spec

end EtcdGrove
end Perennial
