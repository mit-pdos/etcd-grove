/-
`(*alarmBackend).GetAllAlarms()` (`server/storage/schema/alarm.go:84`). Lean-first (no Rocq
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

/-- **`ab.GetAllAlarms()` of an idle, empty, unclaimed alarm bucket** over the real backend at `be`: with
an open share and the backend's pool of reader slots, the caller's thread token (`ReadTx().RLock()`
borrows a slot with it, `RUnlock` gives it back), the client's idle part of the alarm bucket at contents
`r` holding it empty or absent (`rbOwnIn γ (· = "alarm") r`), and the bucket's claim token (so it is not
claimed: the readers' contents of an unclaimed bucket with no write pending are the writer's,
`backend.rtHeld_rbOwnIn_idle`): no record, no error (`ms` empty: the visitor, which unmarshals each key, is
never called); every resource back. Go: `be.ReadTx()`, `RLock()`, `unsafeGetAllAlarms(tx)` (`UnsafeForEach`
of `Alarm`), the deferred `RUnlock()`. The empty-bucket case of the SpecPlan's
`alarmBackend.GetAllAlarms.spec` (`al = []`), which is the only one its caller (`AlarmStore.restore` on a
fresh or snapshot backend) needs. -/
abbrev schema.alarmBackend.GetAllAlarms.spec : Prop :=
  ∀ (abl : Loc) (γ : backend.BNames) (P : backend.BParams) (W Pk : IProp GF) (be : Loc) (qo : Qp)
    (r : GMap GoString backend.BktData),
  P.RB go!"alarm" = true → P.has mvcc.alarmBI → (r.lookup go!"alarm").getD ∅ = ∅ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.alarmBackend go!"be" abl ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #be : GoInterface) ∗
      backend.isBackend γ P W Pk be ∗ backend.bOpen γ qo ∗ backend.rdPool γ P be ∗ threadTok ∗
      backend.rbOwnIn γ (· = go!"alarm") r ∗ backend.rbClaimToks γ P (· = go!"alarm") }}
    (App (Val (abl @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.ty @!! go!"GetAllAlarms")) (Val #()))
  {{ (ms : GoSlice) (err : GoInterface), RET (PairV #ms #err); ⌜err = GoInterface.nil⌝ ∗
      ms ↦* ([] : List Loc) ∗ backend.bOpen γ qo ∗ threadTok ∗
      backend.rbOwnIn γ (· = go!"alarm") r ∗ backend.rbClaimToks γ P (· = go!"alarm") }}

end spec

end EtcdGrove
end Perennial
