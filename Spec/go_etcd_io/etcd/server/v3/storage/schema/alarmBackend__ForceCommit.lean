/-
`alarmBackend.ForceCommit()` (`server/storage/schema/alarm.go:104`, a value receiver). Lean-first (no
Rocq counterpart); for `AlarmStore.restore` (prove-ps2-v3alarm, 2026-11-24).
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

/-- **`ab.ForceCommit()`** of an alarm backend value `ab` over the real backend at `be`, at one write-back
token and an open share: the batch transaction committed (`backend.ForceCommit`, with no commit request:
`commitReq_true`); the open share back. Go: `s.be.ForceCommit()`. -/
abbrev schema.alarmBackend.ForceCommit.spec : Prop :=
  ∀ (ab : go_etcd_io.etcd.server.v3.storage.schema.alarmBackend) (γ : backend.BNames) (P : backend.BParams)
    (W Pk : IProp GF) (be : Loc) (qo : Qp),
  ab.be' = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
    #be →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      backend.isBackend γ P W Pk be ∗ backend.bOpen γ qo ∗ backend.wbTok γ }}
    (App (Val (ab @!! go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.ty @!! go!"ForceCommit"))
      (Val #()))
  {{ RET #(); backend.bOpen γ qo }}

end spec

end EtcdGrove
end Perennial
