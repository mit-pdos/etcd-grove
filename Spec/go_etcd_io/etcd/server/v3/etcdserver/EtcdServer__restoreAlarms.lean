/-
`(*EtcdServer).restoreAlarms()` (`server.go`: `v3alarm.NewAlarmStore` over the server's backend,
stored in `s.alarmStore`). Lean-first (no Rocq counterpart); the server-construction unit, stage
N0 (2026-10-16, D13: `notes/decisions.md`), for `NewServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.restoreAlarms()` over the real backend `d` (`s.be`): an error, the field unchanged; or the
alarm store `NewAlarmStore` made (its lock, `isAlarmStore`, and the apply contract at the backend's
batch lock `Pk` and any frozen hook, as `v3alarm.NewAlarmStore.spec` gives; unit N4, 2026-10-17:
at any batch-lock invariant and hook until then, false) in `s.alarmStore`. -/
abbrev EtcdServer.restoreAlarms.spec : Prop :=
  ∀ (s lg : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp) (a0 : Loc) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
      srvBeAddr s ↦{dq} (interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be :
          GoInterface) ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ backend.wbTok d.γB ∗
      srvAlarmStoreAddr s ↦ a0 }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"restoreAlarms")) (Val #()))
  {{ (err : GoInterface), RET #err; backend.bOpen d.γB qo ∗
      srvBeAddr s ↦{dq} (interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be :
          GoInterface) ∗
      ((⌜err ≠ GoInterface.nil⌝ ∗ srvAlarmStoreAddr s ↦ a0) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ a : Loc, ⌜a ≠ null⌝ ∗ srvAlarmStoreAddr s ↦ a ∗
        isAlarmStore a ∗ □ (∀ (γ : mvcc.StoreNames) (f : GoFunc), ⌜γ.kb = some d⌝ -∗
          backend.plHookRO d.γB f -∗ ⌜f ≠ func.nil⌝ -∗ apply.isAlarmStore a γ Pk #f))) }}

end spec

end EtcdGrove
end Perennial
