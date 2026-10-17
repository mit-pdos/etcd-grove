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

/-- `s.restoreAlarms()`: an error, the field unchanged; or the alarm store `NewAlarmStore` made
(its lock, `isAlarmStore`, and the apply contract at any batch-lock invariant and hook, as
`v3alarm.NewAlarmStore.spec` gives) in `s.alarmStore`. -/
abbrev EtcdServer.restoreAlarms.spec : Prop :=
  ∀ (s lg : Loc) (be : GoInterface) (a0 : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ srvBeAddr s ↦□ be ∗ srvAlarmStoreAddr s ↦ a0 }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"restoreAlarms")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err ≠ GoInterface.nil⌝ ∗ srvAlarmStoreAddr s ↦ a0) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ a : Loc, ⌜a ≠ null⌝ ∗ srvAlarmStoreAddr s ↦ a ∗
        isAlarmStore a ∗ □ (∀ (γ : mvcc.StoreNames) (P : IProp GF) (f : val), apply.isAlarmStore a γ P f)) }}

end spec

end EtcdGrove
end Perennial
