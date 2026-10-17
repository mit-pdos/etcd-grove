/-
`EtcdServer.Downgrade` (`v3_server.go`; unchanged by etcd#22589, the caller of the three handlers it
changes). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/BaseDowngrade.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseDowngrade

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.Downgrade(ctx, r)`** (the `Maintenance.Downgrade` RPC's server method), with the rights
`EP`, `CP` to propose a downgrade enable / cancel: no panic, whatever the action and the cluster
version; `VALIDATE` (0) is `downgradeValidate` and proposes nothing, `ENABLE` (1) is
`downgradeEnable` (no cancel), `CANCEL` (2) is `downgradeCancel` (no enable), any other action
`ErrUnknownMethod`. -/
abbrev EtcdServer.Downgrade.spec : Prop :=
  ∀ (s l r : Loc) (act : w32) (ver : GoString) (ctx : GoInterface) (EP CP : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvDowngradeOk s l EP CP ∗ srvLgReader s ∗ dgErrVar go_etcd_io.etcd.server.v3.etcdserver.errors.ErrUnknownMethod ∗
      structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeRequest go!"Action" r ↦□ act ∗
      structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeRequest go!"Version" r ↦□ ver ∗ EP ∗ CP }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Downgrade")) (Val #ctx))
      (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLgReader s ∗
      ((⌜act = W32 0⌝ ∗ dgValidatePost ver resp err ∗ EP ∗ CP) ∨
        (⌜act = W32 1⌝ ∗ dgEnablePost ver EP resp err ∗ CP) ∨
        (⌜act = W32 2⌝ ∗ dgCancelPost CP resp err ∗ EP) ∨
        (⌜act ≠ W32 0 ∧ act ≠ W32 1 ∧ act ≠ W32 2 ∧ resp = null⌝ ∗
          dgErrIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrUnknownMethod err ∗ EP ∗ CP)) }}

end spec

end EtcdGrove
end Perennial
