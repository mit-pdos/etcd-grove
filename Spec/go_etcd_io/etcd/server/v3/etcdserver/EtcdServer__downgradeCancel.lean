/-
`EtcdServer.downgradeCancel` (`v3_server.go`; changed by etcd#22589). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`s.downgradeCancel(ctx)`** (`Downgrade`'s `CANCEL`), with the right `CP` to propose a
downgrade cancel. No panic. A `nil` cluster version gives `ErrClusterVersionUnavailable` with
nothing proposed (`CP` back); otherwise a response and `nil`, whatever the manager's
`DowngradeCancel` returned (its error is only logged: `issues/etcd-downgrade-cancel-error-dropped.md`). -/
abbrev EtcdServer.downgradeCancel.spec : Prop :=
  ∀ (s l : Loc) (ctx : GoInterface) (EP CP : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvDowngradeOk s l EP CP ∗ srvLgReader s ∗ CP }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"downgradeCancel")) (Val #ctx))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      srvLgReader s ∗ dgCancelPost CP resp err }}

end spec

end EtcdGrove
end Perennial
