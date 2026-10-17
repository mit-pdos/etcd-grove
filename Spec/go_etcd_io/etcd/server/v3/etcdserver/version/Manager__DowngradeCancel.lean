/-
`(*Manager).DowngradeCancel(ctx)` (`version.go`). Lean-first (the downgrade API,
etcd-io/etcd#22575, 2026-10-16).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.version.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.version.Assumptions]

/-- `m.DowngradeCancel(ctx)`, any goroutine, for a manager over a server `si` (whether or not the
cluster version is known: it reads only the downgrade info, never `nil`), returns some error
(`ErrNoInflightDowngrade` when no downgrade is enabled, the read's or the proposal's). -/
abbrev version.Manager.DowngradeCancel.spec : Prop :=
  ∀ (m : Loc) (si : GoInterface) (γcv : GName) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version ∗
      version.managerIs m si ∗ version.serverOk si γcv ∗ version.dgErrVars }}
    (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.version.Manager.ty @!! go!"DowngradeCancel")) (Val #ctx))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
