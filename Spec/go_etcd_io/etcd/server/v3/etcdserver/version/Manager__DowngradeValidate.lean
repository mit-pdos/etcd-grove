/-
`(*Manager).DowngradeValidate(ctx, targetVersion)` (`version.go`). Lean-first (the downgrade
API, etcd-io/etcd#22575, 2026-10-16).
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

/-- `m.DowngradeValidate(ctx, tv)`, any goroutine, for a manager over a server `si`
(`version.serverOk`), **once the cluster version is known** (the caller's `monoNatLbOwn γcv 1`: the
version it reads after the linearizable read is then not nil, and `allowedDowngradeVersion` can
dereference it), returns some error (`nil` when `tv` is the allowed target and no downgrade is in
progress; not stated). -/
abbrev version.Manager.DowngradeValidate.spec : Prop :=
  ∀ (m : Loc) (si : GoInterface) (γcv : GName) (ctx : GoInterface) (tv : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version ∗
      version.managerIs m si ∗ version.serverOk si γcv ∗ monoNatLbOwn γcv 1 ∗ version.dgErrVars }}
    (App (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.version.Manager.ty @!! go!"DowngradeValidate")) (Val #ctx)) (Val #tv))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
