/-
`(*EtcdServer).downgradeCancel(ctx)` (`v3_server.go`). Lean-first (the downgrade API, etcd-io/etcd#22575, 2026-10-16).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvDowngrade

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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.downgradeCancel(ctx)`** (etcd-io/etcd#22575), any goroutine: no panic.
`ErrClusterVersionUnavailable` and no response before the cluster version is known, never when the
caller knew it was (`known`) (the PR's guard: before it, the response's
`s.ClusterVersion().String()` dereferenced the `nil` version, etcd-io/etcd#22574); otherwise a
response, **whatever the cancel returned** (the manager's error is only logged:
`issues/etcd-downgrade-cancel-error-dropped.md`; this is what the code does, not what it should). -/
abbrev EtcdServer.downgradeCancel.spec : Prop :=
  ∀ (s l : Loc) (γcv : GName) (known : Bool) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      clusterVersionAt s γcv ∗ srvVersionOk s γcv ∗ srvDgErrVars ∗ version.dgErrVars ∗
      (if known then monoNatLbOwn γcv 1 else True) ∗
      srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝ }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"downgradeCancel")) (Val #ctx))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜resp = null ∧ known = false⌝ ∗ dgErrIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrClusterVersionUnavailable err) ∨
      (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ dgResp resp ∗ monoNatLbOwn γcv 1) }}

end spec

end EtcdGrove
end Perennial
