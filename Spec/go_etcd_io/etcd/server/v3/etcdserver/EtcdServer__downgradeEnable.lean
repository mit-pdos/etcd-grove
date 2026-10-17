/-
`(*EtcdServer).downgradeEnable(ctx, r)` (`v3_server.go`). Lean-first (the downgrade API, etcd-io/etcd#22575, 2026-10-16).
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

/-- **`s.downgradeEnable(ctx, r)`** (etcd-io/etcd#22575), any goroutine, for a request `r` (read
only), with the logger's reader slot: no panic, whether or not the cluster version is known.
`ErrClusterVersionUnavailable` and no response before the version is known, never when the caller
knew it was (`known`, the witness in the premise) (the PR's guard: before it,
`Manager.DowngradeEnable` dereferenced the `nil` version, etcd-io/etcd#22574); otherwise, once it
is known (`dgOutcome γcv known true`), the format's or the manager's error, or a response. -/
abbrev EtcdServer.downgradeEnable.spec : Prop :=
  ∀ (s l : Loc) (γcv : GName) (known : Bool) (ctx : GoInterface) (r : Loc)
    (act : go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeRequest_DowngradeAction) (ver : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      clusterVersionAt s γcv ∗ srvVersionOk s γcv ∗ srvDgErrVars ∗ version.dgErrVars ∗
      (if known then monoNatLbOwn γcv 1 else True) ∗
      srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝ ∗ srvLgReader s ∗ dgRequestIs r act ver }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"downgradeEnable")) (Val #ctx)) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      srvLgReader s ∗ dgOutcome γcv known true resp err }}

end spec

end EtcdGrove
end Perennial
