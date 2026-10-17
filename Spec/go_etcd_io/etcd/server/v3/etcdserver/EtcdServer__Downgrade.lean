/-
`(*EtcdServer).Downgrade(ctx, r)` (`v3_server.go`: the maintenance service's `Downgrade`). Lean-first (the downgrade API, etcd-io/etcd#22575, 2026-10-16).
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

/-- **`s.Downgrade(ctx, r)`** (etcd-io/etcd#22575), any goroutine, for a request `r` (read only),
with the logger's reader slot: **no panic, whatever the action and whether or not the cluster
version is known** (before the PR, `ENABLE` and `CANCEL` panicked before it was known,
etcd-io/etcd#22574). `ErrClusterVersionUnavailable` and no response before the version is known,
never when the caller knew it was (`known`: the witness in the premise); `VALIDATE` may first
answer the format's error, `ErrUnknownMethod` for an unknown action; else the action's error or a
response, owned, once the version is known (`dgOutcome γcv known false`). -/
abbrev EtcdServer.Downgrade.spec : Prop :=
  ∀ (s l : Loc) (γcv : GName) (known : Bool) (ctx : GoInterface) (r : Loc)
    (act : go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeRequest_DowngradeAction) (ver : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      clusterVersionAt s γcv ∗ srvVersionOk s γcv ∗ srvDgErrVars ∗ version.dgErrVars ∗
      (if known then monoNatLbOwn γcv 1 else True) ∗
      srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝ ∗ srvLgReader s ∗ dgRequestIs r act ver }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Downgrade")) (Val #ctx)) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      srvLgReader s ∗ dgOutcome γcv known false resp err }}

end spec

end EtcdGrove
end Perennial
