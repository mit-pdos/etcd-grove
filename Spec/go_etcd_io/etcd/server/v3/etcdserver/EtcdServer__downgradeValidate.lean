/-
`(*EtcdServer).downgradeValidate(ctx, v)` (`v3_server.go`). Lean-first (the downgrade API, etcd-io/etcd#22575, 2026-10-16; unchanged by the PR, its guard the one the PR copies).
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

/-- `s.downgradeValidate(ctx, v)`, any goroutine: `ErrClusterVersionUnavailable` before the
cluster version is known (never when the caller knew it was, `known`); otherwise the format's or
the manager's error, or a response (`dgOutcome γcv known false`: the format error may come before the
version is read). -/
abbrev EtcdServer.downgradeValidate.spec : Prop :=
  ∀ (s : Loc) (γcv : GName) (known : Bool) (ctx : GoInterface) (v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      clusterVersionAt s γcv ∗ srvVersionOk s γcv ∗ srvDgErrVars ∗ version.dgErrVars ∗
      (if known then monoNatLbOwn γcv 1 else True) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"downgradeValidate")) (Val #ctx)) (Val #v))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); dgOutcome γcv known false resp err }}

end spec

end EtcdGrove
end Perennial
