/-
`EtcdServer.downgradeEnable` (`v3_server.go`; changed by etcd#22589). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`s.downgradeEnable(ctx, r)`** (`Downgrade`'s `ENABLE`), with the right `EP` to propose a
downgrade enable. No panic, whatever the cluster version (`nil` included, at either of the two
reads: the manager's validation and the response's). The response's read cannot be `nil` once the
manager's was not (`clusterVersionOk`'s monotonicity, which the adapter's read shares,
`srvCVR`): the PR's second guard is never taken, so a committed enable is never answered with
`ErrClusterVersionUnavailable`. The outcomes:
- the target `r.Version` does not convert: `ErrWrongDowngradeVersionFormat`, before anything else,
  nothing proposed (`EP` back);
- the manager's validation failed (the read, a `nil` cluster version: `ErrClusterVersionUnavailable`,
  a wrong target, a downgrade in progress): its error, nothing proposed (`EP` back);
- the enable was proposed (`EP` spent) and failed: its error;
- else a response (the cluster version) and `nil`. -/
abbrev EtcdServer.downgradeEnable.spec : Prop :=
  ∀ (s l r : Loc) (ver : GoString) (ctx : GoInterface) (EP CP : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvDowngradeOk s l EP CP ∗ srvLgReader s ∗
      structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeRequest go!"Version" r ↦□ ver ∗ EP }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"downgradeEnable")) (Val #ctx)) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      srvLgReader s ∗ dgEnablePost ver EP resp err }}

end spec

end EtcdGrove
end Perennial
