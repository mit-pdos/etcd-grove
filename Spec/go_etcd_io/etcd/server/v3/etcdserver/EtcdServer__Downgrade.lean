/-
`(*EtcdServer).Downgrade(ctx, r)` (`v3_server.go:1218-1290`): by the action, validate a target
version against the cluster's, enable a downgrade (the version monitor's adapter proposes a
`DowngradeInfoSet` through `raftRequest`), or cancel it; an unknown action: `ErrUnknownMethod`.

**Users**: v3rpc's `maintenanceServer.Downgrade` (`ms.d.Downgrade`, then `togRPCError` and
`hdr.fill`).

**Proof sketch** (names only in the translation: trusted): `convertToClusterVersion` (the
version's parse: `ErrWrongDowngradeVersionFormat`); `ClusterVersion.spec` (`nil`:
`ErrClusterVersionUnavailable`); `s.Version()`'s `DowngradeValidate`/`DowngradeEnable`/
`DowngradeCancel` (the `version` package's monitor over the server's adapter: a linearizable read,
`LinearizableReadNotify.spec`, and an internal request with no observable step, `irrAsks _ none`:
3h's `IrrBody.noop`-like downgrade info, which W0's model does not see); every error is a sentinel
(`version`'s three mapped ones, the server's) or a context's, with its shape. The response is
fresh, its header set (`&pb.DowngradeResponse{}`, then the server's header).

**Changes**: verify round (A8-completeness F5): new. The downgrade state is not in W0's model (no
client observes it but through `Status`), so the triple fires no update.

**Margin**: whether the downgrade was enabled is not said.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`Downgrade(ctx, r)`**: a response, or an error with its shape; no client-observable step. -/
def EtcdServer.Downgrade.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (p tls : Principal) (r : Loc) (dq : DFrac)
    (c : Proto.Content),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗
      Context.ctxOk ctx ∗ reqCtxOk ctx ∗ reqPrin ctx p tls ∗ threadTok ∗
      Proto.msgAt go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeRequest.ty r dq c }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"Downgrade")) (Val #ctx)) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      Proto.msgAt go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeRequest.ty r dq c ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ c', Proto.msgAt go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeResponse.ty
          resp (DFrac.own 1) c') ∨
       (⌜resp = null⌝ ∗ srvErrShape err)) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
