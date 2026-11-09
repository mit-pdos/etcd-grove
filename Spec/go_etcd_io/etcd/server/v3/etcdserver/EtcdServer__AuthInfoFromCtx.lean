/-
## `(*EtcdServer).AuthInfoFromCtx(ctx)`

**Users.** `processInternalRaftRequestOnce`, `doSerialize`, `requireAuthInfo`, the lease checks
(`v3_server.go`); the gRPC interceptors and the watch server (2a, 2b: `isWatchPermitted`). Snippet:
`examples/specreq/etcdserverreq/auth.go` (`ReqPrincipal`).

**Proof sketch.** `AuthStore().AuthInfoFromCtx(ctx)` (3d: the token's user and revision, `nil`, or
`ErrInvalidAuthToken`), then, if `nil` and the configuration's `ClientCertAuthEnabled`,
`AuthStore().AuthInfoFromTLS(ctx)` (3d: the certificate's common name). `reqPrin ctx who` is that
contract (its realization).

**Changes.** The old spec (`specs-ref`'s `EtcdServer__AuthInfoFromCtx.lean`, per auth mode)
restated over `reqPrin`.

**Margin.** The auth revision is not stated (the callers pass it on to the header or compare it).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The request's credentials**: an `AuthInfo` naming `who`'s user (at some auth revision),
`nil` (then `who` is none, or auth is disabled), or an invalid token's error (a refusal). -/
def EtcdServer.AuthInfoFromCtx.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ Context.ctxOk ctx ∗ reqPrin ctx who ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"AuthInfoFromCtx")) (Val #ctx))
  {{ (ai : Loc) (err : GoInterface), RET (PairV #ai #err); threadTok ∗
      ((⌜err = GoInterface.nil ∧ ai = null⌝) ∨
       (⌜err = GoInterface.nil⌝ ∗ ∃ (u : GoString) (rev : w64), ⌜who = some u⌝ ∗
          ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦□ u ∗
          ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦□ rev) ∨
       ⌜ai = null ∧ srvErrOf err .invalidAuthToken⌝) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
