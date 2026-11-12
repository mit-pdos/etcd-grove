/-
## `(*EtcdServer).AuthInfoFromCtx(ctx)`

**Users.** `processInternalRaftRequestOnce`, `doSerialize`, `requireAuthInfo`, the lease checks
(`v3_server.go`); the gRPC interceptors and the watch server (2a, 2b: `isWatchPermitted`). Snippet:
`examples/specreq/etcdserverreq/auth.go` (`ReqPrincipal`).

**Proof sketch.** `AuthStore().AuthInfoFromCtx(ctx)` (3d: the token's user and revision, `nil`, or
`ErrInvalidAuthToken`), then, if `nil` and the configuration's `ClientCertAuthEnabled`,
`AuthStore().AuthInfoFromTLS(ctx)` (3d: the certificate's common name). `reqPrin ctx p tls` is that
contract (its realization): with auth enabled and a token, the token's user `p`; otherwise the
certificate's name `tls`, or `nil` (round 1: the principal depends on the auth flag at the check,
provability F7).

**Changes.** The old spec (`specs-ref`'s `EtcdServer__AuthInfoFromCtx.lean`, per auth mode)
restated over `reqPrin`.

**Margin.** The auth revision is not stated (the callers pass it on to the header or compare it).

Changes: verify-round (A7-provability F3, F5): see the verify round's repair: the context needs only its otel span (`reqCtxSpan`, any trace: the outer method's `EnsureTrace` installed one); the request message comes back with whatever header was set (`∃ h, irrOwnH r dq ir h`: the header is written before proposing).

Changes: verify-round (lease-auth's request): the call to 3d's `AuthInfoFromCtx` supplies `authGate γa R ∗ □ srvStarted s γ id` (the gate `NewAuthStore` gave, kept behind `isServer`), and `ctxToken`'s `tokKeysOk md` comes from the run's context (2a's `Grpc.rpcCtx_vals`; `ctxNoIncoming` contexts carry no metadata).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

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

/-- **The request's credentials**: an `AuthInfo` naming `p`'s or `tls`'s user (at some auth
revision), `nil` (no token with auth enabled, or auth disabled, and no certificate's name), or an
invalid token's error (a refusal). -/
def EtcdServer.AuthInfoFromCtx.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (p tls : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ Context.ctxOk ctx ∗ reqCtxSpan ctx ∗ reqPrin ctx p tls ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"AuthInfoFromCtx")) (Val #ctx))
  {{ (ai : Loc) (err : GoInterface), RET (PairV #ai #err); threadTok ∗
      ((⌜err = GoInterface.nil ∧ ai = null⌝) ∨
       (⌜err = GoInterface.nil⌝ ∗ ∃ (u : GoString) (rev : w64), ⌜p = some u ∨ tls = some u⌝ ∗
          ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦□ u ∗
          ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦□ rev) ∨
       (⌜ai = null⌝ ∗ srvErr err .invalidAuthToken ∗ srvErrShape err)) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
