/-
## `(*authStore).WithRoot(ctx)`

**Users.** The lessor's expiry loop (`server.go:881`, 2d's `revokeExpiredLeases`):
`s.LeaseRevoke(s.authStore.WithRoot(s.ctx), ...)`, whose principal must be `root` when auth is on;
the health checks (`api/etcdhttp/health.go:222,434`: a `Range` as root).
Snippet: `examples/specreq/auth/token.go` (`ReqWithRoot`).

**Proof sketch.** The flag (off: `ctx` unchanged). The simple provider (a type assertion on the
provider): `context.WithValue` of index `0` and a fresh prefix (`genTokenPrefix`; an error: `ctx`
unchanged); `assign(ctx', "root", Revision())` (`tokenProviderAt`'s contract at index `0`:
`rootTokOk` rules out a token assigned twice, which panics in `assignSimpleTokenToUser`; an error:
`ctx` unchanged); `metadata.New({token: tok})`, `metadata.NewIncomingContext(ctx, md)` (2a's
boundary: `ctxInMD ctx' (some md)`, the peer kept). `tokenUser γ tok "root"`: the provider's assigned
token, the realization's root tokens (index `0`, never an entry's index, W0's `tokenUser` must
include them: `req/go_etcd_io_etcd_api_v3.md`).

**Changes.** The old spec was proved with auth off only; it now holds at every mode, with the
premise `rootTokOk` (**decision for the user**: the simple provider, etcd's default, does not give
it, `nonissues/etcd-auth-withroot-token-collision-panic.md`; a fix on the fork, or a probabilistic
premise). Round 1 (review F5): kept; the fork fix (`assignSimpleTokenToUser` returning an error,
which `WithRoot` already maps to `ctx`) is an open question for the user; with it `rootTokOk`
goes.

Integration I5: the TLS clause was `□ (ctxCertUser ctx none -∗ ctxCertUser ctx' none)`, false for a
context with a TLS peer but no incoming metadata, or a gateway request (`ctxCertUser` is `none`
there, and `NewIncomingContext` adds metadata without `grpcgateway-accept`); now over the peer's
identity, `ctxPeerCN` (2a's boundary). 2c's round-1 item 2 (`reqPrin ctx' (some root) tls` when
auth is on) is met but for the errors that return `ctx` (a prefix or `assign` error), which the
code allows.
Second pass (server-core's request, A7-completeness F5): the token disjunct also gives
`Context.ctxValueAt ctx ctx' mdIncomingKey{}`: `ctx'` is `metadata.NewIncomingContext(ctx, md)`, a
`WithValue` of `ctx` itself at grpc's incoming-metadata key (the index and prefix values go only to
the provider's context), so the values other packages' laws track (4b's trace, otel's span:
`reqCtxOk`) carry over from `ctx`.

Verify round (A9 3d F5): `ctxToken`, `ctxCertUser`, `ctxPeerCN` are grpc's (`metadata.New`'s
token key has its one value: `tokKeysOk`).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Api
public import Spec.context.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Auth

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`as.WithRoot(ctx)`**: `ctx` itself, or a context carrying a token the cluster issued to
`root`, whose TLS identity is `ctx`'s peer's (none for a context without a TLS peer). -/
def authStore.WithRoot.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i0 : Nat) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authLb γa i0 ∗ threadTok ∗ rootTokOk γa ∗ Context.ctxOk ctx }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"WithRoot")) (Val #ctx))
  {{ (ctx' : GoInterface), RET #ctx'; threadTok ∗ Context.ctxOk ctx' ∗
      (⌜ctx' = ctx⌝ ∨
       ∃ tok : GoString, ctxToken ctx' (some tok) ∗ tokenUser γ tok rootUser ∗
         □ (∀ c, ctxPeerCN ctx c -∗ ctxCertUser ctx' c) ∗
         Context.ctxValueAt ctx ctx'
           (interface.mkOk google_golang_org.grpc.metadata.mdIncomingKey.ty
             #(zero_val google_golang_org.grpc.metadata.mdIncomingKey))) }}

end spec
end Auth
end EtcdGrove
end Perennial
