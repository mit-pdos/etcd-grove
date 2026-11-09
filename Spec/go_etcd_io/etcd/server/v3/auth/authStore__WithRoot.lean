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
`root`, with no TLS identity if `ctx` had none. -/
def authStore.WithRoot.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i0 : Nat) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authLb γa i0 ∗ threadTok ∗ rootTokOk γa ∗ Context.ctxOk ctx }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"WithRoot")) (Val #ctx))
  {{ (ctx' : GoInterface), RET #ctx'; threadTok ∗ Context.ctxOk ctx' ∗
      (⌜ctx' = ctx⌝ ∨
       ∃ tok : GoString, ctxToken ctx' (some tok) ∗ tokenUser γ tok rootUser ∗
         □ (ctxCertUser ctx none -∗ ctxCertUser ctx' none)) }}

end spec
end Auth
end EtcdGrove
end Perennial
