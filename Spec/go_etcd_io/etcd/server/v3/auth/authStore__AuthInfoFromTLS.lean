/-
## `(*authStore).AuthInfoFromTLS(ctx)` (assumed: translated names only)

**Users.** `EtcdServer.AuthInfoFromCtx`'s fallback with `ClientCertAuthEnabled`
(`v3_server.go:1214`, 2c). Snippet: `examples/specreq/auth/token.go` (`ReqCertUser`).

**Why true** (`auth/store.go:1000-1042`; the body is not translated: the peer's
`credentials.TLSInfo` and the x509 chains are axiomatized types): `peer.FromContext`; no peer, no auth
info, or not a `credentials.TLSInfo` (the fork's checked assertion): `nil`; the first non-empty
verified chain's leaf's common name, with `as.Revision()` (a recorded state's revision, its spec);
`metadata.FromIncomingContext` failing or a `grpcgateway-accept` key: `nil`; no chain: `nil`.
`ctxCertUser ctx c` is exactly that reading (2a's boundary). No panic.

**Changes.** The old axiom (any context, any `AuthInfo`) restated: the user is the context's
certificate's (`ctxCertUser`), the revision a recorded state's. The principal of a request with a
certificate and no token is then its common name, which 2a's and W0's principal must include
(`req/`: 2b's round-1 finding).

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

/-- **`as.AuthInfoFromTLS(ctx)`**: `nil` for a context without a TLS client identity, else an
`AuthInfo` naming its common name, at a recorded state's revision. -/
def authStore.AuthInfoFromTLS.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i0 : Nat) (ctx : GoInterface)
    (c : Option GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authLb γa i0 ∗ Context.ctxOk ctx ∗ ctxCertUser ctx c }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"AuthInfoFromTLS")) (Val #ctx))
  {{ (ai : Loc), RET #ai;
      ⌜ai = null ∧ c = none⌝ ∨
      ∃ (cn : GoString) (rev : w64) (j : Nat) (a : AuthState), ⌜c = some cn ∧ i0 ≤ j ∧ uint.nat rev = a.rev⌝ ∗
        authAt γa j a ∗ authInfoAt ai DFrac.discard cn rev }}

end spec
end Auth
end EtcdGrove
end Perennial
