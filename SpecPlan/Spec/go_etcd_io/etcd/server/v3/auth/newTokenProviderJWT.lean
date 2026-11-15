/-
## `newTokenProviderJWT(lg, optMap)` (assumed: translated names only)

**Users.** `NewTokenProvider` (`jwt`).

**Why true.** (`jwt.go`, untranslated: `golang-jwt`, `crypto`) the options parsed (`jwtOptions.ParseWithDefaults`, `Key()`): an error for missing or mismatched keys or an unknown method; else a `tokenJWT`: `info` verifies a token's signature with the key and returns its claims' user (`jwtTokOk γ opts`: then a token the cluster issued to that user), `assign` signs `(username, revision)` (a token of `name`: the same premise), `genTokenPrefix` `""`. It assigns no stored token, so root tokens do not collide. No panic.

**Changes.** The old axiom (post `True`) restated as the provider contract, over `jwtTokOk`.
Verify round: at any gate `R` (no waiter).

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.Internal
public import SpecPlan.Spec.go_uber_org.zap.Api

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

/-- **`newTokenProviderJWT(lg, m)`** for the options of `opts`: an error, or a provider of the
cluster's JWTs. -/
def newTokenProviderJWT.spec : Prop :=
  ∀ (lg m : Loc) (opts : GoString) (γ : Cluster) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ optsMapAt m opts ∗ jwtTokOk γ opts }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.newTokenProviderJWT)) (Val #lg)) (Val #m))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      ⌜err ≠ GoInterface.nil⌝ ∨
      (⌜err = GoInterface.nil⌝ ∗
        tokenProviderAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenJWT.ty) #p) γ R true) }}

end spec
end Auth
end EtcdGrove
end Perennial
