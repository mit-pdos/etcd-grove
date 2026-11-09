/-
## `NewTokenProvider(lg, tokenOpts, indexWaiter, TokenTTL)`

**Users.** `NewServer` (`server.go:~360`, 2e), with `cfg.AuthToken`, `s.applyWait.Wait` and
`cfg.TokenTTL`. Snippet: `examples/specreq/auth/boot.go` (`ReqBoot`).

**Proof sketch.** `decomposeOpts` (its spec: an error, `ErrInvalidAuthOpts`); by kind: `simple`
(`newTokenProviderSimple`: the waiter, the TTL; its contract from the waiter's `waiterOk`, the map's
lock invariant: each token's user with `tokenUser γ`, from the `authnCtx` of its assignment; the
caller's `threadTok` kept for the TTL keeper goroutine `enable` starts), `jwt`
(`newTokenProviderJWT`, assumed: its tokens are `jwtTokOk γ opts`'s), `""` (`newTokenProviderNop`:
never accepts or assigns a token); any other: `ErrInvalidAuthOpts`.

**Changes.** The old spec (per kind, `tokenProviderOk`) restated over W0's `tokenUser`.

**Margin.** The simple provider's TTL is not stated (an expired token is refused: allowed).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Api
public import Spec.go_uber_org.zap.Api

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

/-- **`NewTokenProvider(lg, opts, iw, ttl)`**: an error for options it does not accept (the
caller's thread token given back), or a provider of the cluster `γ`'s tokens, able to issue root
tokens unless it is the simple one. -/
def NewTokenProvider.spec : Prop :=
  ∀ (lg : Loc) (opts : GoString) (iw : GoFunc) (ttl : w64) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ waiterOk iw ∗ threadTok ∗
      □ (⌜optsKind opts = go!"jwt"⌝ -∗ jwtTokOk γ opts) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewTokenProvider)) (Val #lg))
      (Val #opts)) (Val #iw)) (Val #ttl))
  {{ (tp : GoInterface) (err : GoInterface), RET (PairV #tp #err);
      (⌜err ≠ GoInterface.nil ∧ (err = errOf .invalidAuthOpts ∨ optsKind opts = go!"jwt")⌝ ∗
          threadTok) ∨
      (⌜err = GoInterface.nil⌝ ∗ tokenProviderAt tp γ (decide (optsKind opts ≠ go!"simple"))) }}

end spec
end Auth
end EtcdGrove
end Perennial
