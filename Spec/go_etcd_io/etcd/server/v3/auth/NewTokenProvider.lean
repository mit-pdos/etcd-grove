/-
## `NewTokenProvider(lg, tokenOpts, indexWaiter, TokenTTL)`

**Users.** `NewServer` (`server.go:~360`, 2e), with `cfg.AuthToken`, `s.applyWait.Wait` and
`cfg.TokenTTL`. Snippet: `examples/specreq/auth/boot.go` (`ReqBoot`).

**Proof sketch.** `decomposeOpts` (its spec: an error, `ErrInvalidAuthOpts`); by kind: `simple`
(`newTokenProviderSimple`: the waiter, the TTL; its contract from the waiter's `waiterOk`, the map's
lock invariant: each token's user with `tokenUser γ`, from the `authnCtx` of its assignment; no
thread token: the TTL keeper goroutine `enable` starts, `go t.simpleTokenKeeper.run()`
(`simple_token.go:188`), runs on its fork's own token), `jwt`
(`newTokenProviderJWT`, assumed: its tokens are `jwtTokOk γ opts`'s), `""` (`newTokenProviderNop`:
never accepts or assigns a token); any other: `ErrInvalidAuthOpts`.

**Changes.** The old spec (per kind, `tokenProviderOk`) restated over W0's `tokenUser`.
Verify round (A9 3d F7): the waiter gated on `R` (`waiterOk iw R`, carried by `tokenProviderAt`):
the server's waiter, `srv.applyWait.Wait`, works only after `start()`, so `NewServer` could not give
the ungated premise; the provider calls it only in `info`, which `AuthInfoFromCtx` reaches with `□ R`
(`R := srvStarted`). The error is the global's value (`errIs`, the sentinel encoding).
Changes: verify-round (server-core's RR4 request): no `threadTok` in the premise (it was kept on
success for the TTL keeper, given back on error). No path needs one: the keeper is a `go` of its
own (`simple_token.go:188`), whose fork gives it a fresh token, and the constructors only allocate.
Dropping it is stronger for the caller than returning it (`NewServer` keeps its token throughout).

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

/-- **`NewTokenProvider(lg, opts, iw, ttl)`**: an error for options it does not accept, or a provider of the cluster `γ`'s tokens, able to issue root
tokens unless it is the simple one. -/
def NewTokenProvider.spec : Prop :=
  ∀ (lg : Loc) (opts : GoString) (iw : GoFunc) (ttl : w64) (γ : Cluster) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ waiterOk iw R ∗
      □ (⌜optsKind opts = go!"jwt"⌝ -∗ jwtTokOk γ opts) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewTokenProvider)) (Val #lg))
      (Val #opts)) (Val #iw)) (Val #ttl))
  {{ (tp : GoInterface) (err : GoInterface), RET (PairV #tp #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ (errIs .invalidAuthOpts err ∨ ⌜optsKind opts = go!"jwt"⌝)) ∨
      (⌜err = GoInterface.nil⌝ ∗ tokenProviderAt tp γ R (decide (optsKind opts ≠ go!"simple"))) }}

end spec
end Auth
end EtcdGrove
end Perennial
