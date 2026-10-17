/-
`auth.NewTokenProvider(lg, opts, indexWaiter, ttl)` (`store.go`): names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
Settled at unit N1 (2026-10-17): an axiom at the trust boundary
(`Proof/go_etcd_io/etcd/server/v3/auth/NewTokenProvider.lean`), true of the Go code.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `NewTokenProvider(lg, opts, iw, ttl)`: a token provider, or an error (an invalid `opts`): on
success the provider is not nil. It only stores the index waiter `iw` (`newTokenProviderSimple`;
the provider's `info` calls it later, which this contract does not speak of: whoever states the
provider's contract, `auth.tokenProviderOk`, takes `iw`'s). True of the Go code (`store.go`
`NewTokenProvider`, `decomposeOpts`, `simple_token.go`, `jwt.go`, `options.go`, `nop.go`, read at
unit N1): no path panics (`decomposeOpts`'s `strings.Split` has an element; the JWT key parsing
returns errors), every success returns a non-nil pointer (`*tokenSimple`, `*tokenJWT`,
`*tokenNop`); on the JWT path's error the interface holds a nil `*tokenJWT`, which the contract
does not describe. -/
abbrev auth.NewTokenProvider.spec : Prop :=
  ∀ (lg : Loc) (opts : GoString) (iw : GoFunc) (ttl : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜lg ≠ null⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewTokenProvider)) (Val #lg))
      (Val #opts)) (Val #iw)) (Val #ttl))
  {{ (tp err : GoInterface), RET (PairV #tp #err);
      ⌜err = GoInterface.nil → tp ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
