/-
`newTokenProviderJWT(lg, optMap)` (`server/auth/jwt.go`): names-only, the JWT token provider's
constructor, for `NewTokenProvider`. Lean-first (no Rocq counterpart); the auth plan's E2g
(2026-10-25): an axiom at the trust boundary
(`Proof/go_etcd_io/etcd/server/v3/auth/newTokenProviderJWT.lean`), which replaces
`NewTokenProvider`'s own (unit N1, 2026-10-17), now proved over it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `newTokenProviderJWT(lg, m)`, over the options' map `m` (owned): some `*tokenJWT` and some
error; it returns. True of the Go code (`jwt.go` `newTokenProviderJWT`, `options.go`, read at the
etcd pin): a nil `lg` is replaced by `zap.NewNop()`; the options' parsing (`ParseWithDefaults`:
`strconv`, the signing method's lookup, `os.ReadFile` of the key files) and the key's (`Key()`:
`jwt`'s PEM parsers) return errors rather than panic (`edKey`'s two unchecked type assertions
hold: golang-jwt's `ParseEdPrivateKeyFromPEM`/`ParseEdPublicKeyFromPEM` return an `ed25519` key
or an error; the signing method's type switch only uses checked assertions); the map is only read
(lookups and a range over its keys). What the result is (a nil pointer with an error, a provider without one) is not stated:
`NewTokenProvider`'s contract does not speak of the JWT provider. -/
abbrev auth.newTokenProviderJWT.spec : Prop :=
  ∀ (lg m : Loc) (mm : GMap GoString GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ m ↦$ mm }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.newTokenProviderJWT)) (Val #lg)) (Val #m))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err); True }}

end spec

end EtcdGrove
end Perennial
