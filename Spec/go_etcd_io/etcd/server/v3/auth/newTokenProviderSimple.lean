/-
`newTokenProviderSimple(lg, indexWaiter, TokenTTL)` (`server/auth/simple_token.go`): the simple
token provider's constructor, for `NewTokenProvider`. Lean-first (no Rocq counterpart); the auth
plan's E2g (2026-10-25). Until E2g its proof was `tokenSimple_new` (S5e, `TokenKeeperRun.lean`),
which takes a positive TTL and the index waiter's contract; this statement takes neither, so that
`NewTokenProvider`, whose TTL and waiter are its caller's, can call it: the provider's facts are
given for a positive TTL only, and its index waiter as the field's value (`tokenSimple_new`
derives the old statement).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.TokenSimpleAdmin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `newTokenProviderSimple(lg, iw, ttl)`: a provider `p` whose index waiter is `iw` (read-only);
for a positive TTL, under fresh names, the provider's read-only facts (`simpleOk`: its logger, not
nil, `zap.NewNop()`'s for a nil `lg`, and its mutex with the lock invariant: no token, no keeper),
the admin side's share (`simpleAdmin`, no keeper) and the authority over the rights to issue tokens
(`γf`, empty). For a TTL not positive nothing is promised beyond the waiter (the lock invariant
records a positive TTL, which the keeper's `run` needs). -/
abbrev auth.newTokenProviderSimple.spec : Prop :=
  ∀ (lg : Loc) (iw : GoFunc) (ttl : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.newTokenProviderSimple)) (Val #lg))
      (Val #iw)) (Val #ttl))
  {{ (p : Loc), RET #p; auth.tsF go!"indexWaiter" p ↦□ iw ∗
      (⌜sint.Z ttl ≤ 0⌝ ∨ ∃ γt γf : GName, auth.simpleOk p γt γf ∗ auth.simpleAdmin p ∗
        ghostMapAuth γf 1 (∅ : GMap GoString Unit)) }}

end spec

end EtcdGrove
end Perennial
