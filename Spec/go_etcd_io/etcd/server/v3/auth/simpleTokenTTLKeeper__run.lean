/-
## `(*simpleTokenTTLKeeper).run()` (internal helper)

**Users.** `tokenSimple.enable` (`go tm.run()`).

**Proof sketch.** `time.NewTicker(simpleTokenTTLResolution)` (the package's, positive: `isPkgInit`); the loop: a tick: `time.Now()`, under `tm.mu` (`&t.simpleTokensMu`: `keeperTokens` and the provider's map) every expired token deleted (`deleteTokenFunc`, the provider's map; the keeper's map); `stopc`: return; the deferred `Stop` and `close(donec)` (no payload: the goroutine ends with the fork's own token, framed by `wp_fork`).

**Changes.** New (round 1, review S6: per (type, method); the old proofs' lemmas in `Proof/.../auth/TokenSimple*.lean`, `TokenKeeperRun.lean`, `TokenNop.lean`, `PermSorter.lean`).
Verify-round (server-core's RR4 request): `donec`'s close carries no `threadTok`.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Internal

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

/-- **`tm.run()`**, the keeper's goroutine: returns once stopped. -/
def simpleTokenTTLKeeper.run.spec : Prop :=
  ∀ (tm t : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ keeperAt tm t ∗ keeperRun tm }}
    (App (Val (tm @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec
end Auth
end EtcdGrove
end Perennial
