/-
## `(*simpleTokenTTLKeeper).stop()` (internal helper)

**Users.** `tokenSimple.disable`.

**Proof sketch.** `select` sending on `stopc` or receiving `donec`, then `<-donec` (the goroutine done; no token: it ran on its fork's).

**Changes.** New (round 1, review S6: per (type, method); the old proofs' lemmas in `Proof/.../auth/TokenSimple*.lean`, `TokenKeeperRun.lean`, `TokenNop.lean`, `PermSorter.lean`).
Verify-round (server-core's RR4 request): returns no `threadTok` (was the provider's reserved one).

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.Internal

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

/-- **`tm.stop()`** with the stop right: the keeper's goroutine is done when it returns. -/
def simpleTokenTTLKeeper.stop.spec : Prop :=
  ∀ (tm t : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ keeperAt tm t ∗ keeperStop tm }}
    (App (Val (tm @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper.ty @!! go!"stop")) (Val #()))
  {{ RET #(); True }}

end spec
end Auth
end EtcdGrove
end Perennial
