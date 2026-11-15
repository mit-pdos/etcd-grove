/-
## `(*simpleTokenTTLKeeper).addSimpleToken(token)` (internal helper)

**Users.** `tokenSimple.assignSimpleTokenToUser`, `info`, `invalidateUser` (under `simpleTokensMu`).

**Proof sketch.** A map operation on `tm.tokens` (held under the lock: `keeperTokens`): the token added (with a deadline `time.Now() + TTL`).

**Changes.** New (round 1, review S6: per (type, method); the old proofs' lemmas in `Proof/.../auth/TokenSimple*.lean`, `TokenKeeperRun.lean`, `TokenNop.lean`, `PermSorter.lean`).

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

/-- **`tm.addSimpleToken(tok)`** under the lock: the token added (with a deadline `time.Now() + TTL`). -/
def simpleTokenTTLKeeper.addSimpleToken.spec : Prop :=
  ∀ (tm : Loc) (S : GoString → Prop) (tok : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ keeperTokens tm S }}
    (App (Val (tm @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper.ty @!! go!"addSimpleToken")) (Val #tok))
  {{ RET #(); keeperTokens tm (fun x => S x ∨ x = tok) }}

end spec
end Auth
end EtcdGrove
end Perennial
