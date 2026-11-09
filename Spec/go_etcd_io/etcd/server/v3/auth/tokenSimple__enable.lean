/-
## `(*tokenSimple).enable()` (internal helper)

**Users.** `tp_enable`, through `AuthEnable`, `Recover`, `NewAuthStore`.

**Proof sketch.** `simpleTokensMu.Lock()`; a keeper: nothing; a non-positive TTL replaced by `simpleTokenTTLDefault` (the package's, `isPkgInit`); a fresh keeper (`keeperAt`, its tokens empty) and `go keeper.run()` (its spec, with `keeperRun`: the provider's reserved `threadTok`, from the invariant); `Unlock`.

**Changes.** New (round 1, review S6: per (type, method); the old proofs' lemmas in `Proof/.../auth/TokenSimple*.lean`, `TokenKeeperRun.lean`, `TokenNop.lean`, `PermSorter.lean`).

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

/-- **`t.enable()`**: no panic, nothing a caller observes. -/
def tokenSimple.enable.spec : Prop :=
  ∀ (t : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleAt t γ }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenSimple.ty @!! go!"enable")) (Val #()))
  {{ RET #(); True }}

end spec
end Auth
end EtcdGrove
end Perennial
