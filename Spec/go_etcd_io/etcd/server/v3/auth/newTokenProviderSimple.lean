/-
## `newTokenProviderSimple(lg, indexWaiter, TokenTTL)` (internal helper)

**Users.** `NewTokenProvider` (`simple`).

**Proof sketch.** A fresh `tokenSimple` with an empty token map (so every token it will hold is one an `authnCtx` assigned: `tokenUser γ`), the waiter (`waiterOk`: `isValidSimpleToken`'s receive), the TTL (`enable` replaces a non-positive one); the caller's `threadTok` kept for the TTL keeper goroutine `enable` starts (`go simpleTokenKeeper.run()`), which `disable` stops and waits for.

**Changes.** The old spec (`simpleOk`, its ghost map) restated as the provider contract. Verify
round (A9 3d F7): the waiter gated on `R`, which `info` needs (`□ R`).

**Margin.** Root tokens may collide: not `rootTokOk` (`rt = false`).
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

/-- **`newTokenProviderSimple(lg, iw, ttl)`**: a provider of the cluster's simple tokens. -/
def newTokenProviderSimple.spec : Prop :=
  ∀ (lg : Loc) (iw : GoFunc) (ttl : w64) (γ : Cluster) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ waiterOk iw R ∗ threadTok }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.newTokenProviderSimple)) (Val #lg))
      (Val #iw)) (Val #ttl))
  {{ (p : Loc), RET #p;
      tokenProviderAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenSimple.ty) #p) γ R false }}

end spec
end Auth
end EtcdGrove
end Perennial
