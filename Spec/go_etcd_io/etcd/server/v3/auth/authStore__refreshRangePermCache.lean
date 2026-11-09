/-
## `(*authStore).refreshRangePermCache(tx)` (internal helper)

**Users.** Every admin step that changes users or roles, `AuthEnable`, `Recover`, `NewAuthStore`.

**Proof sketch.** `rangePermCacheMu.Lock()`; a fresh map; `tx.UnsafeGetAllUsers()` (4b: `a`'s users); for each, `getMergedPerms(tx, name)` (its spec: an entry, never `nil` for a listed user); the map replaced (the cache view moves to `a`: `cacheOwn`, the writer's); `Unlock`.

**Changes.** The old spec restated over `Api.lean`'s and `Internal.lean`'s vocabulary.

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

/-- **`as.refreshRangePermCache(tx)`**: the cache rebuilt from the transaction's state. -/
def authStore.refreshRangePermCache.spec : Prop :=
  ∀ (st : Loc) (tx : GoInterface) (a a0 : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ cacheOwn st a0 ∗ txAt tx a ∗ ⌜validPerms a⌝ }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"refreshRangePermCache")) (Val #tx))
  {{ RET #(); cacheOwn st a ∗ txAt tx a }}

end spec
end Auth
end EtcdGrove
end Perennial
