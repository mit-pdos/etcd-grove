/-
## `(*authStore).lockedReadTx()` (internal helper)

**Users.** `isOpPermitted`, `IsAdminPermitted`, `CheckPassword`.

**Proof sketch.** `beMu.RLock()` (a reader slot of the caller's `threadTok`), `as.be` (the current backend, `beMu`'s invariant), its `ReadTx()` and `RLock()` (4b: the backend view, a recorded state at or after every `authLb`), `beMu.RUnlock()`: the transaction is of the backend current when it was locked; the server closes a replaced backend only after `Recover` returns, and that close waits for the read lock.

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

/-- **`as.lockedReadTx()`**: a locked read transaction of the backend view, at a recorded state at
or after `i0`; the caller's thread token lent to it until `RUnlock`. -/
def authStore.lockedReadTx.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i0 : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authLb γa i0 ∗ threadTok }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"lockedReadTx")) (Val #()))
  {{ (tx : GoInterface), RET #tx; ∃ (j : Nat) (a : AuthState), ⌜i0 ≤ j⌝ ∗ authAt γa j a ∗ rdTx γa tx j a }}

end spec
end Auth
end EtcdGrove
end Perennial
