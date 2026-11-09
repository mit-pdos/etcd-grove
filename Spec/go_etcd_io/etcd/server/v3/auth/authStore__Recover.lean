/-
## `(*authStore).Recover(be)`

**Users.** `EtcdServer.applySnapshot` (`server.go:1127`, 2d), the writer, with the snapshot's backend
`schema.NewAuthBackend(lg, newbe)`. Snippet: `examples/specreq/auth/boot.go` (`ReqRecover`).

**Proof sketch.** `beMu.Lock()`, `as.be = be` (the linearization point: the snapshot's state `a'`
recorded as `i + 1`, `authReached`; the backend view moves; the old backend's share given back, its
readers' transactions still open, which the server's close of it waits for, 4a), `Unlock`; the new
backend's read transaction (a reader slot: `threadTok`): the flag, `setRevision` (the atomic view),
`refreshRangePermCache` (the cache view), `RUnlock`; `enabledMu.Lock()`, the flag (the flag view),
the provider's `enable()` if on.

**Changes.** The old spec (`authRecoverOk`, mode `on` only after `notes/snapshot-auth-on-plan.md`)
restated over W0's state at every mode: the snapshot's state follows the store's (`AuthReach`,
which 2d has from the cluster's history: the snapshot is at a later index).

**Margin.** The provider is not disabled when the snapshot's state has auth off (its tokens stay
valid in it; `AuthInfoFromCtx` reads the flag first).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Api

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

/-- **`as.Recover(be)`** by the writer: the snapshot backend's state `a'`, a successor of the
store's, recorded as its next state; the replaced backend's share given back. -/
def authStore.Recover.spec : Prop :=
  ∀ (st : Loc) (be : GoInterface) (γ : Cluster) (γa : AuthNames) (i : Nat) (a a' : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authCur γa i a ∗ threadTok ∗ authBackendAt be a' ∗
      authReached γ a' ∗ ⌜AuthReach a a' ∧ validPerms a'⌝ }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"Recover")) (Val #be))
  {{ RET #(); authCur γa (i + 1) a' ∗ threadTok ∗
      ∃ (be0 : GoInterface) (a0 : AuthState), authBackendAt be0 a0 }}

end spec
end Auth
end EtcdGrove
end Perennial
