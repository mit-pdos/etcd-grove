/-
## `(*authStore).Revision()`

**Users.** `isOpPermitted`, `Authenticate`, `authInfoFromToken`, `AuthInfoFromTLS`, `WithRoot`, the
metrics reporter (this package); `doSerialize`'s re-check, `Authenticate`'s loop, the lease checks
(`v3_server.go:575,601,608,719,752,779,881,1053`, 2c); `applierV3backend.AuthStatus` (3a). Snippet:
`examples/specreq/auth/admin.go` (`ReqRevisionBumped`).

**Proof sketch.** `atomic.LoadUint64(&as.revision)` under the atomic's invariant: its value is the
revision of the history's last state, or of the one before it during `Recover` (the backend swapped,
`setRevision` not yet run); both at or after every `authLb`.

**Changes.** The old mode verdict (`revisionVerdict M`) restated as a recorded state's revision.
**Two equal reads** say that the states they were read at have the same revision, so (the history is
a chain of admin steps, `authAt_reach`, and every admin change of the users or roles bumps the
revision, W0's `authStep`) the same users and roles. They do **not** say that a permission check
made between them was at either state: the check's backend and cache views may be one step behind
the atomic (`nonissues/etcd-auth-revision-before-visible.md`).

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.Api

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

/-- **`as.Revision()`**: the revision of a recorded state at or after the lower bound `i0`. No
lock (an atomic load). -/
def authStore.Revision.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i0 : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authLb γa i0 }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"Revision")) (Val #()))
  {{ (r : w64), RET #r; ∃ (j : Nat) (a : AuthState), ⌜i0 ≤ j ∧ uint.nat r = a.rev⌝ ∗ authAt γa j a }}

end spec
end Auth
end EtcdGrove
end Perennial
