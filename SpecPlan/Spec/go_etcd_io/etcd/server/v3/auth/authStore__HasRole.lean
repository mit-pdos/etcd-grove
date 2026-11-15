/-
## `(*authStore).HasRole(user, role)`

**Users.** `authApplierV3.RoleGet`'s check (`apply/auth.go:235`, 3a), the writer. Snippet:
`examples/specreq/auth/check.go` (`ReqWriterCheck`).

**Proof sketch.** The batch transaction (4b's `authBatchTx.Lock`: `LockInsideApply` runs the
backend's post-lock hook from `Pre` to `Q`, `authBeHook`): the user read at the writer's `a`; absent: `false`
(a warning); else whether `role` is among its roles.

**Changes.** The old spec restated over the writer's state.

Integration I5: the post-lock hook (always taken here, so `Q` back). Re-review (N1): the current backend's hook,
`authBeCur γa be ∗ authBeHook be Pre Q` (was the store-indexed `authHook`).
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

/-- **`as.HasRole(user, role)`** by the writer: whether `user` has `role` at its state. -/
def authStore.HasRole.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i : Nat) (a : AuthState) (user role : GoString)
    (be : GoInterface) (Pre Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authCur γa i a ∗
      authBeCur γa be ∗ Pre ∗ authBeHook be Pre Q }}
    (App (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"HasRole")) (Val #user)) (Val #role))
  {{ (b : Bool), RET #b; authCur γa i a ∗ authBeCur γa be ∗ Q ∗
      ⌜b = true ↔ ∃ ur, a.users user = some ur ∧ role ∈ ur.roles⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
