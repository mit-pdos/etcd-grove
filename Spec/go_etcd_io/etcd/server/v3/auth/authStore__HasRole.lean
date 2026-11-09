/-
## `(*authStore).HasRole(user, role)`

**Users.** `authApplierV3.RoleGet`'s check (`apply/auth.go:235`, 3a), the writer. Snippet:
`examples/specreq/auth/check.go` (`ReqWriterCheck`).

**Proof sketch.** The batch transaction (4b): the user read at the writer's `a`; absent: `false`
(a warning); else whether `role` is among its roles.

**Changes.** The old spec restated over the writer's state.

**Margin.** None.
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

/-- **`as.HasRole(user, role)`** by the writer: whether `user` has `role` at its state. -/
def authStore.HasRole.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i : Nat) (a : AuthState) (user role : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authCur γa i a }}
    (App (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"HasRole")) (Val #user)) (Val #role))
  {{ (b : Bool), RET #b; authCur γa i a ∗
      ⌜b = true ↔ ∃ ur, a.users user = some ur ∧ role ∈ ur.roles⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
