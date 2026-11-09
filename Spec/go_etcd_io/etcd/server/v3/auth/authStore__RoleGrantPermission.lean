/-
## `(*authStore).RoleGrantPermission(r)`

**Users.** `applierV3backend.RoleGrantPermission` (`apply/backend.go:223`). Snippet: `examples/specreq/auth/admin.go` (`ReqAdminSteps`).

**Proof sketch.** A nil `Perm`: `ErrPermissionNotGiven`; `isValidPermissionRange` false: `ErrInvalidAuthMgmt` (so every recorded state keeps `validPerms`); the role read (absent: `ErrRoleNotFound`); every permission of the same range replaced by the new one, `sort.Sort(permSlice)`, put, `commitRevision`, refresh. The admin step's state is recorded at index `i + 1` (`authCur`), every
view at it when the call returns.

**Changes.** Restated over `admStep`; the old premise on `Permission_Type_name` is the package's initialization (`isPkgInit`). The old per-mode verdicts (`adminOut M hs`) are W0's `authStep` effect at
the writer's state (`admStep`), with no mode index.

**Margin.** Which of the two validation errors, and when, is exact in the code (`authReqAt`'s `Perm` non-nil rules out the first); W0's model allows either at any state.
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

/-- **`as.RoleGrantPermission(r)`** by the writer, for a request `r` asking `.roleGrantPermission name perm`: W0's effect of
the request at the store's state (`admStep`), recorded as the next state, and the reply. -/
def authStore.RoleGrantPermission.spec : Prop :=
  ∀ (st r : Loc) (name : GoString) (perm : Perm),
    AdminTriple (GF := GF) (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"RoleGrantPermission")) (Val #r)) (authReqAt r (.roleGrantPermission name perm)) st (.roleGrantPermission name perm)

end spec
end Auth
end EtcdGrove
end Perennial
