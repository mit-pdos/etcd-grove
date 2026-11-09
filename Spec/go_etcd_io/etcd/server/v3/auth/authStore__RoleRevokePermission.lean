/-
## `(*authStore).RoleRevokePermission(r)`

**Users.** `applierV3backend.RoleRevokePermission` (`apply/backend.go:239`). Snippet: `examples/specreq/auth/admin.go` (`ReqAdminSteps`).

**Proof sketch.** The role read (absent: `ErrRoleNotFound`); the permissions of exactly the range filtered; none removed: `ErrPermissionNotGranted`; put, `commitRevision`, refresh. The admin step's state is recorded at index `i + 1` (`authCur`), every
view at it when the call returns.

**Changes.** Restated over `admStep`. The old per-mode verdicts (`adminOut M hs`) are W0's `authStep` effect at
the writer's state (`admStep`), with no mode index.

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

/-- **`as.RoleRevokePermission(r)`** by the writer, for a request `r` asking `.roleRevokePermission role key rangeEnd`: W0's effect of
the request at the store's state (`admStep`), recorded as the next state, and the reply. -/
def authStore.RoleRevokePermission.spec : Prop :=
  ∀ (st r : Loc) (role key rangeEnd : GoString),
    AdminTriple (GF := GF) (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"RoleRevokePermission")) (Val #r)) (authReqAt r (.roleRevokePermission role key rangeEnd)) st (.roleRevokePermission role key rangeEnd)

end spec
end Auth
end EtcdGrove
end Perennial
