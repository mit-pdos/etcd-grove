/-
## `(*authStore).RoleGet(r)`

**Users.** `applierV3backend.RoleGet` (`apply/backend.go:231`), behind `authApplierV3.RoleGet`'s check (an administrator, or a user with the role: `HasRole`). Snippet: `examples/specreq/auth/admin.go` (`ReqAdminSteps`).

**Proof sketch.** `as.be.GetRole(name)` (4b); absent: `ErrRoleNotFound`, also for `root` when no role `root` is stored (W0's model answers a list there: requested of W0, `req/go_etcd_io_etcd_api_v3.md`, "from 3d", item 6; **until it changes, this spec is false at that input**); `root` stored: `rootPerm`; else the permissions copied. The admin step's state is recorded at index `i + 1` (`authCur`), every
view at it when the call returns.

**Changes.** Restated over `admStep`. The old per-mode verdicts (`adminOut M hs`) are W0's `authStep` effect at
the writer's state (`admStep`), with no mode index.

**Margin.** Order of the permissions.
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

/-- **`as.RoleGet(r)`** by the writer, for a request `r` asking `.roleGet name`: W0's effect of
the request at the store's state (`admStep`), recorded as the next state, and the reply. -/
def authStore.RoleGet.spec : Prop :=
  ∀ (st r : Loc) (name : GoString),
    AdminTriple (GF := GF) (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"RoleGet")) (Val #r)) (authReqAt r (.roleGet name)) st (.roleGet name)

end spec
end Auth
end EtcdGrove
end Perennial
