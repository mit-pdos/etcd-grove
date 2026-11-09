/-
## `(*authStore).RoleDelete(r)`

**Users.** `applierV3backend.RoleDelete` (`apply/backend.go:247`). Snippet: `examples/specreq/auth/admin.go` (`ReqAdminSteps`).

**Proof sketch.** `root` with auth on: `ErrInvalidAuthMgmt`; the role read (absent: `ErrRoleNotFound`); deleted; every user holding it rewritten without it (`UnsafeGetAllUsers` of the batch transaction, 4b); `commitRevision`, refresh. The admin step's state is recorded at index `i + 1` (`authCur`), every
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

/-- **`as.RoleDelete(r)`** by the writer, for a request `r` asking `.roleDelete name`: W0's effect of
the request at the store's state (`admStep`), recorded as the next state, and the reply. -/
def authStore.RoleDelete.spec : Prop :=
  ∀ (st r : Loc) (name : GoString),
    AdminTriple (GF := GF) (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"RoleDelete")) (Val #r)) (authReqAt r (.roleDelete name)) st (.roleDelete name)

end spec
end Auth
end EtcdGrove
end Perennial
