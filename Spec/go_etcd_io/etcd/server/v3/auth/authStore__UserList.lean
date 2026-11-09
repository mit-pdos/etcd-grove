/-
## `(*authStore).UserList(r)`

**Users.** `applierV3backend.UserList` (`apply/backend.go:255`). Snippet: `examples/specreq/auth/admin.go` (`ReqAdminSteps`).

**Proof sketch.** `as.be.GetAllUsers()` (4b), the names copied. No state change. The admin step's state is recorded at index `i + 1` (`authCur`), every
view at it when the call returns.

**Changes.** Restated over `admStep`. The old per-mode verdicts (`adminOut M hs`) are W0's `authStep` effect at
the writer's state (`admStep`), with no mode index.

**Margin.** The order (the bucket's, by name) is not stated.
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

/-- **`as.UserList(r)`** by the writer, for a request `r` asking `.userList`: W0's effect of
the request at the store's state (`admStep`), recorded as the next state, and the reply. -/
def authStore.UserList.spec : Prop :=
  ∀ (st r : Loc),
    AdminTriple (GF := GF) (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"UserList")) (Val #r)) (authReqAt r .userList) st .userList

end spec
end Auth
end EtcdGrove
end Perennial
