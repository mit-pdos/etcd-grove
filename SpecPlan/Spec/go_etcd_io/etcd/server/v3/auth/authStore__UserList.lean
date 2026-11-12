/-
## `(*authStore).UserList(r)`

**Users.** `applierV3backend.UserList` (`apply/backend.go:255`). Snippet: `examples/specreq/auth/admin.go` (`ReqAdminSteps`).

**Proof sketch.** `as.be.GetAllUsers()` (4b: the read transaction, each record once in some order, `Schema.entsAny`; no batch lock: `Pre` back), the names copied. No state change. The step's state, `storeNext` (the code's function of the request, its
credential and `a`), is recorded at index `i + 1` (`authCur`), every view at it when the call
returns; its answer is one W0's `authStep` gives (`storeNext_adm`).

**Changes.** Restated over `admStep`. The old per-mode verdicts (`adminOut M hs`) are W0's `authStep` effect at
the writer's state (`admStep`), with no mode index. Round 1 (review F1, F2): `admStep` lifts W0's
step (which appends to `authHist`) by its auth part; the writer's premise is about the one next
state `storeNext rq cred a` (was: every state the model allows).

**Margin.** The order (the bucket's, by name) is not stated.
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

/-- **`as.UserList(r)`** by the writer, for a request `r` asking `.userList`: the store moves
to `storeNext` (the code's next state, which the writer shows reached), an answer of W0's step
(`admStep`) there, and the reply. -/
def authStore.UserList.spec : Prop :=
  ∀ (st r : Loc),
    AdminTriple (GF := GF) (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"UserList")) (Val #r)) (authReqAt r .userList []) st .userList []

end spec
end Auth
end EtcdGrove
end Perennial
