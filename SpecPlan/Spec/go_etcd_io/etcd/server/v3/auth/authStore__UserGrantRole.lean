/-
## `(*authStore).UserGrantRole(r)`

**Users.** `applierV3backend.UserGrantRole` (`apply/backend.go:191`). Snippet: `examples/specreq/auth/admin.go` (`ReqAdminSteps`).

**Proof sketch.** The user read (absent: `ErrUserNotFound`); a role other than `root` read (absent: `ErrRoleNotFound`); `sort.SearchStrings` over the user's sorted roles: present, no change; else appended, `sort.Strings`, put, `commitRevision`, refresh. The step's state, `storeNext` (the code's function of the request, its
credential and `a`), is recorded at index `i + 1` (`authCur`), every view at it when the call
returns; its answer is one W0's `authStep` gives (`storeNext_adm`).

**Changes.** Restated over `admStep` (the model appends the role; the store keeps the list sorted: `authBackendAt`'s "up to order"). The old per-mode verdicts (`adminOut M hs`) are W0's `authStep` effect at
the writer's state (`admStep`), with no mode index. Round 1 (review F1, F2): `admStep` lifts W0's
step (which appends to `authHist`) by its auth part; the writer's premise is about the one next
state `storeNext rq cred a` (was: every state the model allows).

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

/-- **`as.UserGrantRole(r)`** by the writer, for a request `r` asking `.userGrantRole user role`: the store moves
to `storeNext` (the code's next state, which the writer shows reached), an answer of W0's step
(`admStep`) there, and the reply. -/
def authStore.UserGrantRole.spec : Prop :=
  ∀ (st r : Loc) (user role : GoString),
    AdminTriple (GF := GF) (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"UserGrantRole")) (Val #r)) (authReqAt r (.userGrantRole user role) []) st (.userGrantRole user role) []

end spec
end Auth
end EtcdGrove
end Perennial
