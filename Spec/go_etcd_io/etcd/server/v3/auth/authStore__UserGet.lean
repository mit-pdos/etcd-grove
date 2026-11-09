/-
## `(*authStore).UserGet(r)`

**Users.** `applierV3backend.UserGet` (`apply/backend.go:199`), behind `authApplierV3.UserGet`'s check (an administrator or the user itself). Snippet: `examples/specreq/auth/admin.go` (`ReqAdminSteps`).

**Proof sketch.** `as.be.GetUser(name)` (4b: a read section of the read transaction, at the writer's `a`: between writer calls every view is at it; no batch lock, so `Pre` and the hook come back, `hookOut`; integration I5: was "the batch transaction"); absent: `ErrUserNotFound`; the roles copied into a fresh response. No state change (`a' = a`, recorded again). The step's state, `storeNext` (the code's function of the request, its
credential and `a`), is recorded at index `i + 1` (`authCur`), every view at it when the call
returns; its answer is one W0's `authStep` gives (`storeNext_adm`).

**Changes.** Restated over `admStep`. The old per-mode verdicts (`adminOut M hs`) are W0's `authStep` effect at
the writer's state (`admStep`), with no mode index. Round 1 (review F1, F2): `admStep` lifts W0's
step (which appends to `authHist`) by its auth part; the writer's premise is about the one next
state `storeNext rq cred a` (was: every state the model allows).

**Margin.** The response's roles are in the store's (sorted) order; the model's answer is any permutation.
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

/-- **`as.UserGet(r)`** by the writer, for a request `r` asking `.userGet name`: the store moves
to `storeNext` (the code's next state, which the writer shows reached), an answer of W0's step
(`admStep`) there, and the reply. -/
def authStore.UserGet.spec : Prop :=
  ∀ (st r : Loc) (name : GoString),
    AdminTriple (GF := GF) (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"UserGet")) (Val #r)) (authReqAt r (.userGet name) []) st (.userGet name) []

end spec
end Auth
end EtcdGrove
end Perennial
