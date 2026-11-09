/-
## `(*authStore).UserAdd(r)`

**Users.** the apply layer's `applierV3backend.UserAdd` (`apply/backend.go:167`), behind the auth applier's administrator check (`apply/auth.go:52`). Snippet: `examples/specreq/auth/admin.go` (`ReqAdminSteps`).

**Proof sketch.** An empty name: `ErrUserEmpty`. The batch transaction (4b): the user read; present: `ErrUserAlreadyExist`. The credential (`selectPassword`: the request's `b64 cred` decoded to `cred`; never `ErrNoPasswordUser` under `authReqAt`), the user put, `commitRevision` (the linearization point: `storeNext` recorded, with the writer's `authReached` and `recordsFit`), `refreshRangePermCache`, the deferred `Unlock` (the backend view moves). The step's state, `storeNext` (the code's function of the request, its
credential and `a`), is recorded at index `i + 1` (`authCur`), every view at it when the call
returns; its answer is one W0's `authStep` gives (`storeNext_adm`).

**Changes.** The old `UserAdd.spec`/`specSure` (two specs) merged: `authReqAt`'s realization rules out `ErrNoPasswordUser` (the server always sends a decodable hash); the name bound (`issues/etcd-auth-useradd-long-name-fatal.md`) is now `AdminTriple`'s `recordsFit`. Round 1: the credential is the request's (`cred`, W0's `pwHash pw cred`); a pre-3.5 plain-password entry is out of scope (`authReqAt`). The old per-mode verdicts (`adminOut M hs`) are W0's `authStep` effect at
the writer's state (`admStep`), with no mode index. Round 1 (review F1, F2): `admStep` lifts W0's
step (which appends to `authHist`) by its auth part; the writer's premise is about the one next
state `storeNext rq cred a` (was: every state the model allows).

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

/-- **`as.UserAdd(r)`** by the writer, for a request `r` asking `.userAdd name pw noPw`: the store moves
to `storeNext` (the code's next state, which the writer shows reached), an answer of W0's step
(`admStep`) there, and the reply. -/
def authStore.UserAdd.spec : Prop :=
  ∀ (st r : Loc) (name pw : GoString) (noPw : Bool) (cred : Bytes),
    AdminTriple (GF := GF) (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"UserAdd")) (Val #r)) (authReqAt r (.userAdd name pw noPw) cred) st (.userAdd name pw noPw) cred

end spec
end Auth
end EtcdGrove
end Perennial
