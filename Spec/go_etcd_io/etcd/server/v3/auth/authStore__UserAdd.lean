/-
## `(*authStore).UserAdd(r)`

**Users.** the apply layer's `applierV3backend.UserAdd` (`apply/backend.go:167`), behind the auth applier's administrator check (`apply/auth.go:52`). Snippet: `examples/specreq/auth/admin.go` (`ReqAdminSteps`).

**Proof sketch.** An empty name: `ErrUserEmpty`. The batch transaction (4b): the user read; present: `ErrUserAlreadyExist`. The password (`selectPassword`: the request's `hashedPw` decoded, or a pre-3.5 entry's plain password hashed, `Bcrypt.GenerateFromPassword`; never `ErrNoPasswordUser` under `authReqAt`), the user put, `commitRevision` (the linearization point: the next state recorded, `admNext` giving its `authReached` and `recordsFit`), `refreshRangePermCache`, the deferred `Unlock` (the backend view moves). The admin step's state is recorded at index `i + 1` (`authCur`), every
view at it when the call returns.

**Changes.** The old `UserAdd.spec`/`specSure` (two specs) merged: `authReqAt`'s realization rules out `ErrNoPasswordUser` (the server always sends a decodable hash); the name bound (`issues/etcd-auth-useradd-long-name-fatal.md`) is now `admNext`'s `recordsFit`. The old per-mode verdicts (`adminOut M hs`) are W0's `authStep` effect at
the writer's state (`admStep`), with no mode index.

**Margin.** The stored hash is not the model's password (`hashedPw`): `CheckPassword` relates them.
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

/-- **`as.UserAdd(r)`** by the writer, for a request `r` asking `.userAdd name pw noPw`: W0's effect of
the request at the store's state (`admStep`), recorded as the next state, and the reply. -/
def authStore.UserAdd.spec : Prop :=
  ∀ (st r : Loc) (name pw : GoString) (noPw : Bool),
    AdminTriple (GF := GF) (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"UserAdd")) (Val #r)) (authReqAt r (.userAdd name pw noPw)) st (.userAdd name pw noPw)

end spec
end Auth
end EtcdGrove
end Perennial
