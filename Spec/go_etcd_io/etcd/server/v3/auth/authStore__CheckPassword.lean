/-
## `(*authStore).CheckPassword(username, password)`

**Users.** `EtcdServer.Authenticate`'s loop (`v3_server.go:853`, 2c), a reader. Snippet:
`examples/specreq/auth/admin.go` (`ReqUserAddThenCheck`).

**Proof sketch.** The flag (`IsAuthEnabled`, at `jf`; off: `0`, `ErrAuthNotEnabled`); under
`lockedReadTx` (at `jx`): the user (absent: `ErrAuthFailed`), password-less
(`Options.NoPassword`: `ErrNoPasswordUser`), the stored revision `ax.rev` (the backend's, the same
view as the user: what makes 2c's "checked revision equals `Revision()` later" mean "the user's
record has not changed since"); `RUnlock`; then `Bcrypt.CompareHashAndPassword` of the stored hash
(`authBackendAt`'s realization: a hash of the model's password, `Bcrypt.hashOf`) with `password`:
`nil` for the user's password (the boundary's correctness), any answer otherwise.

**Changes.** New statement over W0's state (the old one was an axiom: bcrypt untranslated); the
revision is the backend view's, not the atomic's.

**Margin.** A wrong password may pass (bcrypt reads 72 bytes, hashes collide: the boundary assumes
no rejection), so success does not say the password is the user's; W0's `authenticate` step must
allow that (`req/go_etcd_io_etcd_api_v3.md`, "from 3d").
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

/-- **`as.CheckPassword(name, pw)`**: auth off at a recorded state (`0`, `ErrAuthNotEnabled`); or,
auth on at the flag's state `af` and the backend's `ax`: the user absent or `pw` not its password
(`ErrAuthFailed`), password-less (`ErrNoPasswordUser`), or the user with a password and the backend
state's revision (`nil`). `pw` the user's password never fails with auth on. -/
def authStore.CheckPassword.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i0 : Nat) (name pw : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authLb γa i0 ∗ threadTok }}
    (App (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"CheckPassword")) (Val #name)) (Val #pw))
  {{ (r : w64) (err : GoInterface), RET (PairV #r #err); threadTok ∗
      ∃ (jf jx : Nat) (af ax : AuthState), ⌜i0 ≤ jf ∧ i0 ≤ jx⌝ ∗ authAt γa jf af ∗ authAt γa jx ax ∗
      ⌜(af.enabled = false ∧ r = W64 0 ∧ err = errOf .authNotEnabled) ∨
       (af.enabled = true ∧ r = W64 0 ∧ err = errOf .authFailed ∧
          (ax.users name = none ∨ ∃ ur p, ax.users name = some ur ∧ ur.password = some p ∧ p ≠ pw)) ∨
       (af.enabled = true ∧ r = W64 0 ∧ err = errOf .noPasswordUser ∧
          ∃ ur, ax.users name = some ur ∧ ur.password = none) ∨
       (af.enabled = true ∧ err = GoInterface.nil ∧ uint.nat r = ax.rev ∧
          ∃ ur p, ax.users name = some ur ∧ ur.password = some p)⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
