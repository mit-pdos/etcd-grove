/-
## `(*authStore).CheckPassword(username, password)`

**Users.** `EtcdServer.Authenticate`'s loop (`v3_server.go:853`, 2c), a reader. Snippet:
`examples/specreq/auth/admin.go` (`ReqUserAddThenCheck`).

**Proof sketch.** The flag (`IsAuthEnabled`, at `jf`; off: `0`, `ErrAuthNotEnabled`); under
`lockedReadTx` (at `jx`): the user (absent: `ErrAuthFailed`), password-less
(`Options.NoPassword`: `ErrNoPasswordUser`), the stored revision `ax.rev` (the backend's, the same
view as the user: what makes 2c's "checked revision equals `Revision()` later" mean "the user's
record has not changed since"); `RUnlock`; then `Bcrypt.CompareHashAndPassword` of the stored credential `c` (`authBackendAt`'s
realization: W0's `UserRec.password`) with `password`: `nil` exactly when `pwMatch c password`
(the boundary).

**Changes.** New statement over W0's state (the old one was an axiom: bcrypt untranslated); the
revision is the backend view's, not the atomic's. Round 1 (review S14): over W0's round-5
`pwMatch` (the stored credential, not the password).

**Margin.** None (`pwMatch` is bcrypt's verdict; W0's `authenticate` uses the same).
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
auth on at the flag's state `af` and the backend's `ax`: the user absent or `pw` not matching its
credential (`ErrAuthFailed`), password-less (`ErrNoPasswordUser`), or `pw` matching it and the
backend state's revision (`nil`). -/
def authStore.CheckPassword.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i0 : Nat) (name pw : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authLb γa i0 ∗ threadTok }}
    (App (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"CheckPassword")) (Val #name)) (Val #pw))
  {{ (r : w64) (err : GoInterface), RET (PairV #r #err); threadTok ∗
      ∃ (jf jx : Nat) (af ax : AuthState), ⌜i0 ≤ jf ∧ i0 ≤ jx⌝ ∗ authAt γa jf af ∗ authAt γa jx ax ∗
      ⌜(af.enabled = false ∧ r = W64 0 ∧ err = errOf .authNotEnabled) ∨
       (af.enabled = true ∧ r = W64 0 ∧ err = errOf .authFailed ∧
          (ax.users name = none ∨ ∃ ur c, ax.users name = some ur ∧ ur.password = some c ∧ ¬ pwMatch c pw)) ∨
       (af.enabled = true ∧ r = W64 0 ∧ err = errOf .noPasswordUser ∧
          ∃ ur, ax.users name = some ur ∧ ur.password = none) ∨
       (af.enabled = true ∧ err = GoInterface.nil ∧ uint.nat r = ax.rev ∧
          ∃ ur c, ax.users name = some ur ∧ ur.password = some c ∧ pwMatch c pw)⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
