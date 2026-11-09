/-
## `(*authStore).IsAdminPermitted(authInfo)`

**Users.** The auth applier's administrator check (`apply/auth.go:53`), `checkLeasePutsKeys`
(`apply/auth.go:210`), `LeaseRevoke`'s and `RoleGet`'s (`apply/auth.go:223,234`): the writer (3a);
`EtcdServer.checkMembershipOperationPermission` (`server.go:1403`), the lease checks
(`v3_server.go:588,620,767`), 2c; `AuthAdmin.isPermitted` (`api/v3rpc/auth.go:188`), 2a: readers.
Snippet: `examples/specreq/auth/check.go` (`ReqAdminCheck`).

**Proof sketch.** The flag (`IsAuthEnabled`, at `jf`); a nil `AuthInfo` or an empty user:
`ErrUserEmpty`; `lockedReadTx` (at `jx`): the user (absent: `ErrUserNotFound`), its root role
(`hasRootRole`; without: `ErrPermissionDenied`); `RUnlock`.

**Changes.** The old `adminVerdict M` restated over two recorded states (`adminPost`), one statement
for every mode; at the writer's state (`jf = jx = i`) it is W0's `AuthState.admin` and `adminErr`.

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

/-- **`as.IsAdminPermitted(ai)`** for a nil `ai` (then `u = ""`) or one naming `u`: `nil` only
with auth off at a recorded state or `u` of the root role at one (`adminPost`). -/
def authStore.IsAdminPermitted.spec : Prop :=
  ∀ (st ai : Loc) (γ : Cluster) (γa : AuthNames) (i0 : Nat) (dq : DFrac) (u : GoString)
    (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authLb γa i0 ∗ threadTok ∗ (⌜ai = null ∧ u = []⌝ ∨ authInfoAt ai dq u rev) }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"IsAdminPermitted")) (Val #ai))
  {{ (err : GoInterface), RET #err; threadTok ∗ (⌜ai = null ∧ u = []⌝ ∨ authInfoAt ai dq u rev) ∗
      adminPost γa i0 u err }}

end spec
end Auth
end EtcdGrove
end Perennial
