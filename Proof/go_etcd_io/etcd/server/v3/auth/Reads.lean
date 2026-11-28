/-
**What the admin reads return** (the auth plan's E2j, 2026-10-26): the replies of `UserGet`,
`RoleGet`, `UserList` and `RoleList` of a state of the store, the latest one at the admin side's
authority (`histLast`). Lean-first (no Rocq counterpart); the specs are
`Spec/go_etcd_io/etcd/server/v3/auth/authStore__{UserGet,RoleGet,UserList,RoleList}.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`UserGet`'s reply** for the user `name` of the state `sta`: `ErrUserNotFound` and no response
if the state has no such user; else no error and a response whose `Roles` hold the user's roles
(a copy, owned). -/
def userGetOut (sta : AuthState) (name : GoString) (resp : Loc) (err : GoInterface) : IProp GF :=
  match sta.users.lookup name with
  | none => iprop(⌜resp = null⌝ ∗ authErrOf .userNotFound err)
  | some roles => iprop(⌜err = GoInterface.nil⌝ ∗
      ∃ v : etcdserverpb.AuthUserGetResponse, resp ↦ v ∗ v.Roles' ↦* roles)

/-- **`RoleGet`'s reply** for the role `name` of the state `sta`: `ErrRoleNotFound` and no response
if the state has no such role; else no error and a response which, for a role other than `root`,
holds the role's permissions as stored (read-only messages whose permissions of a known type are
the state's, in the state's order: by (key, range end), nomode X-a1; `root`'s reply is the package's `rootPerm`, whose contents the spec leaves open). -/
def roleGetOut (sta : AuthState) (name : GoString) (resp : Loc) (err : GoInterface) : IProp GF :=
  match sta.roles.lookup name with
  | none => iprop(⌜resp = null⌝ ∗ authErrOf .roleNotFound err)
  | some ps => iprop(⌜err = GoInterface.nil⌝ ∗
      ∃ v : etcdserverpb.AuthRoleGetResponse, resp ↦ v ∗
        (⌜name = rootRole⌝ ∨ ∃ (pl : List Loc) (ws : List PermW), v.Perm' ↦* pl ∗
          ⌜pl.length = ws.length ∧ ({ name := name, perms := ws } : RoleRec).toRole = ps⌝ ∗
          [∗list] x ∈ pl.zip ws, ownPermW x.1 x.2))

/-- **`UserList`'s reply** of the state `sta`: no error, and a response whose `Users` are the
state's users' names, each once (in no promised order). -/
def userListOut (sta : AuthState) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop(⌜err = GoInterface.nil⌝ ∗ ∃ (v : etcdserverpb.AuthUserListResponse) (names : List GoString),
    resp ↦ v ∗ v.Users' ↦* names ∗
    ⌜names.Nodup ∧ ∀ n, n ∈ names ↔ (sta.users.lookup n).isSome⌝)

/-- **`RoleList`'s reply** of the state `sta`: as `userListOut`, the state's roles' names
(`rolesListed`: every listed role when fewer than `2 ^ 63 - 1` are listed; A6 (R-c), 2026-11-19). -/
def roleListOut (sta : AuthState) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop(⌜err = GoInterface.nil⌝ ∗ ∃ (v : etcdserverpb.AuthRoleListResponse) (names : List GoString),
    resp ↦ v ∗ v.Roles' ↦* names ∗ ⌜rolesListed names sta⌝)

/-- **`CheckPassword`'s answer** for `username` in the mode `M`: an error, one of the package's
(`authErrOf`; C1's A4, 2026-10-29: the server returns it as its own); or no error, auth
enabled at some recorded state (`enabledVerdict`), the user in a recorded state and `rev` the
revision of a recorded state not earlier than it (the locked read transaction's view, `authViewSnap`:
its users' bucket and its `auth` bucket; 2026-11-16, the second refutation's fix: until then one
recorded state with the user and the revision `rev`, which Go breaks: a `UserDelete` whose revision
is written back before its delete is committed, `nonissues/etcd-auth-readtx-delete-window-mixed-state.md`).
Nothing about the password: bcrypt's answer is the trust boundary (`bcrypt.CompareHashAndPassword`,
D-AU6). -/
def passwordChecked (M : AuthMode) (username : GoString) (rev : w64) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err ≠ GoInterface.nil⌝ ∗ ∃ e : AuthErr, authErrOf e err) ∨
    (⌜err = GoInterface.nil⌝ ∗ enabledVerdict M true ∗
    ∃ v : BkView, authViewSnap M v ∗
      ⌜uint.nat rev = v.atAuth.revision ∧ (v.atUsers.users.lookup username).isSome⌝))

/-- A user message's `Name` (read-only) holds `n`: what `UserList` reads of `GetAllUsers`'s
messages. -/
def userNameAt (u : Loc) (n : GoString) : IProp GF :=
  iprop(∃ nm : GoSlice, structFieldRef go_etcd_io.etcd.api.v3.authpb.User go!"Name" u ↦□ nm ∗
    nm ↦*□ n)

instance userNameAt_persistent (u : Loc) (n : GoString) :
    Persistent (userNameAt (GF := GF) u n) := by
  unfold userNameAt; infer_instance

/-- A role message's `Name` (read-only) holds `n`: what `RoleList` reads. -/
def roleNameAt (r : Loc) (n : GoString) : IProp GF :=
  iprop(∃ nm : GoSlice, structFieldRef go_etcd_io.etcd.api.v3.authpb.Role go!"Name" r ↦□ nm ∗
    nm ↦*□ n)

instance roleNameAt_persistent (r : Loc) (n : GoString) :
    Persistent (roleNameAt (GF := GF) r n) := by
  unfold roleNameAt; infer_instance

end defs

end auth
end EtcdGrove
end Perennial
