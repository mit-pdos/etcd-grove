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
the state's, in some order; `root`'s reply is the package's `rootPerm`, whose contents the spec leaves open). -/
def roleGetOut (sta : AuthState) (name : GoString) (resp : Loc) (err : GoInterface) : IProp GF :=
  match sta.roles.lookup name with
  | none => iprop(⌜resp = null⌝ ∗ authErrOf .roleNotFound err)
  | some ps => iprop(⌜err = GoInterface.nil⌝ ∗
      ∃ v : etcdserverpb.AuthRoleGetResponse, resp ↦ v ∗
        (⌜name = rootRole⌝ ∨ ∃ (pl : List Loc) (ws : List PermW), v.Perm' ↦* pl ∗
          ⌜pl.length = ws.length ∧ ({ name := name, perms := ws } : RoleRec).toRole.Perm ps⌝ ∗
          [∗list] x ∈ pl.zip ws, ownPermW x.1 x.2))

/-- **`UserList`'s reply** of the state `sta`: no error, and a response whose `Users` are the
state's users' names, each once (in no promised order). -/
def userListOut (sta : AuthState) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop(⌜err = GoInterface.nil⌝ ∗ ∃ (v : etcdserverpb.AuthUserListResponse) (names : List GoString),
    resp ↦ v ∗ v.Users' ↦* names ∗
    ⌜names.Nodup ∧ ∀ n, n ∈ names ↔ (sta.users.lookup n).isSome⌝)

/-- **`RoleList`'s reply** of the state `sta`: as `userListOut`, the state's roles' names. -/
def roleListOut (sta : AuthState) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop(⌜err = GoInterface.nil⌝ ∗ ∃ (v : etcdserverpb.AuthRoleListResponse) (names : List GoString),
    resp ↦ v ∗ v.Roles' ↦* names ∗
    ⌜names.Nodup ∧ ∀ n, n ∈ names ↔ (sta.roles.lookup n).isSome⌝)

/-- **`CheckPassword`'s answer** for `username` in the mode `M`: an error; or no error, auth
enabled at some recorded state (`enabledVerdict`), and the revision `rev` of a recorded state that
has the user (`authSnap`: the locked read transaction's). Nothing about the password: bcrypt's
answer is the trust boundary (`bcrypt.CompareHashAndPassword`, D-AU6). -/
def passwordChecked (M : AuthMode) (username : GoString) (rev : w64) (err : GoInterface) :
    IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ enabledVerdict M true ∗
    ∃ sta : AuthState, authSnap M sta ∗
      ⌜uint.nat rev = sta.revision ∧ (sta.users.lookup username).isSome⌝))

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
