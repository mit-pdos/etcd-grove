/-
**The admin side's steps** (the auth plan's S4, 2026-10-24; `notes/auth-plan.md`,
`notes/decisions.md`, "S4 of the auth plan"): what each admin operation of the auth store
(`store.go`: `AuthEnable`/`AuthDisable`, `UserAdd`/`UserDelete`/`UserChangePassword`/
`UserGrantRole`/`UserRevokeRole`, `RoleAdd`/`RoleDelete`/`RoleGrantPermission`/
`RoleRevokePermission`) does to the model's state (`AuthState`, `Model.lean`), as a relation
between the state the operation found and its outcome (`Outcome`): refused with one of the
package's errors (`AuthErr`, the state unchanged), nothing to do (`same`: `nil`, the state
unchanged), or the next state (`next`: the records written and the revision bumped,
`commitRevision`). Most steps are functions (`userAddF`, ...); the two whose result the Go code
leaves to a sort (`UserGrantRole` sorts the user's roles, `RoleGrantPermission` the role's
permissions by key, unstably) or to a wire detail the model does not keep (a permission of an
unknown type, which `RoleRec.toRole` drops) are relations.

**The reads of `as.enabled` outside `enabledMu`** (`UserDelete`, `UserRevokeRole`, `RoleDelete`
refuse to touch `root` when auth is enabled; `AuthEnable`/`AuthDisable` read it under the lock
but before the batch transaction) are a parameter `en` of the step, the flag's value the code read
(`enabledVerdict`: some recorded state's flag), in the spirit of the verdicts' honesty about the
checks' reads (`Model.lean`): the step is relative to the flag read, not to the latest state's.

**The authority** (`authOwn M hs`): in the mode `on γa`, the admin side's half of the history
(`authHistHalf`) and half the ghost variable of the latest state (`authCurHalf`; the store's
revision invariant holds the other half, `InvAuth.lean`), held by the admin side's caller (the
server's apply thread) and threaded through the admin operations' specs: an operation whose
outcome is `next st'` appends `st'` (`adminOut`); in `off` the states stay disabled; in `any`
nothing. The history's other half is the backend's batch lock's (`authLockShare`, the auth plan's
S4f, 2026-10-25): `Lock()` gives it with the buckets' state (`authLockI`), so inside the
transaction the caller holds the whole authority (`authOwnF`), which an append needs, and
`Unlock()` takes it back with the buckets at the new latest state.

**Premises** (`stepOk`): the revision below `2^64 - 1` (the atomic `revision` is a `uint64`) and
the next state's permissions fitting the cache's trees (`permsFit`, `refreshRangePermCache`'s
premise): the records' growth is unbounded in the Go code
(`issues/etcd-auth-record-too-large-fatal.md`); a record's name as a bbolt key is bounded by the
write contract (`issues/etcd-auth-useradd-long-name-fatal.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Buckets

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI

/-! ## The errors -/

/-- The error variables the admin side and the checks return (`store.go`). -/
inductive AuthErr where
  | rootUserNotExist | rootRoleNotExist | userAlreadyExist | userEmpty | userNotFound
  | roleAlreadyExist | roleNotFound | roleEmpty | permissionNotGiven | noPasswordUser
  | permissionDenied | roleNotGranted | permissionNotGranted | authOldRevision
  | invalidAuthToken | invalidAuthMgmt
  -- `Authenticate`'s (the auth plan's S5), appended
  | authFailed | authNotEnabled
  deriving DecidableEq, Inhabited

/-- The Go variable's name. -/
def AuthErr.var [FfiSyntax] [GoGlobalContext] : AuthErr → GoString
  | .rootUserNotExist => go_etcd_io.etcd.server.v3.auth.ErrRootUserNotExist
  | .rootRoleNotExist => go_etcd_io.etcd.server.v3.auth.ErrRootRoleNotExist
  | .userAlreadyExist => go_etcd_io.etcd.server.v3.auth.ErrUserAlreadyExist
  | .userEmpty => go_etcd_io.etcd.server.v3.auth.ErrUserEmpty
  | .userNotFound => go_etcd_io.etcd.server.v3.auth.ErrUserNotFound
  | .roleAlreadyExist => go_etcd_io.etcd.server.v3.auth.ErrRoleAlreadyExist
  | .roleNotFound => go_etcd_io.etcd.server.v3.auth.ErrRoleNotFound
  | .roleEmpty => go_etcd_io.etcd.server.v3.auth.ErrRoleEmpty
  | .permissionNotGiven => go_etcd_io.etcd.server.v3.auth.ErrPermissionNotGiven
  | .noPasswordUser => go_etcd_io.etcd.server.v3.auth.ErrNoPasswordUser
  | .permissionDenied => go_etcd_io.etcd.server.v3.auth.ErrPermissionDenied
  | .roleNotGranted => go_etcd_io.etcd.server.v3.auth.ErrRoleNotGranted
  | .permissionNotGranted => go_etcd_io.etcd.server.v3.auth.ErrPermissionNotGranted
  | .authOldRevision => go_etcd_io.etcd.server.v3.auth.ErrAuthOldRevision
  | .invalidAuthToken => go_etcd_io.etcd.server.v3.auth.ErrInvalidAuthToken
  | .invalidAuthMgmt => go_etcd_io.etcd.server.v3.auth.ErrInvalidAuthMgmt
  | .authFailed => go_etcd_io.etcd.server.v3.auth.ErrAuthFailed
  | .authNotEnabled => go_etcd_io.etcd.server.v3.auth.ErrAuthNotEnabled

/-! ## The steps -/

/-- An admin operation's outcome at the state it found. -/
inductive Outcome where
  /-- refused with the error `e`, the state unchanged -/
  | err (e : AuthErr)
  /-- nothing to do (`nil`), the state unchanged -/
  | same
  /-- the next state (the records written, the revision bumped) -/
  | next (st : AuthState)

/-- A step's relation: the state found and the outcome. -/
abbrev StepRel := AuthState → Outcome → Prop

/-- `commitRevision`: the revision bumped. -/
def bump (st : AuthState) : AuthState := { st with revision := st.revision + 1 }

/-- `UnsafePutUser` of a record of the name with the roles (the user's other fields are not
in the model). -/
def putUser (st : AuthState) (name : GoString) (roles : User) : AuthState :=
  { st with users := GMap.insert name roles st.users }

/-- `UnsafeDeleteUser`. -/
def delUser (st : AuthState) (name : GoString) : AuthState :=
  { st with users := GMap.delete name st.users }

/-- `UnsafePutRole` of a record of the name with the permissions. -/
def putRole (st : AuthState) (name : GoString) (ps : Role) : AuthState :=
  { st with roles := GMap.insert name ps st.roles }

/-- `RoleDelete`'s writes: the role deleted, and every user's roles without it. -/
def delRole (st : AuthState) (name : GoString) : AuthState :=
  { st with
    roles := GMap.delete name st.roles
    users := GMap.fmap (fun u => u.filter fun r => r ≠ name) st.users }

/-- A functional step as a relation. -/
def stepOf (f : AuthState → Outcome) : StepRel := fun st o => o = f st

/-- `AuthEnable`, having read the flag `en`: already enabled, nothing; no root user
(`ErrRootUserNotExist`); root without the root role (`ErrRootRoleNotExist`); else enabled, the
revision as stored (`setRevision(tx.UnsafeReadAuthRevision())`). -/
def authEnableF (en : Bool) (st : AuthState) : Outcome :=
  if en then .same
  else match st.users !! rootRole with
    | none => .err .rootUserNotExist
    | some u => if isRoot u then .next { st with enabled := true } else .err .rootRoleNotExist

/-- `AuthDisable`, having read the flag `en`: disabled, the revision bumped; or nothing. -/
def authDisableF (en : Bool) (st : AuthState) : Outcome :=
  if en then .next (bump { st with enabled := false }) else .same

/-- `UserAdd(name)`: an empty name (`ErrUserEmpty`), an existing user (`ErrUserAlreadyExist`),
else the user with no roles. (`ErrNoPasswordUser`, when the password cannot be selected, is a
data-dependent refusal outside the model: `adminOut`'s `extra`.) -/
def userAddF (name : GoString) (st : AuthState) : Outcome :=
  if name = [] then .err .userEmpty
  else if (st.users !! name).isSome then .err .userAlreadyExist
  else .next (bump (putUser st name []))

/-- `UserDelete(name)`, having read the flag `en`: `root` with auth enabled
(`ErrInvalidAuthMgmt`); no such user (`ErrUserNotFound`); else deleted. -/
def userDeleteF (en : Bool) (name : GoString) (st : AuthState) : Outcome :=
  if en ∧ name = rootRole then .err .invalidAuthMgmt
  else match st.users !! name with
    | none => .err .userNotFound
    | some _ => .next (bump (delUser st name))

/-- `UserChangePassword(name)`: no such user (`ErrUserNotFound`); else the record rewritten with
the same roles, the revision bumped. (`ErrNoPasswordUser`: `extra`.) -/
def userChangePasswordF (name : GoString) (st : AuthState) : Outcome :=
  match st.users !! name with
  | none => .err .userNotFound
  | some _ => .next (bump st)

/-- `UserGrantRole(user, role)`: no such user (`ErrUserNotFound`); a role other than `root` that
does not exist (`ErrRoleNotFound`); a role the user has (nothing: "ignored"); else the user's
roles with the role, sorted (`sort.Strings`: some sorted permutation). -/
def userGrantRoleR (user role : GoString) : StepRel := fun st o =>
  match st.users !! user with
  | none => o = .err .userNotFound
  | some u =>
    if role ≠ rootRole ∧ (st.roles !! role).isNone then o = .err .roleNotFound
    else if role ∈ u then o = .same
    else ∃ u' : User, u'.Perm (u ++ [role]) ∧ u'.Pairwise go.GoStringLt ∧
      o = .next (bump (putUser st user u'))

/-- `UserRevokeRole(name, role)`, having read the flag `en`: `root`'s root role with auth
enabled (`ErrInvalidAuthMgmt`); no such user (`ErrUserNotFound`); a role the user lacks
(`ErrRoleNotGranted`); else the roles without it. -/
def userRevokeRoleF (en : Bool) (name role : GoString) (st : AuthState) : Outcome :=
  if en ∧ name = rootRole ∧ role = rootRole then .err .invalidAuthMgmt
  else match st.users !! name with
    | none => .err .userNotFound
    | some u =>
      if role ∈ u then .next (bump (putUser st name (u.filter fun r => r ≠ role)))
      else .err .roleNotGranted

/-- `RoleAdd(name)`: an empty name (`ErrRoleEmpty`), an existing role (`ErrRoleAlreadyExist`),
else the role with no permissions. -/
def roleAddF (name : GoString) (st : AuthState) : Outcome :=
  if name = [] then .err .roleEmpty
  else if (st.roles !! name).isSome then .err .roleAlreadyExist
  else .next (bump (putRole st name []))

/-- `RoleDelete(role)`, having read the flag `en`: `root` with auth enabled
(`ErrInvalidAuthMgmt`); no such role (`ErrRoleNotFound`); else the role deleted and revoked from
every user. -/
def roleDeleteF (en : Bool) (role : GoString) (st : AuthState) : Outcome :=
  if en ∧ role = rootRole then .err .invalidAuthMgmt
  else match st.roles !! role with
    | none => .err .roleNotFound
    | some _ => .next (bump (delRole st role))

/-- The permission `p` is the one `[key, rangeEnd)` (`bytes.Equal` on both). -/
def permAt (key rangeEnd : GoString) (p : Perm) : Prop := p.key = key ∧ p.rangeEnd = rangeEnd

instance permAt_decidable (key rangeEnd : GoString) (p : Perm) : Decidable (permAt key rangeEnd p) :=
  inferInstanceAs (Decidable (p.key = key ∧ p.rangeEnd = rangeEnd))

/-- `RoleRevokePermission(role, key, rangeEnd)`: no such role (`ErrRoleNotFound`); else the
role's permissions without those on `[key, rangeEnd)`, or `ErrPermissionNotGranted` when none
of the model's are (the code compares the record's permissions, among which one of an unknown
type, outside the model, may match: so a success is allowed whatever the model's). -/
def roleRevokePermissionR (role key rangeEnd : GoString) : StepRel := fun st o =>
  match st.roles !! role with
  | none => o = .err .roleNotFound
  | some ps =>
    (o = .err .permissionNotGranted ∧ ∀ p ∈ ps, ¬ permAt key rangeEnd p) ∨
    o = .next (bump (putRole st role (ps.filter fun p => ¬ permAt key rangeEnd p)))

open Classical in
/-- `RoleGrantPermission(role, w)` for the wire permission `w` (`Buckets.lean`): no permission
given (`ErrPermissionNotGiven`, `w = none`); an invalid range (`ErrInvalidAuthMgmt`,
`isValidPermissionRange`); no such role (`ErrRoleNotFound`); else the role's permissions with
`w`'s: the record's entry of the same key and range end, if the first of a key at or above `w`'s
is one, gets `w`'s type, else `w` is appended and the record sorted by key (`sort.Sort`,
unstable): in the model, some permutation of the permissions with the new one, or one entry on
`w`'s range replaced; a permission of an unknown type (`permOfWire w = none`) is dropped by the
model (`RoleRec.toRole`), so the model's list loses at most the entry it replaced, and is
reordered when the record is sorted (unstable: entries of one key may change places; S4d,
2026-10-24: a sublist up to a permutation). -/
def roleGrantPermissionR (role : GoString) (w : Option PermW) : StepRel := fun st o =>
  match w with
  | none => o = .err .permissionNotGiven
  | some w =>
    if ¬ rangeValid w.key w.rangeEnd then o = .err .invalidAuthMgmt
    else match st.roles !! role with
      | none => o = .err .roleNotFound
      | some ps =>
        match permOfWire w with
        | some perm => ∃ ps' : Role,
            (ps'.Perm (ps ++ [perm]) ∨
              ∃ (i : Nat) (p : Perm), ps[i]? = some p ∧ permAt w.key w.rangeEnd p ∧
                ps' = ps.set i perm) ∧
            o = .next (bump (putRole st role ps'))
        | none => ∃ ps' ps'' : Role, ps''.Sublist ps ∧ ps'.Perm ps'' ∧
            o = .next (bump (putRole st role ps'))

/-! ## The steps keep the history's invariants -/

theorem permKeysOk_bump (st : AuthState) (h : permKeysOk st) : permKeysOk (bump st) := h

theorem permKeysOk_enabled (st : AuthState) (b : Bool) (h : permKeysOk st) :
    permKeysOk { st with enabled := b } := h

theorem permKeysOk_putUser (st : AuthState) (name : GoString) (roles : User) (h : permKeysOk st) :
    permKeysOk (putUser st name roles) := h

theorem permKeysOk_delUser (st : AuthState) (name : GoString) (h : permKeysOk st) :
    permKeysOk (delUser st name) := h

theorem permKeysOk_putRole (st : AuthState) (name : GoString) (ps : Role) (h : permKeysOk st)
    (hps : ∀ p ∈ ps, p.key ≠ []) : permKeysOk (putRole st name ps) := by
  intro r ps' hr p hp
  by_cases hrn : name = r
  · subst hrn
    simp only [putRole, GMap.lookup_insert] at hr
    cases hr
    exact hps p hp
  · simp only [putRole, GMap.lookup_insert_ne _ _ hrn] at hr
    exact h r ps' hr p hp

theorem permKeysOk_delRole (st : AuthState) (name : GoString) (h : permKeysOk st) :
    permKeysOk (delRole st name) := by
  intro r ps hr p hp
  by_cases hrn : name = r
  · subst hrn
    simp only [delRole, GMap.lookup_delete] at hr
    cases hr
  · simp only [delRole, GMap.lookup_delete_ne _ hrn] at hr
    exact h r ps hr p hp

/-- The `next` state of a step at a state with valid permission keys has them. -/
theorem permKeysOk_of_perm {ps ps' : Role} (hp : ps'.Perm ps) (h : ∀ p ∈ ps, p.key ≠ []) :
    ∀ p ∈ ps', p.key ≠ [] := fun p hp' => h p (hp.mem_iff.1 hp')

/-! ## The authority, and an operation's outcome in the mode -/

section ghost
variable [FfiSyntax] {GF : BundledGFunctors} [AllG GF]

/-- **The admin side's authority** in the mode `M`, the history `hs` (see the file header):
`on γa`, the admin side's half of the history and half the latest state's ghost variable (the
other half is the store's revision invariant's, `InvAuth.lean`); `off`, the states disabled (and
one at least); `any`, nothing. -/
def authOwn (M : AuthMode) (hs : List AuthState) : IProp GF :=
  match M with
  | .on γa => iprop(authHistHalf γa hs ∗ ∃ st : AuthState, ⌜hs.getLast? = some st⌝ ∗ authCurHalf γa st)
  | .off => iprop(⌜hs ≠ [] ∧ ∀ st ∈ hs, st.enabled = false⌝)
  | .any => iprop(True)

/-- **The batch lock's share of the authority** (the auth plan's S4f): `on γa`, the lock's half
of the history; in the other modes nothing. -/
def authLockShare (M : AuthMode) (hs : List AuthState) : IProp GF :=
  match M with
  | .on γa => authLockHalf γa hs
  | _ => iprop(True)

/-- **The authority inside a batch transaction** (the auth plan's S4f): `on γa`, the history's
whole authority (the admin side's half joined with the lock's, `authOwnF_split`) and half the
latest state's ghost variable; the other modes as `authOwn`. -/
def authOwnF (M : AuthMode) (hs : List AuthState) : IProp GF :=
  match M with
  | .on γa => iprop(authHist γa hs ∗ ∃ st : AuthState, ⌜hs.getLast? = some st⌝ ∗ authCurHalf γa st)
  | .off => iprop(⌜hs ≠ [] ∧ ∀ st ∈ hs, st.enabled = false⌝)
  | .any => iprop(True)

/-- The state the backend's batch transaction finds, given the authority `hs`: `on γa`, the
latest; `off`, a disabled one; `any`, any. -/
def histLast (M : AuthMode) (hs : List AuthState) (st : AuthState) : Prop :=
  match M with
  | .on _ => hs.getLast? = some st
  | .off => st.enabled = false
  | .any => True

theorem authOwn_any (hs : List AuthState) : ⊢ authOwn (GF := GF) .any hs := by
  unfold authOwn; itrivial

theorem authOwnF_any (hs : List AuthState) : ⊢ authOwnF (GF := GF) .any hs := by
  unfold authOwnF; itrivial

/-- The authority inside a transaction is the admin side's and the lock's. -/
theorem authOwnF_split (M : AuthMode) (hs : List AuthState) :
    authOwnF (GF := GF) M hs ⊣⊢ authOwn M hs ∗ authLockShare M hs := by
  cases M with
  | on γa =>
    simp only [authOwnF, authOwn, authLockShare]
    constructor
    · iintro ⟨Hh, Hc⟩
      icases (authHist_split γa hs).1 $$ Hh with ⟨H1, H2⟩
      iframe H1 Hc H2
    · iintro ⟨⟨H1, Hc⟩, H2⟩
      iframe Hc; iapply (authHist_split γa hs).2; iframe H1 H2
  | off =>
    simp only [authOwnF, authOwn, authLockShare]
    constructor
    · iintro H; iframe H
    · iintro ⟨H, -⟩; iexact H
  | any =>
    simp only [authOwnF, authOwn, authLockShare]
    constructor
    · iintro -; isplitl <;> itrivial
    · iintro -; itrivial

/-- **What the batch lock holds with the buckets at `st`** (the auth plan's S4f): its share of
some history whose latest state (`histLast`) is `st`. -/
def authLockI (M : AuthMode) (st : AuthState) : IProp GF :=
  iprop(∃ hs : List AuthState, authLockShare M hs ∗ ⌜histLast M hs st⌝)

/-- **`Lock()`'s join**: the admin side's authority and the lock's share agree on the history, so
the buckets hold the admin side's latest state. -/
theorem authOwn_lockI_join (M : AuthMode) (hs : List AuthState) (st : AuthState) :
    ⊢ authOwn (GF := GF) M hs -∗ authLockI M st -∗ authOwnF M hs ∗ ⌜histLast M hs st⌝ := by
  iintro Hown HI
  iunfold authLockI at HI
  icases HI with ⟨%hs', Hsh, %Hl⟩
  cases M with
  | on γa =>
    simp only [authOwn, authLockShare]
    icases Hown with ⟨Hh, Hc⟩
    ihave %Heq := authHistHalf_lock_agree γa hs hs' $$ Hh Hsh
    subst Heq
    isplitl
    · iapply (authOwnF_split (.on γa) hs).2
      simp only [authOwn, authLockShare]; iframe Hh Hc Hsh
    · ipureintro; exact Hl
  | off =>
    isplitl
    · iapply (authOwnF_split .off hs).2; iframe Hown
      simp only [authLockShare]; itrivial
    · ipureintro; simp only [histLast] at Hl ⊢; exact Hl
  | any =>
    isplitl
    · iapply authOwnF_any
    · ipureintro; simp only [histLast]

/-- **`Unlock()`'s split**: the lock takes its share back with the buckets at the latest state. -/
theorem authOwnF_lockI_split (M : AuthMode) (hs : List AuthState) (st : AuthState)
    (hl : histLast M hs st) :
    authOwnF (GF := GF) M hs ⊢ authOwn M hs ∗ authLockI M st := by
  iintro H
  icases (authOwnF_split M hs).1 $$ H with ⟨Hown, Hsh⟩
  iframe Hown
  iunfold authLockI
  iexists hs; iframe Hsh; ipureintro; exact hl

/-- The authority keeps a recorded state (a bupd: the lower bound is taken from the authority). -/
theorem authHist_stateAt_keep (γa : AuthNames) (hs : List AuthState) (i : Nat) (st : AuthState)
    (h : hs[i]? = some st) :
    authHist (GF := GF) γa hs ⊢ |==> (authHist γa hs ∗ authStateAt γa i st) := by
  unfold authHist authStateAt
  iintro ⟨H, %Hk⟩
  imod (monoListAuthOwn_update (γ := γa.hist) (l := hs) hs (List.prefix_refl hs)) $$ H with ⟨H, #Hlb⟩
  imodintro
  iframe H
  isplitr
  · ipureintro; exact Hk
  isplitl []
  · iapply (monoListIdxOwn_get i st h) $$ Hlb
  · ipureintro; exact Hk st (List.mem_of_getElem? h)

/-- The latest state is recorded (`on γa`). -/
theorem authOwnF_last (γa : AuthNames) (hs : List AuthState) :
    authOwnF (GF := GF) (.on γa) hs ⊢ |==> (authOwnF (.on γa) hs ∗
      ∃ st : AuthState, ⌜hs.getLast? = some st⌝ ∗ authStateAt γa (hs.length - 1) st) := by
  simp only [authOwnF]
  iintro ⟨Hh, ⟨%st, %Hl, Hc⟩⟩
  have hi : hs[hs.length - 1]? = some st := by
    cases hs with
    | nil => cases Hl
    | cons x xs =>
      rw [List.getLast?_eq_getElem?] at Hl
      exact Hl
  imod (authHist_stateAt_keep γa hs (hs.length - 1) st hi) $$ Hh with ⟨Hh, #Hst⟩
  imodintro
  iframe Hh
  isplitl [Hc]
  · iexists st; iframe Hc; ipureintro; exact Hl
  · iexists st; iframe Hst; ipureintro; exact Hl

end ghost

section res
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The error `err` is the variable of `e` (persistent). -/
def authErrOf (e : AuthErr) (err : GoInterface) : IProp GF :=
  iprop(∃ ei : GoInterfaceOk, globalAddr e.var ↦□ GoInterface.ok ei ∗ ⌜err = GoInterface.ok ei⌝)

instance authErrOf_persistent (e : AuthErr) (err : GoInterface) :
    Persistent (authErrOf (GF := GF) e err) := by
  unfold authErrOf; infer_instance

/-- The authority after the outcome `o`, with the error returned: refused, unchanged and the
error's variable; nothing, unchanged and `nil`; the next state appended and `nil`. -/
def outRes (M : AuthMode) (hs : List AuthState) (o : Outcome) (err : GoInterface) : IProp GF :=
  match o with
  | .err e => iprop(authOwn M hs ∗ authErrOf e err)
  | .same => iprop(authOwn M hs ∗ ⌜err = GoInterface.nil⌝)
  | .next st' => iprop(authOwn M (hs ++ [st']) ∗ ⌜err = GoInterface.nil⌝)

/-- **An admin operation's result** in the mode `M`, from the authority `hs`, for the step `R`
and the data-dependent refusals `extra` (errors the model does not decide, the state unchanged):
the outcome of `R` at the state the transaction found (`histLast`), with the authority after it
(`outRes`), or one of the `extra` errors. -/
def adminOut (M : AuthMode) (hs : List AuthState) (R : StepRel) (extra : AuthErr → Prop)
    (err : GoInterface) : IProp GF :=
  iprop((∃ e : AuthErr, ⌜extra e⌝ ∗ authOwn M hs ∗ authErrOf e err) ∨
    (∃ (st : AuthState) (o : Outcome), ⌜histLast M hs st ∧ R st o⌝ ∗ outRes M hs o err))

/-- No data-dependent refusal. -/
def noExtra : AuthErr → Prop := fun _ => False

/-- **A step's premises** (see the file header): at the state the transaction finds, the
revision fits a `uint64` after the bump, and a `next` state's permissions fit the cache's trees. -/
def stepOk (M : AuthMode) (hs : List AuthState) (R : StepRel) : Prop :=
  ∀ st : AuthState, histLast M hs st →
    st.revision + 1 < 2 ^ 64 ∧ ∀ (o : Outcome) (st' : AuthState), R st o → o = .next st' → permsFit st'

end res

end auth
end EtcdGrove
end Perennial
