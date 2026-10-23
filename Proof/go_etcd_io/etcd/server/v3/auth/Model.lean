/-
**The authorization model** (`notes/auth-plan.md`, A0; 2026-10-23): what "permitted" means, as
a pure function of the auth store's state, and the vocabulary the apply package's and the server's
auth contracts are stated in (`apply.isAuthStore`, `notes/decisions.md` D-AU1, D-AU2).

**The state** `AuthState`: whether auth is enabled, the auth revision, the users (each the names
of its roles) and the roles (each its key permissions). A permission is `[key, rangeEnd)` in the
bytes-affine order (`GoStringLt`, Go's `bytes.Compare`): a point when `rangeEnd` is empty, open
to the end of the key space when `rangeEnd` is `"\x00"` (`isOpenEnded`), with a type `READ`,
`WRITE` or `READWRITE` (`range_perm_cache.go`, `getMergedPerms`).

**Permitted**: `permitted st ai key rangeEnd ty` is what `isOpPermitted` decides (`store.go`): with
auth disabled everything; else the principal `ai` must carry a user name with a revision that is
not `0` and not older than the store's (`ErrAuthOldRevision`: a token minted before a permission
change is refused), the user must exist, and either has the root role or its roles' permissions
of the type cover the key (`checkKeyPoint`: some permission contains it) or the range
(`checkKeyInterval`: the union of the permissions covers every key of `[key, rangeEnd)`, which is
what an interval tree's `Contains` computes). `adminOk st ai` is `IsAdminPermitted`'s: with auth
disabled everything; else a named user that exists and has the root role.

**The history** (`AuthNames`, `authHist`, `authStateAt`): the store's states in order, a
monotone list whose authority the store's admin side holds (track S of the plan) and whose
elements are persistent facts. A check's verdict is stated over recorded states, in the form that
is true of the Go code's checks, which read the enabled flag, the revision, the user and the
permission cache under separate locks: when the check passes, some recorded state permitted the
operation; when it refuses, some recorded state did not (`permVerdict`, `adminVerdict`). Nothing
says the two are the same state, nor that the state is the latest: an admin change racing with a
check can make the verdict a mix of two states (store.go's own TOCTOU), and the end-to-end
statements (track A) need only the first half.

**The mode** `AuthMode` of a contract: `off` (auth disabled and never enabled: the checks pass;
what `NewAuthStore` on an empty backend gives and every closed theorem runs in), `any` (nothing is
promised of the verdicts: what the real store's proofs give until track S, unit P2's `on = true`),
`on γa` (the verdicts over the history `γa`).
-/
module

public import Code.go_etcd_io.etcd.server.v3.auth
public import Perennial.Ghost.MonoList
public import Perennial.Golang.Theory.String
public import Perennial.Std.GMap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI

/-! ## The pure model -/

/-- A permission's type (`authpb.Permission_Type`: `READ = 0`, `WRITE = 1`, `READWRITE = 2`). -/
inductive PermType where
  | read
  | write
  | readwrite
  deriving DecidableEq, Inhabited

/-- `authpb.Permission_Type`'s value. -/
def PermType.toFin : PermType → Fin 3
  | .read => 0
  | .write => 1
  | .readwrite => 2

def PermType.ofFin : Fin 3 → PermType
  | 0 => .read
  | 1 => .write
  | 2 => .readwrite

@[simp] theorem PermType.ofFin_toFin (t : PermType) : PermType.ofFin t.toFin = t := by
  cases t <;> rfl

/-- Whether a permission of type `t` grants reads (resp. writes). -/
def PermType.grantsRead : PermType → Bool
  | .write => false
  | _ => true

def PermType.grantsWrite : PermType → Bool
  | .read => false
  | _ => true

/-- Whether a permission of type `t` grants an operation of type `op` (`op` is `read` for a
range, `write` for a put or a delete). -/
def PermType.grants (t op : PermType) : Bool :=
  match op with
  | .read => t.grantsRead
  | .write => t.grantsWrite
  | .readwrite => t.grantsRead && t.grantsWrite

/-- A key permission (`authpb.Permission`): `[key, rangeEnd)`. -/
structure Perm where
  key : GoString
  rangeEnd : GoString
  ty : PermType
  deriving DecidableEq, Inhabited

/-- A role: its key permissions (`authpb.Role.KeyPermission`). -/
abbrev Role := List Perm

/-- A user: the names of its roles (`authpb.User.Roles`). -/
abbrev User := List GoString

/-- The auth store's state. -/
structure AuthState where
  enabled : Bool
  revision : Nat
  users : GMap GoString User
  roles : GMap GoString Role
  deriving Inhabited

/-- The principal a check is given: `AuthInfo`'s user name and revision. -/
structure AuthInfoM where
  user : GoString
  rev : Nat
  deriving DecidableEq, Inhabited

/-- The principal of a Go `AuthInfo`. -/
def authInfoM [FfiSyntax] (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) : AuthInfoM :=
  ⟨info.Username', uint.nat info.Revision'⟩

/-- The root role's name (`store.go`, `rootRole`). -/
def rootRole : GoString := go!"root"

/-- `rangeEnd` is `"\x00"`: the range is open to the end of the key space (`isOpenEnded`). -/
def isOpenEnded (rangeEnd : GoString) : Prop := rangeEnd = [(0 : w8)]

/-- The key `k` is in the range `[key, rangeEnd)`: the point `key` when `rangeEnd` is empty, every
key at or after `key` when it is open-ended, `key ≤ k < rangeEnd` otherwise. -/
def inRange (key rangeEnd k : GoString) : Prop :=
  if rangeEnd = [] then k = key
  else go.GoStringLe key k ∧ (isOpenEnded rangeEnd ∨ go.GoStringLt k rangeEnd)

/-- The permission `p` covers the key `k` for operations of type `op`. -/
def Perm.covers (p : Perm) (op : PermType) (k : GoString) : Prop :=
  p.ty.grants op = true ∧ inRange p.key p.rangeEnd k

/-- The permissions of the user `u` in `st`: those of its roles that exist (`getMergedPerms`
skips a missing role). -/
def userPerms (st : AuthState) (u : User) : List Perm :=
  u.flatMap fun r => (st.roles !! r).getD []

/-- The user's permissions cover the key `k` (`checkKeyPoint`: `Intersects` of the point). -/
def coversPoint (st : AuthState) (u : User) (op : PermType) (k : GoString) : Prop :=
  ∃ p ∈ userPerms st u, p.covers op k

/-- The user's permissions cover every key of `[key, rangeEnd)` (`checkKeyInterval`: the interval
tree's `Contains`, the union of the permissions' intervals). -/
def coversRange (st : AuthState) (u : User) (op : PermType) (key rangeEnd : GoString) : Prop :=
  ∀ k, inRange key rangeEnd k → ∃ p ∈ userPerms st u, p.covers op k

/-- The user `u` has the root role. -/
def isRoot (u : User) : Prop := rootRole ∈ u

/-- **`isOpPermitted`'s verdict** for the principal `ai` on `[key, rangeEnd)` with an operation of
type `op` (see the file header). -/
def permitted (st : AuthState) (ai : AuthInfoM) (key rangeEnd : GoString) (op : PermType) : Prop :=
  st.enabled = false ∨
  (ai.rev ≠ 0 ∧ st.revision ≤ ai.rev ∧
    ∃ u, st.users !! ai.user = some u ∧
      (isRoot u ∨
        (if rangeEnd = [] then coversPoint st u op key else coversRange st u op key rangeEnd)))

/-- **`IsAdminPermitted`'s verdict**: `none` is a `nil` `AuthInfo`. -/
def adminOk (st : AuthState) (ai : Option AuthInfoM) : Prop :=
  st.enabled = false ∨
  ∃ a u, ai = some a ∧ a.user ≠ [] ∧ st.users !! a.user = some u ∧ isRoot u

/-! ## Countability (for the history's ghost list) -/

/-- `Perm` as a tuple, with its inverse: `countableOfLeftInverse`. -/
def Perm.enc (p : Perm) : GoString × GoString × Fin 3 := (p.key, p.rangeEnd, p.ty.toFin)

def Perm.dec (x : GoString × GoString × Fin 3) : Perm := ⟨x.1, x.2.1, PermType.ofFin x.2.2⟩

theorem Perm.dec_enc (p : Perm) : Perm.dec (Perm.enc p) = p := by
  cases p; simp [Perm.enc, Perm.dec]

instance Perm.countable : Pos.Countable Perm := countableOfLeftInverse Perm.enc Perm.dec Perm.dec_enc

def AuthState.enc (st : AuthState) : Bool × Nat × GMap GoString User × GMap GoString Role :=
  (st.enabled, st.revision, st.users, st.roles)

def AuthState.dec (x : Bool × Nat × GMap GoString User × GMap GoString Role) : AuthState :=
  ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩

theorem AuthState.dec_enc (st : AuthState) : AuthState.dec (AuthState.enc st) = st := by
  cases st; rfl

instance AuthState.countable : Pos.Countable AuthState :=
  countableOfLeftInverse AuthState.enc AuthState.dec AuthState.dec_enc

/-! ## The mode and the history -/

/-- The ghost name of an auth store's history. -/
abbrev AuthNames := GName

/-- **A contract's mode** (see the file header). -/
inductive AuthMode where
  /-- auth disabled, never enabled: the checks pass (`NewAuthStore` on an empty backend) -/
  | off
  /-- nothing promised of the verdicts (the real store's proofs until track S) -/
  | any
  /-- the verdicts over the history `γa` -/
  | on (γa : AuthNames)

/-- Whether the mode may refuse (the chain model's `Chain.auth on`). -/
def AuthMode.isOn : AuthMode → Bool
  | .off => false
  | _ => true

@[simp] theorem AuthMode.isOn_off : AuthMode.off.isOn = false := rfl
@[simp] theorem AuthMode.isOn_any : AuthMode.any.isOn = true := rfl
@[simp] theorem AuthMode.isOn_on (γa : AuthNames) : (AuthMode.on γa).isOn = true := rfl

theorem AuthMode.isOn_false_iff (M : AuthMode) : M.isOn = false ↔ M = .off := by
  cases M <;> simp [AuthMode.isOn]

section ghost
variable [FfiSyntax] {GF : BundledGFunctors} [AllG GF]

/-- The history's authority: the states so far, in order (the store's admin side holds it). -/
def authHist (γa : AuthNames) (hs : List AuthState) : IProp GF := monoListAuthOwn γa 1 hs

/-- The `i`-th state of the history (persistent). -/
def authStateAt (γa : AuthNames) (i : Nat) (st : AuthState) : IProp GF := monoListIdxOwn γa i st

instance authStateAt_persistent (γa : AuthNames) (i : Nat) (st : AuthState) :
    Persistent (authStateAt (GF := GF) γa i st) := by
  unfold authStateAt; infer_instance

theorem authStateAt_agree (γa : AuthNames) (i : Nat) (st st' : AuthState) :
    authStateAt (GF := GF) γa i st ∗ authStateAt γa i st' ⊢ ⌜st = st'⌝ := by
  unfold authStateAt
  iintro ⟨H1, H2⟩
  iapply (mono_list_idx_agree γa i st st') $$ H1 H2

theorem authHist_stateAt (γa : AuthNames) (hs : List AuthState) (i : Nat) (st : AuthState)
    (h : hs[i]? = some st) : authHist (GF := GF) γa hs ⊢ authStateAt γa i st := by
  unfold authHist authStateAt
  iintro H
  ihave Hlb := monoListLbOwn_get γa 1 hs $$ H
  iapply (monoListIdxOwn_get i st h) $$ Hlb

theorem authHist_lookup (γa : AuthNames) (hs : List AuthState) (i : Nat) (st : AuthState) :
    authHist (GF := GF) γa hs ∗ authStateAt γa i st ⊢ ⌜hs[i]? = some st⌝ := by
  unfold authHist authStateAt
  iintro ⟨H1, H2⟩
  iapply (mono_list_auth_idx_lookup γa 1 hs i st) $$ H1 H2

theorem authHist_alloc (hs : List AuthState) : ⊢ |==> ∃ γa : AuthNames, authHist (GF := GF) γa hs := by
  unfold authHist
  iintro
  imod (mono_list_own_alloc (GF := GF) hs) with ⟨%γ, H, -⟩
  imodintro
  iexists γ
  iexact H

theorem authHist_append (γa : AuthNames) (hs : List AuthState) (st : AuthState) :
    authHist (GF := GF) γa hs ⊢ |==> authHist γa (hs ++ [st]) := by
  unfold authHist
  iintro H
  imod (monoListAuthOwn_update_app (γ := γa) (l := hs) [st]) $$ H with ⟨H, -⟩
  imodintro
  iexact H

/-- **A permission check's verdict** in the mode `M` (persistent; see the file header): `off`,
the check passed; `any`, nothing; `on γa`, a recorded state that permitted the operation if it
passed, a recorded state that did not if it refused. -/
def permVerdict (M : AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (key rangeEnd : GoString) (op : PermType) (err : GoInterface) : IProp GF :=
  match M with
  | .off => iprop(⌜err = GoInterface.nil⌝)
  | .any => iprop(True)
  | .on γa =>
      iprop((∃ (i : Nat) (st : AuthState), authStateAt γa i st ∗
          ⌜err = GoInterface.nil → permitted st (authInfoM info) key rangeEnd op⌝) ∗
        (∃ (i : Nat) (st : AuthState), authStateAt γa i st ∗
          ⌜err ≠ GoInterface.nil → ¬ permitted st (authInfoM info) key rangeEnd op⌝))

instance permVerdict_persistent (M : AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (key rangeEnd : GoString) (op : PermType) (err : GoInterface) :
    Persistent (permVerdict (GF := GF) M info key rangeEnd op err) := by
  unfold permVerdict; cases M <;> infer_instance

theorem permVerdict_any (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString)
    (op : PermType) (err : GoInterface) : ⊢ permVerdict (GF := GF) .any info key rangeEnd op err := by
  unfold permVerdict; itrivial

theorem permVerdict_off (M : AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (key rangeEnd : GoString) (op : PermType) (err : GoInterface) :
    permVerdict (GF := GF) M info key rangeEnd op err ⊢ ⌜M = .off → err = GoInterface.nil⌝ := by
  cases M
  · unfold permVerdict; iintro %H; ipureintro; intro _; exact H
  · unfold permVerdict; iintro -; ipureintro; intro h; cases h
  · unfold permVerdict; iintro -; ipureintro; intro h; cases h

/-- **`IsAdminPermitted`'s verdict** in the mode `M` (persistent), for the `AuthInfo` `a`
(`none`: a `nil` pointer). -/
def adminVerdict (M : AuthMode) (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (err : GoInterface) : IProp GF :=
  match M with
  | .off => iprop(⌜err = GoInterface.nil⌝)
  | .any => iprop(True)
  | .on γa =>
      iprop((∃ (i : Nat) (st : AuthState), authStateAt γa i st ∗
          ⌜err = GoInterface.nil → adminOk st (ai.map authInfoM)⌝) ∗
        (∃ (i : Nat) (st : AuthState), authStateAt γa i st ∗
          ⌜err ≠ GoInterface.nil → ¬ adminOk st (ai.map authInfoM)⌝))

instance adminVerdict_persistent (M : AuthMode) (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (err : GoInterface) : Persistent (adminVerdict (GF := GF) M ai err) := by
  unfold adminVerdict; cases M <;> infer_instance

theorem adminVerdict_any (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) (err : GoInterface) :
    ⊢ adminVerdict (GF := GF) .any ai err := by
  unfold adminVerdict; itrivial

theorem adminVerdict_off (M : AuthMode) (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (err : GoInterface) :
    adminVerdict (GF := GF) M ai err ⊢ ⌜M = .off → err = GoInterface.nil⌝ := by
  cases M
  · unfold adminVerdict; iintro %H; ipureintro; intro _; exact H
  · unfold adminVerdict; iintro -; ipureintro; intro h; cases h
  · unfold adminVerdict; iintro -; ipureintro; intro h; cases h

/-- **`IsAuthEnabled`'s answer** in the mode `M` (persistent): `off`, `false`; `any`, anything;
`on γa`, some recorded state's flag. -/
def enabledVerdict (M : AuthMode) (b : Bool) : IProp GF :=
  match M with
  | .off => iprop(⌜b = false⌝)
  | .any => iprop(True)
  | .on γa => iprop(∃ (i : Nat) (st : AuthState), authStateAt γa i st ∗ ⌜b = st.enabled⌝)

instance enabledVerdict_persistent (M : AuthMode) (b : Bool) :
    Persistent (enabledVerdict (GF := GF) M b) := by
  unfold enabledVerdict; cases M <;> infer_instance

theorem enabledVerdict_any (b : Bool) : ⊢ enabledVerdict (GF := GF) .any b := by
  unfold enabledVerdict; itrivial

/-- **`Revision`'s answer** in the mode `M` (persistent): `on γa`, some recorded state's revision. -/
def revisionVerdict (M : AuthMode) (x : w64) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (i : Nat) (st : AuthState), authStateAt γa i st ∗ ⌜uint.nat x = st.revision⌝)
  | _ => iprop(True)

instance revisionVerdict_persistent (M : AuthMode) (x : w64) :
    Persistent (revisionVerdict (GF := GF) M x) := by
  unfold revisionVerdict; cases M <;> infer_instance

theorem revisionVerdict_any (x : w64) : ⊢ revisionVerdict (GF := GF) .any x := by
  unfold revisionVerdict; itrivial

end ghost

end auth
end EtcdGrove
end Perennial
