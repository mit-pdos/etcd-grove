/-
**The authorization model** (`notes/auth-plan.md`, A0; 2026-10-23): what "permitted" means, as
a pure function of the auth store's state, and the vocabulary the apply package's and the server's
auth contracts are stated in (`apply.isAuthStore`, `notes/decisions.md` D-AU1, D-AU2).

**The state** `AuthState`: whether auth is enabled, the auth revision, the users (each the names
of its roles) and the roles (each its key permissions). A permission is `[key, rangeEnd)` in the
bytes-affine order (`GoStringLt`, Go's `bytes.Compare`): a point when `rangeEnd` is empty, open
to the end of the key space when `rangeEnd` is `"\x00"` (`isOpenEnded`), with a type `READ`,
`WRITE` or `READWRITE` (`range_perm_cache.go`, `getMergedPerms`).

**Permitted**: `permitted st ai key rangeEnd ty` is what `isOpPermitted` decides at one state
(`store.go`): with auth disabled everything; else the principal `ai` must carry a user name with a
revision that is not `0` (`granted`), the user must exist, and either has the root role or its
roles' permissions of the type cover the key (`checkKeyPoint`: some permission contains it) or the
range (`checkKeyInterval`: the union of the permissions covers every key of `[key, rangeEnd)`,
which is what an interval tree's `Contains` computes), for a request of the shape the cache
decides (`reqShape`: a non-empty key, a point, an open-ended or a proper range). The revision
check (`ErrAuthOldRevision`: a token minted before a permission change is refused) is a fact of
its own in the verdict, not of the same state (see `permitted`). `adminOk st ai` is
`IsAdminPermitted`'s: with auth disabled everything; else a named user that exists and has the
root role.

**The history** (`AuthNames`, `authHist`, `authStateAt`): the store's states in order, a
monotone list whose authority the store's admin side holds (track S of the plan) and whose
elements are persistent facts, each with valid permission keys (`permKeysOk`). A check's verdict
is stated over recorded states, in the form that is true of the Go code's checks, which read the
enabled flag, the revision, the user and the permission cache under separate locks: when the
check passes, some recorded state permitted the operation and some recorded state's revision
admitted the token; when it refuses, the four states it read (`AuthView`) refuse it
(`refusedV`; `permVerdict`, `adminVerdict`). Nothing says the states are the same, nor that any
is the latest: an admin change racing with a check can make the verdict a mix of states
(store.go's own TOCTOU), and the end-to-end statements (track A) need only the first half.

**The mode** `AuthMode` of a contract: `off` (auth disabled and never enabled: the checks pass;
what `NewAuthStore` on an empty backend gives and every closed theorem runs in), `any` (nothing is
promised of the verdicts: what the real store's proofs give until track S, unit P2's `on = true`),
`on γa` (the verdicts over the history `γa`).
-/
module

public import Code.go_etcd_io.etcd.server.v3.auth
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.GhostVar
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

instance isRoot_decidable (u : User) : Decidable (isRoot u) :=
  inferInstanceAs (Decidable (rootRole ∈ u))

/-- **The request's shape the permission cache decides** (the auth plan's S2, `cacheVerdict`):
a non-empty key, and a range that is empty (a point), open-ended or proper (`key < rangeEnd`).
The cache's interval trees take the empty key as the top of the key space, the model as its least
key, and `Contains` of an inverted range is not the model's coverage, so the cache's answer for
another request is not stated (`permitted` and `refusedV` say nothing of the coverage then). -/
def reqShape (key rangeEnd : GoString) : Prop :=
  key ≠ [] ∧ (rangeEnd = [] ∨ isOpenEnded rangeEnd ∨ go.GoStringLt key rangeEnd)

/-- The user's permissions cover the request: the point `key` when `rangeEnd` is empty
(`checkKeyPoint`), else the range (`checkKeyInterval`). -/
def covers (st : AuthState) (u : User) (op : PermType) (key rangeEnd : GoString) : Prop :=
  if rangeEnd = [] then coversPoint st u op key else coversRange st u op key rangeEnd

/-- **The principal `ai` is granted the operation at `st`** (what `isOpPermitted` decides after the
enabled flag and the revision, `store.go`): a revision that is not `0` (`ErrUserEmpty`: an
`AuthInfo{}`, no user given), a user that exists, with the root role or whose roles' permissions
of the type cover the request, for a request of the shape the cache decides (`reqShape`). -/
def granted (st : AuthState) (ai : AuthInfoM) (key rangeEnd : GoString) (op : PermType) : Prop :=
  ai.rev ≠ 0 ∧ ∃ u, st.users !! ai.user = some u ∧
    (isRoot u ∨ (reqShape key rangeEnd → covers st u op key rangeEnd))

/-- **`isOpPermitted`'s verdict at one state** for the principal `ai` on `[key, rangeEnd)` with an
operation of type `op` (see the file header): auth disabled, or the principal granted the
operation. The revision check (`ErrAuthOldRevision`: the token's revision below the store's) is
not here: the check reads the revision before the user and the cache, so a passing check need not
have seen a single state at which the user was granted *and* the revision admitted the token (an
admin change between the two reads bumps the revision and may grant the user); `permVerdict`
states it of a recorded state of its own (the auth plan's S3, 2026-10-23; until then this
predicate had it, and no proof could establish it). -/
def permitted (st : AuthState) (ai : AuthInfoM) (key rangeEnd : GoString) (op : PermType) : Prop :=
  st.enabled = false ∨ granted st ai key rangeEnd op

/-- **`IsAdminPermitted`'s verdict**: `none` is a `nil` `AuthInfo`. -/
def adminOk (st : AuthState) (ai : Option AuthInfoM) : Prop :=
  st.enabled = false ∨
  ∃ a u, ai = some a ∧ a.user ≠ [] ∧ st.users !! a.user = some u ∧ isRoot u

/-- **The states a permission check read**, one per read under its own lock (`isOpPermitted`):
the enabled flag's (`IsAuthEnabled`), the revision's (`Revision`), the user's (the backend's read
transaction) and the permission cache's (`isRangeOpPermitted`). An admin change racing with the
check can make them four different states (`store.go`'s own TOCTOU); a refusal is stated over all
four (`refusedV`), since no single one need witness it. -/
structure AuthView where
  flag : AuthState
  rev : AuthState
  user : AuthState
  cache : AuthState

/-- **`isOpPermitted` refuses in the view `v`**: auth enabled, and the revision `0`, or below the
store's, or every user of the name (none, or the one) without the root role and, for a request
of the shape the cache decides, every user of the name at the cache's state without permissions
covering the request. -/
def refusedV (v : AuthView) (ai : AuthInfoM) (key rangeEnd : GoString) (op : PermType) : Prop :=
  v.flag.enabled = true ∧
  (ai.rev = 0 ∨ ai.rev < v.rev.revision ∨
    ∀ u, v.user.users !! ai.user = some u → ¬ isRoot u ∧
      (reqShape key rangeEnd →
        ∀ u', v.cache.users !! ai.user = some u' → ¬ covers v.cache u' op key rangeEnd))

/-- **`IsAdminPermitted` refuses**, having read the flag at `sf` and the user at `su`: auth
enabled, and no principal, an unnamed one (`ErrUserEmpty`), or one whose user does not exist at
`su` (`ErrUserNotFound`) or lacks the root role (`ErrPermissionDenied`). -/
def adminRefused (sf su : AuthState) (ai : Option AuthInfoM) : Prop :=
  sf.enabled = true ∧
  ∀ a u, ai = some a → a.user ≠ [] → su.users !! a.user = some u → ¬ isRoot u

/-- At one state, for a request of the shape the cache decides, a refusal is the verdict's
negation up to the revision check. -/
theorem refusedV_diag (st : AuthState) (ai : AuthInfoM) (key rangeEnd : GoString) (op : PermType)
    (hs : reqShape key rangeEnd) :
    refusedV ⟨st, st, st, st⟩ ai key rangeEnd op ↔
      ¬ permitted st ai key rangeEnd op ∨ (st.enabled = true ∧ ai.rev < st.revision) := by
  unfold refusedV permitted granted
  constructor
  · rintro ⟨he, h⟩
    rcases h with h0 | hlt | hu
    · left
      rintro (hf | ⟨hne, -⟩)
      · rw [he] at hf; cases hf
      · exact hne h0
    · right; exact ⟨he, hlt⟩
    · left
      rintro (hf | ⟨-, u, hu', hr | hc⟩)
      · rw [he] at hf; cases hf
      · exact (hu u hu').1 hr
      · exact (hu u hu').2 hs u hu' (hc hs)
  · rintro (h | ⟨he, hlt⟩)
    · have he : st.enabled = true := by
        cases hst : st.enabled
        · exact absurd (Or.inl hst) h
        · rfl
      refine ⟨he, ?_⟩
      by_cases h0 : ai.rev = 0
      · left; exact h0
      · right; right
        intro u hu
        have hng : ¬ (isRoot u ∨ (reqShape key rangeEnd → covers st u op key rangeEnd)) :=
          fun hg => h (Or.inr ⟨h0, u, hu, hg⟩)
        refine ⟨fun hr => hng (Or.inl hr), fun _ u' hu' hc => ?_⟩
        rw [hu] at hu'; cases hu'
        exact hng (Or.inr fun _ => hc)
    · exact ⟨he, Or.inr (Or.inl hlt)⟩

/-! ## Well-formedness of a state's permissions (the request side's premises; the auth plan's S2) -/

/-- `isValidPermissionRange(key, rangeEnd)` (`range_perm_cache.go`, checked by
`RoleGrantPermission`): a non-empty key, and a point, a range with `key < rangeEnd`, or an
open-ended range. -/
def rangeValid (key rangeEnd : GoString) : Prop :=
  key ≠ [] ∧ (rangeEnd = [] ∨ go.GoStringLt key rangeEnd ∨ isOpenEnded rangeEnd)

/-- Every permission of every role has a non-empty key (`rangeValid`'s first rule): the
permission cache's interval trees take the empty key as the top of the key space (`adt.affCmp`,
the affine order), the model as its least key; the cache computes `coversPoint`/`coversRange` of
such states. -/
def permKeysOk (st : AuthState) : Prop :=
  ∀ r ps, st.roles !! r = some ps → ∀ p ∈ ps, p.key ≠ []

/-- A user's permissions fit an interval tree's count (`getMergedPerms` inserts each into a tree
whose count is a `uint64` kept below `2^63`, `adt.ownIvt`). -/
def permsFit (st : AuthState) : Prop :=
  ∀ u roles, st.users !! u = some roles → (userPerms st roles).length < 2 ^ 63

/-- A permission of the user `u` is one of a role of the state. -/
theorem mem_userPerms {st : AuthState} {u : User} {p : Perm} (h : p ∈ userPerms st u) :
    ∃ r ps, st.roles !! r = some ps ∧ p ∈ ps := by
  unfold userPerms at h
  rw [List.mem_flatMap] at h
  obtain ⟨r, -, hp⟩ := h
  cases hr : st.roles !! r with
  | none => rw [hr] at hp; cases hp
  | some ps => rw [hr] at hp; exact ⟨r, ps, hr, hp⟩

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

/-- The ghost names of an auth store's history: the monotone list of its states (`hist`), and
the ghost variable of its latest state (`cur`; the auth plan's S4, 2026-10-24): the admin side's
authority (`authOwn`, `Steps.lean`) holds one half, the store's revision invariant the other
(`revInv`, `InvAuth.lean`), so that `commitRevision`'s atomic add is to the latest state's
revision and the step it records is the model's; and the token providers' issued tokens (`tok`;
the auth plan's S5, 2026-10-24: `tokIssued`, `Tokens.lean`), a ghost map whose persistent
elements say which user a token was issued to; and the tokens not yet issued (`fresh`; the auth
plan's S5b, 2026-10-24: `tokFresh`, `Tokens.lean`), a ghost map whose exclusive elements are the
right to issue a token, which the simple provider's `assign` needs to rule out its panic on a
token issued twice. -/
structure AuthNames where
  hist : GName
  cur : GName
  tok : GName
  fresh : GName

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

/-- The history's authority: the states so far, in order (the store's admin side holds it), each
with valid permission keys (`permKeysOk`: what `isValidPermissionRange` enforces on grants and the
backend's data is assumed to have on boot; the permission cache computes the model's coverage of
such states, the auth plan's S2). -/
def authHist (γa : AuthNames) (hs : List AuthState) : IProp GF :=
  iprop(monoListAuthOwn γa.hist 1 hs ∗ ⌜∀ st ∈ hs, permKeysOk st⌝)

/-- Half of the ghost variable of the latest state (S4). -/
def authCurHalf (γa : AuthNames) (st : AuthState) : IProp GF :=
  ghostVar γa.cur (1 : Qp).half st

theorem authCurHalf_agree (γa : AuthNames) (st st' : AuthState) :
    ⊢ authCurHalf (GF := GF) γa st -∗ authCurHalf γa st' -∗ ⌜st = st'⌝ :=
  ghostVar_agree γa.cur st _ st' _

theorem authCurHalf_update (γa : AuthNames) (st st' new : AuthState) :
    ⊢ authCurHalf (GF := GF) γa st -∗ authCurHalf γa st' ==∗
      authCurHalf γa new ∗ authCurHalf γa new :=
  ghostVar_update_halves new γa.cur st st'

/-- The `i`-th state of the history (persistent), with valid permission keys. -/
def authStateAt (γa : AuthNames) (i : Nat) (st : AuthState) : IProp GF :=
  iprop(monoListIdxOwn γa.hist i st ∗ ⌜permKeysOk st⌝)

instance authStateAt_persistent (γa : AuthNames) (i : Nat) (st : AuthState) :
    Persistent (authStateAt (GF := GF) γa i st) := by
  unfold authStateAt; infer_instance

theorem authStateAt_permKeysOk (γa : AuthNames) (i : Nat) (st : AuthState) :
    authStateAt (GF := GF) γa i st ⊢ ⌜permKeysOk st⌝ := by
  unfold authStateAt
  iintro ⟨-, %H⟩
  ipureintro; exact H

theorem authStateAt_agree (γa : AuthNames) (i : Nat) (st st' : AuthState) :
    authStateAt (GF := GF) γa i st ∗ authStateAt γa i st' ⊢ ⌜st = st'⌝ := by
  unfold authStateAt
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  iapply (mono_list_idx_agree γa.hist i st st') $$ H1 H2

theorem authHist_stateAt (γa : AuthNames) (hs : List AuthState) (i : Nat) (st : AuthState)
    (h : hs[i]? = some st) : authHist (GF := GF) γa hs ⊢ authStateAt γa i st := by
  unfold authHist authStateAt
  iintro ⟨H, %Hk⟩
  isplitl [H]
  · ihave Hlb := monoListLbOwn_get γa.hist 1 hs $$ H
    iapply (monoListIdxOwn_get i st h) $$ Hlb
  · ipureintro; exact Hk st (List.mem_of_getElem? h)

theorem authHist_lookup (γa : AuthNames) (hs : List AuthState) (i : Nat) (st : AuthState) :
    authHist (GF := GF) γa hs ∗ authStateAt γa i st ⊢ ⌜hs[i]? = some st⌝ := by
  unfold authHist authStateAt
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  iapply (mono_list_auth_idx_lookup γa.hist 1 hs i st) $$ H1 H2

/-- A history and its latest state's ghost variable, both halves, with the token providers'
issued tokens under `γt` (allocated with the provider, `tokAlloc`, `Tokens.lean`) and the fresh
tokens under `γf` (`Tokens.lean`, S5b). -/
theorem authHist_alloc (γt γf : GName) (hs : List AuthState) (cur : AuthState)
    (hk : ∀ st ∈ hs, permKeysOk st) :
    ⊢ |==> ∃ γa : AuthNames, ⌜γa.tok = γt ∧ γa.fresh = γf⌝ ∗ authHist (GF := GF) γa hs ∗
      authCurHalf γa cur ∗
      authCurHalf γa cur := by
  unfold authHist authCurHalf
  iintro
  imod (mono_list_own_alloc (GF := GF) hs) with ⟨%γ, H, -⟩
  imod (ghostVar_alloc (GF := GF) cur) with ⟨%γc, Hc⟩
  imodintro
  iexists ⟨γ, γc, γt, γf⟩
  iframe H
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitr
  · ipureintro; exact hk
  · iapply (ghostVar_split_half γc 1 cur).1 $$ Hc

theorem authHist_append (γa : AuthNames) (hs : List AuthState) (st : AuthState)
    (hk : permKeysOk st) : authHist (GF := GF) γa hs ⊢ |==> authHist γa (hs ++ [st]) := by
  unfold authHist
  iintro ⟨H, %Hk⟩
  imod (monoListAuthOwn_update_app (γ := γa.hist) (l := hs) [st]) $$ H with ⟨H, -⟩
  imodintro
  iframe H
  ipureintro
  intro x hx
  rw [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact Hk x hx
  · exact hk

/-- The view's four states are recorded (persistent). -/
def recordedV (γa : AuthNames) (v : AuthView) : IProp GF :=
  iprop((∃ i : Nat, authStateAt γa i v.flag) ∗ (∃ i : Nat, authStateAt γa i v.rev) ∗
    (∃ i : Nat, authStateAt γa i v.user) ∗ (∃ i : Nat, authStateAt γa i v.cache))

instance recordedV_persistent (γa : AuthNames) (v : AuthView) :
    Persistent (recordedV (GF := GF) γa v) := by
  unfold recordedV; infer_instance

/-- Four recorded states as a view. -/
theorem recordedV_intro (γa : AuthNames) (i j k l : Nat) (a b c d : AuthState) :
    authStateAt (GF := GF) γa i a ⊢ authStateAt γa j b -∗ authStateAt γa k c -∗
      authStateAt γa l d -∗ recordedV γa ⟨a, b, c, d⟩ := by
  unfold recordedV
  iintro Ha Hb Hc Hd
  isplitl [Ha]
  · iexists i; iexact Ha
  isplitl [Hb]
  · iexists j; iexact Hb
  isplitl [Hc]
  · iexists k; iexact Hc
  · iexists l; iexact Hd

/-- One recorded state, as every state of the view. -/
theorem recordedV_diag (γa : AuthNames) (i : Nat) (st : AuthState) :
    authStateAt (GF := GF) γa i st ⊢ recordedV γa ⟨st, st, st, st⟩ := by
  unfold recordedV
  iintro #H
  iframe #

/-- **A permission check's verdict** in the mode `M` (persistent; see the file header): `off`,
the check passed; `any`, nothing; `on γa`: if it passed, a recorded state that permitted the
operation (`permitted`: auth disabled, or the user granted it) and a recorded state whose
revision admitted the token (or at which auth was disabled); if it refused, a view of four
recorded states in which it refuses (`refusedV`). -/
def permVerdict (M : AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (key rangeEnd : GoString) (op : PermType) (err : GoInterface) : IProp GF :=
  match M with
  | .off => iprop(⌜err = GoInterface.nil⌝)
  | .any => iprop(True)
  | .on γa =>
      iprop((∃ (i : Nat) (st : AuthState), authStateAt γa i st ∗
          ⌜err = GoInterface.nil → permitted st (authInfoM info) key rangeEnd op⌝) ∗
        (∃ (i : Nat) (st : AuthState), authStateAt γa i st ∗
          ⌜err = GoInterface.nil → st.enabled = false ∨ st.revision ≤ (authInfoM info).rev⌝) ∗
        (∃ v : AuthView, recordedV γa v ∗
          ⌜err ≠ GoInterface.nil → refusedV v (authInfoM info) key rangeEnd op⌝))

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

/-- **`IsAdminPermitted`'s verdict** in the mode `M` (persistent), for the `AuthInfo` `ai`
(`none`: a `nil` pointer): `on γa`, if it passed a recorded state at which the principal is admin
(`adminOk`), if it refused the recorded states of the flag and of the user in which it refuses
(`adminRefused`). -/
def adminVerdict (M : AuthMode) (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (err : GoInterface) : IProp GF :=
  match M with
  | .off => iprop(⌜err = GoInterface.nil⌝)
  | .any => iprop(True)
  | .on γa =>
      iprop((∃ (i : Nat) (st : AuthState), authStateAt γa i st ∗
          ⌜err = GoInterface.nil → adminOk st (ai.map authInfoM)⌝) ∗
        (∃ (i j : Nat) (sf su : AuthState), authStateAt γa i sf ∗ authStateAt γa j su ∗
          ⌜err ≠ GoInterface.nil → adminRefused sf su (ai.map authInfoM)⌝))

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
