/-
# etcd's auth store (`server/auth`, batch 3d): vocabulary

One member's auth store (`*authStore`, `store.go`, `range_perm_cache.go`) and its token providers
(`simple_token.go`, `nop.go`; `jwt.go` untranslated, assumed). Namespace `Auth`.

## The shape, in words

**The store's state is W0's `AuthState`** (`api/v3/Model.lean`: the enabled flag, the auth revision,
the users with their passwords and roles, the roles with their permissions). The store keeps a
**history** of the states it has been in, numbered `0, 1, 2, …`: `authAt γa i a` (persistent) says
its `i`-th state is `a`. **Every recorded state is a state the cluster `γ` has reached**
(`authAt_reached`: an `etcdLb γ σ` with `σ.auth = a`), because the only writer, the member's apply
thread, moves the store along the committed log (`admStep`, `Recover`) and supplies that fact for
each state it records. The history is a chain of the model's admin steps (`authAt_reach`).

**One writer** (`authCur γa i a`, exclusive): the apply thread (3a's appliers, 2d's snapshot
install, 2e's boot) holds the store's current state; every admin method takes it and returns it
at `i + 1` with the step's state (the same state for an error: a duplicate entry of the history).
Between two writer calls every view of the store is at the current state (`authCur_at` gives
`authLb γa i`), so a check made by the writer answers at exactly `a`.

**Readers** (any goroutine: the gRPC handlers' `AuthInfoFromCtx`, the request path's checks, the
watch server's) read **four views** that move at different moments: the enabled flag
(`enabledMu`), the revision atomic, the backend's read transaction (`lockedReadTx`), the permission
cache (`rangePermCache`). An admin step changes them one after the other (`commitRevision` bumps
the atomic, `refreshRangePermCache` rebuilds the cache, the batch transaction's `Unlock` publishes
the users and roles, the flag last), so a reader may see two consecutive states at once. Each
reader's spec says **at which recorded state each view it read was**, from a lower bound `authLb
γa i0` it holds (every view is at or after `i0`): `checkOk`/`checkDenied` for the permission
checks (the flag at `jf`, the backend at `jx`, the cache at `jc`). A pass is justified at
one recorded state (the flag's, the backend's or the cache's); a denial in general is not (the
views may straddle an `AuthDisable` and a role revocation: the guarantee is exactly the three
views). **This is the timing of `nonissues/etcd-doserialize-auth-enable-race.md` and of
`nonissues/etcd-auth-revision-before-visible.md`**: a reader's revision (the atomic) may be one step
ahead of its backend and cache views, so "the revision did not change" does not mean "the check's
state is the read's state". W0's round 6 admits it for linearizable reads (`State.permittedSince`:
a permission at some auth state since the call started).

**Tokens** name users as the cluster issued them: W0's `tokenUser γ tok u`. A token the store
accepts (`AuthInfoFromCtx`) maps to a user `u` with `tokenUser γ tok u`; a token it assigns
(`Authenticate`, `WithRoot`) is one. The simple provider's tokens are `prefix.index` with `index` the
`Authenticate` entry's log index: assigning one twice panics (`assignSimpleTokenToUser`), so its
right is the once-only `tokFrom γa n` (no index above `n` assigned yet), and `WithRoot`'s index `0`
token needs `rootTokOk γa` (`nonissues/etcd-auth-withroot-token-collision-panic.md`: two random
prefixes may collide; the simple provider does not give it).

**Passwords**: W0's model keeps a user's stored credential (`UserRec.password`, the hash the
proposer computed, `pwHash pw cred`) and checks a password with `pwMatch cred pw` (bcrypt's
`CompareHashAndPassword`: the boundary `Spec/golang_org/x/crypto/bcrypt/`). The request carries the
credential base64-encoded (`b64 cred`, `authReqAt`). `CheckPassword` passes for the user's password and may pass for others (bcrypt's
72-byte limit and collisions: the boundary assumes no rejection).

**Mode.** Auth on and off are values of `a.enabled`, not two specs (`auth-component.md`).

## Vocabulary

Pure: `AuthErr` (the package's error variables) with `AuthErr.etcd` (`togRPCError`'s table),
`AuthErr.global` (its package variable), `AuthErr.msg` (its message),
`rngInverted` (W0's `KeyRange.inverted`), `validPerms` (W0's `KeyRange.validPerm` of every
permission), `recordsFit` (opaque: bbolt's limits, 4b's `Schema.putFits` of 3h's `authpb` encoding), `admStep rq a a' res` (W0's `authStep` effect of an admin request at an authorized
caller), `storeNext rq cred a` (the store's next state, a function), `AuthReach`,
`checkOk`/`checkDenied`, `mdToken`, `tokKeysOk`, `trimBearer`, `simpleTok`, `b64` (opaque,
provisional: `encoding/base64`'s boundary).

Resources: `AuthNames` (opaque ghost names); `authStoreAt st γ γa` (persistent: `st` is a member's
store over cluster `γ`); `authCur γa i a` (exclusive: the writer); `authAt γa i a`, `authLb γa i`
(persistent); `tokFrom γa n` (exclusive), `rootTokOk γa`; `authnCtx γ ctx name idx` (transparent,
persistent: an `Authenticate` context, over `ctxValIs`); `tokenProviderAt tp γ R rt` (exclusive: a
provider not yet given to a store; `R`: its `info` runs once `R` holds; `rt`: it can issue root
tokens without a collision), `authGate γa R` (persistent: the store's checks run once `R` holds);
`authBackendAt be a` (exclusive: an `AuthBackend` holding `a`; 3d's own, introduced by 4a/4b),
`authBeCur γa be` (exclusive: the store's current backend, the writer's), `authBeHook be Pre Q` (the
backend's post-lock hook run, one use; introduced by 4a; the writer's methods take it with
`authBeCur`, `hookOut`); `authReqAt r rq cred`, `authRespAt rq res p`,
`authnRespAt p tok` (provisional: 3h's messages), `authInfoAt ai dq u rev` (the `AuthInfo`);
`ctxInMD ctx o`, `ctxCertUser ctx c`, `ctxPeerCN ctx c` (grpc's, abbreviations since the verify
round; `ctxToken` transparent over them); `errIs ae v` (the error variable's value: `init` gives
them, existentially). From W0: `pwHash`/`pwMatch`, `tokenUser` (`tokenUser_agree`), `authStep` (its
`lo` only matters for `authenticate`, which no admin method takes), `State.invertedDeny`,
`State.permittedSince`, `etcdLb_noEmptyUser`.

## Intended realization

* `AuthNames`: the history's `mono_list` (`γa.hist`), the cluster `γ`, the token map's ghost
  (`γa.tok`: each assigned simple token's user and index), the provider's kind, the gate `R`, the
  current backend's ghost variable (`authBeCur`'s other half, in `beMu`'s invariant).
* `authStoreAt st γ γa`: `st`'s read-only fields (`lg`, `tokenProvider`, `bcryptCost` in
  `[MinCost, MaxCost]`); `enabledMu`'s invariant (`enabled` at the flag view's state; the writer's
  half), `beMu`'s (the current `AuthBackend` with its contract at the backend view's state),
  `rangePermCacheMu`'s (the map at the cache view's state: each entry `getMergedPerms` of one user
  at that state, as interval trees, 3f's `adt` vocabulary), the revision atomic's invariant (its
  value the revision of the history's last or second-to-last state); the history's authority with,
  for every recorded state, `etcdLb γ σ ∗ ⌜σ.auth = a⌝` and `validPerms a`, and the view indices
  (each at the last or second-to-last state, `authLb`'s lower bounds); the provider's contract
  (`tokenProviderAt`'s, opened).
* `authCur γa i a`: the history's last index and state, the writer's half of `enabled`, the right
  to lock the batch transaction (4b; a lock gives the session and 4a's `beTurn`, both given back by
  the same method's `Unlock`, so nothing of them crosses a call), `bcryptCost`.
* `authBeCur γa be`: the writer's half of the field `as.be ↦{1/2} be` (with the ghost variable
  holding `be`), whose other half `beMu`'s invariant keeps: the admin methods read `as.be` without
  `beMu` (`store.go:433`, `UserAdd`; the writer is the only one to write it), the permission checks
  under `beMu`'s read lock (`lockedReadTx`, `:942`) from the invariant's half, and `Recover` writes it
  under `beMu.Lock` with both halves (`:399-402`) (re-review N1: no store-indexed hook, so `Recover`'s
  move of it leaves no stale hook behind; verify-round cleanup, RR-grpc-auth: the field share, not
  "read under `beMu`").
* `tokFrom γa n`: the simple provider's map holds no token of an index above `n` (the half of the
  index bound; the other half in the map's lock invariant). JWT and no-op: `True`.
* `authGate γa R`: `γa`'s recorded gate is `R` (a saved proposition), the provider's.

## Laws

`authStoreAt_persistent`, `authAt_persistent`, `authLb_persistent`, `authCur_timeless`,
`authAt_timeless`, `authLb_timeless`, `rootTokOk_persistent`, `authnCtx_persistent`,
`errIs_persistent`, `authGate_persistent`, `authBeCur_timeless`, `authReqAt_persistent`;
`authCur_excl`, `authBeCur_excl`, `authCur_at`, `authAt_agree`, `authAt_le`, `authLb_le`,
`authLb_mono`, `authAt_reach`, `authAt_reached`, `authAt_valid`, `tokFrom_excl`,
`authStoreAt_agree`, `authStoreAt_lb`; `init`; `storeNext_adm`,
`authReach_of_reach`, `authRespAt_ne_null`, `authnRespAt_ne_null`. (Verify round: `errOf_ne_nil`,
`errOf_inj` gone with `errOf`, whose facts `init` now gives; the tie of the mapped errors to the
server's sentinels is server-core's `authErr_srv` (`etcdserver/errors`, over `errIs`).)

## Requirement snippets

`examples/specreq/auth/`: `check.go` (a permission check as the request path and the watch server
make it: a pass is a reached state's permission; the writer's check at its own state), `token.go`
(the context's token to its user; `WithRoot`'s context; an invalid token refused), `admin.go` (the
apply thread's admin steps and their errors; `CheckPassword` after `UserAdd`; the revision bumped by
a change), `boot.go` (`NewTokenProvider` and `NewAuthStore` at boot, `Recover` at a snapshot,
`Close`).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.State
public import Spec.golang_org.x.crypto.bcrypt.Api
public import Spec.google_golang_org.grpc.Api
public import Spec.context.Api
public import Perennial.Proof.errors.NewVar
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.auth
public import GeneratedProof.go_etcd_io.etcd.server.v3.auth

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Auth

open Iris Iris.BI EtcdModel
open Classical

/-! ## The package's errors -/

/-- The auth package's error variables (`store.go`'s `Err*`, the ones the translated code returns). -/
inductive AuthErr where
  | rootUserNotExist | rootRoleNotExist | userAlreadyExist | userEmpty | userNotFound
  | roleAlreadyExist | roleNotFound | roleEmpty | permissionNotGiven | authFailed
  | noPasswordUser | permissionDenied | roleNotGranted | permissionNotGranted | authNotEnabled
  | authOldRevision | invalidAuthToken | invalidAuthOpts | invalidAuthMgmt

/-- **`togRPCError`'s table** (`api/v3rpc/util.go`): the client-facing error of each, `none` for the
two it does not map (`ErrNoPasswordUser`, `ErrInvalidAuthOpts`: a gRPC `Unknown`). -/
def AuthErr.etcd : AuthErr → Option EtcdErr
  | .rootUserNotExist => some .rootUserNotExist
  | .rootRoleNotExist => some .rootRoleNotExist
  | .userAlreadyExist => some .userAlreadyExist
  | .userEmpty => some .userEmpty
  | .userNotFound => some .userNotFound
  | .roleAlreadyExist => some .roleAlreadyExist
  | .roleNotFound => some .roleNotFound
  | .roleEmpty => some .roleEmpty
  | .permissionNotGiven => some .permissionNotGiven
  | .authFailed => some .authFailed
  | .noPasswordUser => none
  | .permissionDenied => some .permissionDenied
  | .roleNotGranted => some .roleNotGranted
  | .permissionNotGranted => some .permissionNotGranted
  | .authNotEnabled => some .authNotEnabled
  | .authOldRevision => some .authOldRevision
  | .invalidAuthToken => some .invalidAuthToken
  | .invalidAuthOpts => none
  | .invalidAuthMgmt => some .invalidAuthMgmt

section errnames
variable [GooseExts] [GoGlobalContext]
open go_etcd_io.etcd.server.v3.auth

/-- **The package variable of each error** (`store.go:46-68`). -/
def AuthErr.global : AuthErr → GoString
  | .rootUserNotExist => ErrRootUserNotExist
  | .rootRoleNotExist => ErrRootRoleNotExist
  | .userAlreadyExist => ErrUserAlreadyExist
  | .userEmpty => ErrUserEmpty
  | .userNotFound => ErrUserNotFound
  | .roleAlreadyExist => ErrRoleAlreadyExist
  | .roleNotFound => ErrRoleNotFound
  | .roleEmpty => ErrRoleEmpty
  | .permissionNotGiven => ErrPermissionNotGiven
  | .authFailed => ErrAuthFailed
  | .noPasswordUser => ErrNoPasswordUser
  | .permissionDenied => ErrPermissionDenied
  | .roleNotGranted => ErrRoleNotGranted
  | .permissionNotGranted => ErrPermissionNotGranted
  | .authNotEnabled => ErrAuthNotEnabled
  | .authOldRevision => ErrAuthOldRevision
  | .invalidAuthToken => ErrInvalidAuthToken
  | .invalidAuthOpts => ErrInvalidAuthOpts
  | .invalidAuthMgmt => ErrInvalidAuthMgmt

end errnames

/-- **Each error's message** (its `errors.New` text, `store.go:46-68`). -/
def AuthErr.msg : AuthErr → GoString
  | .rootUserNotExist => go!"auth: root user does not exist"
  | .rootRoleNotExist => go!"auth: root user does not have root role"
  | .userAlreadyExist => go!"auth: user already exists"
  | .userEmpty => go!"auth: user name is empty"
  | .userNotFound => go!"auth: user not found"
  | .roleAlreadyExist => go!"auth: role already exists"
  | .roleNotFound => go!"auth: role not found"
  | .roleEmpty => go!"auth: role name is empty"
  | .permissionNotGiven => go!"auth: permission not given"
  | .authFailed => go!"auth: authentication failed, invalid user ID or password"
  | .noPasswordUser => go!"auth: authentication failed, password was given for no password user"
  | .permissionDenied => go!"auth: permission denied"
  | .roleNotGranted => go!"auth: role is not granted to the user"
  | .permissionNotGranted => go!"auth: permission is not granted to the role"
  | .authNotEnabled => go!"auth: authentication is not enabled"
  | .authOldRevision => go!"auth: revision in header is old"
  | .invalidAuthToken => go!"auth: invalid auth token"
  | .invalidAuthOpts => go!"auth: invalid auth options"
  | .invalidAuthMgmt => go!"auth: invalid auth management"

/-! ## Pure: ranges, states, steps -/

/-- **An inverted range**: a proper `rangeEnd` (not `""`, not `"\x00"`) at or below the key: W0's
`KeyRange.inverted` (integration I5: was a local copy, `key ≠ [] ∧ keyLe rangeEnd key`, the same
range set). The model's `covers` holds of it vacuously (it has no key); the permission cache's
interval tree may refuse it (`Contains` of an empty interval), so a refusal says nothing about the
model there: W0's `State.invertedDeny`. Kept as a name for 3a's `opErr`. -/
abbrev rngInverted (r : KeyRange) : Prop := r.inverted

/-- **Every permission's range is one `RoleGrantPermission` accepts** (`isValidPermissionRange`): a
non-empty key, and a single key, a proper range, or open-ended. -/
def validPerms (a : AuthState) : Prop :=
  ∀ r ps, a.roles r = some ps → ∀ p ∈ ps, p.range.validPerm

/-- **Every user's and role's record of `a`, encoded, fits bbolt's limits** (its name at most
`MaxKeySize`, `32768` bytes; its `authpb` encoding at most `MaxValueSize`): a write past them is
fatal on every member
(`issues/etcd-auth-useradd-long-name-fatal.md`, `nonissues/etcd-auth-record-too-large-fatal.md`),
and its revision fits the `uint64` atomic (`a.rev < 2 ^ 64`: the cluster's step budget, W0).
A scope restriction of the admin steps (the request was committed; the apply cannot refuse it).
Intended realization (integration I5): for each record, every `authpb` encoding `bs` of it
(`Proto.encodes authpb.User.ty c bs`, `c` the record's content) has `Schema.putFits name bs` (4b's
`authBatchTx.UnsafePutUser`/`UnsafePutRole` premise), and `a.rev < 2 ^ 64`. Opaque until 3h gives the
`authpb` record contents (`req/go_etcd_io_etcd_api_v3_etcdserverpb.md`, "from 3d"). -/
opaque recordsFit (a : AuthState) : Prop

/-- **The effect of the admin request `rq` on the auth state**: W0's `authStep` at a caller who may
make it (the store does not check who calls: its applier does, before, `apply/auth.go`). Vacuous at
a state where nobody may (none is reachable: `AuthEnable` needs `root` with the root role, which
nothing removes while auth is on). -/
def admStep (rq : Req) (a a' : AuthState) (res : Resp) : Prop :=
  ∀ (who : Principal) (σ : State), σ.auth = a → a.mayCall who rq →
    ∃ σ' : State, authStep who rq σ σ' res ∧ σ'.auth = a'

open Classical in
/-- **The store's next state for the admin request `rq` at `a`**, as the code computes it (a
function: the one next state the cluster's history fixed at the commit, which the apply thread can
name; review round 1, F2). `cred` is the request's stored credential (the hash the proposer put in
`HashedPassword`, decoded: `authReqAt`'s); unused by the other requests. Lists as W0 keeps them
(appended; the store keeps them sorted, the same up to order). Agrees with `admStep` (a law the
proof gives: `storeNext_adm`). -/
def storeNext (rq : Req) (cred : Bytes) (a : AuthState) : AuthState :=
  let bump (a' : AuthState) : AuthState := { a' with rev := a.rev + 1 }
  match rq with
  | .authEnable =>
      if a.enabled = false ∧ a.isRoot rootUser then { a with enabled := true } else a
  | .authDisable => if a.enabled = true then bump { a with enabled := false } else a
  | .userAdd name _ noPw =>
      if name ≠ [] ∧ a.users name = none then
        bump (a.setUser name (some ⟨if noPw then none else some cred, []⟩))
      else a
  | .userDelete name =>
      if ¬ (a.enabled = true ∧ name = rootUser) ∧ a.users name ≠ none then bump (a.setUser name none)
      else a
  | .userChangePassword name _ =>
      match a.users name with
      | some ur => bump (a.setUser name (some { ur with password := ur.password.map (fun _ => cred) }))
      | none => a
  | .userGrantRole user role =>
      match a.users user with
      | some ur =>
          if (role = rootRole ∨ a.roles role ≠ none) ∧ role ∉ ur.roles then
            bump (a.setUser user (some { ur with roles := ur.roles ++ [role] }))
          else a
      | none => a
  | .userRevokeRole user role =>
      if a.enabled = true ∧ user = rootUser ∧ role = rootRole then a
      else match a.users user with
        | some ur =>
            if role ∈ ur.roles then
              bump (a.setUser user (some { ur with roles := ur.roles.filter (· ≠ role) }))
            else a
        | none => a
  | .roleAdd name =>
      if name ≠ [] ∧ a.roles name = none then bump (a.setRole name (some [])) else a
  | .roleDelete name =>
      if ¬ (a.enabled = true ∧ name = rootRole) ∧ a.roles name ≠ none then
        bump (AuthState.dropRole (a.setRole name none) name)
      else a
  | .roleGrantPermission name perm =>
      match a.roles name with
      | some ps =>
          if perm.range.validPerm then
            bump (a.setRole name (some (Perm.dropRange ps perm.range.key perm.range.rangeEnd ++ [perm])))
          else a
      | none => a
  | .roleRevokePermission role key rangeEnd =>
      match a.roles role with
      | some ps =>
          if ∃ q ∈ ps, q.range.key = key ∧ q.range.rangeEnd = rangeEnd then
            bump (a.setRole role (some (Perm.dropRange ps key rangeEnd)))
          else a
      | none => a
  | _ => a

/-- **The store's step is one of W0's** (an obligation of the store's proof): from a state where the
request's credential is a hash of its password, some answer `res` makes `storeNext` an `admStep`;
`storeNext_adm` is what `AdminTriple`'s post states per call. -/
def storeNext_adm.spec : Prop := ∀ (rq : Req) (cred : Bytes) (a : AuthState),
  (∀ name pw noPw, rq = .userAdd name pw noPw → noPw = false → pwHash pw cred) →
  (∀ name pw, rq = .userChangePassword name pw → pwHash pw cred) →
  ∃ res, admStep rq a (storeNext rq cred a) res

/-- **`a'` follows `a` by admin steps** (the store's history, and a snapshot's state: `Recover`). -/
inductive AuthReach : AuthState → AuthState → Prop
  | refl (a : AuthState) : AuthReach a a
  | step (a a₁ a' : AuthState) (rq : Req) (res : Resp) :
      admStep rq a a₁ res → AuthReach a₁ a' → AuthReach a a'

/-- **The cluster's reachability moves the auth state by admin steps** (second pass, A9's second
tier: `authStore.Recover`'s premise `AuthReach a a'` from 2d's `Reach σ σ'` between the store's
state and the snapshot's). A pure fact of W0's model: a request's `Step` changes `σ.auth` only by
`authStep` of a permitted admin request (whose effect on the auth state depends on it and the
request only: `admStep`), refusals, denials, errors, the other kinds' steps and the environment's
steps leave it. -/
def authReach_of_reach.spec : Prop := ∀ σ σ' : State, Reach σ σ' → AuthReach σ.auth σ'.auth

/-- **A permission check passed** (`isOpPermitted`) for the user `u` with the auth revision `rev`, on
an operation of type `t` over `rng`, its views at the states `af` (the flag), `ax` (the backend) and
`ac` (the cache): auth off at the flag, or a user given and the root role at the backend or the
range covered at the cache. Each disjunct is one state's `State.permits`. -/
def checkOk (u : GoString) (rev : w64) (t : PermType) (rng : KeyRange) (af ax ac : AuthState) :
    Prop :=
  af.enabled = false ∨ (af.enabled = true ∧ rev ≠ W64 0 ∧ (ax.isRoot u ∨ ac.covers u t rng))

/-- **A permission check refused** (`ErrPermissionDenied`): auth on at the flag, a user given, not of
the root role at the backend, and the range not covered at the cache (or inverted). -/
def checkDenied (u : GoString) (rev : w64) (t : PermType) (rng : KeyRange) (af ax ac : AuthState) :
    Prop :=
  af.enabled = true ∧ rev ≠ W64 0 ∧ ¬ ax.isRoot u ∧ (¬ ac.covers u t rng ∨ rngInverted rng)

/-! ## Pure: tokens and passwords -/

/-- `strings.TrimPrefix(s, "Bearer ")`. -/
def trimBearer (s : GoString) : GoString :=
  if s.take 7 = go!"Bearer " then s.drop 7 else s

/-- **The token `AuthInfoFromCtx` reads from the incoming metadata `md`** (grpc's `Grpc.MD`): the
first value of `token` (`rpctypes.TokenFieldNameGRPC`), else of `authorization`
(`TokenFieldNameSwagger`), with a `Bearer ` prefix removed; none if neither key is there. -/
def mdToken (md : Grpc.MD) : Option GoString :=
  match md.get go!"token" with
  | t :: _ => some (trimBearer t)
  | [] =>
    match md.get go!"authorization" with
    | t :: _ => some (trimBearer t)
    | [] => none

/-- **The token keys of `md` have values** (`AuthInfoFromCtx` indexes `ts[0]` of a present key:
`nonissues/etcd-auth-token-md-empty.md`): true of a gRPC run's metadata (`Grpc.rpcCtx_vals`) and of
`metadata.New`'s (`WithRoot`'s). -/
def tokKeysOk (md : Grpc.MD) : Prop :=
  ∀ e ∈ md, (e.1 = go!"token" ∨ e.1 = go!"authorization") → e.2 ≠ []

/-- The simple token of prefix `p` and index `idx`: `fmt.Sprintf("%s.%d", p, idx)` (opaque: the
decimal rendering; injective in `idx` for a prefix without `.`). -/
opaque simpleTok (p : GoString) (idx : Nat) : GoString

/-- (provisional, the `encoding/base64` boundary's) `base64.StdEncoding.EncodeToString(h)`: what
`EtcdServer.UserAdd`/`UserChangePassword` put in `HashedPassword` (2c), and what `selectPassword`
decodes (`DecodeString (b64 h) = h`). -/
opaque b64 (h : List w8) : GoString

/-! ## Resources -/

/-- Ghost names of one auth store: opaque. -/
opaque AuthNames : Type := Unit

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`st` is a member's auth store over the cluster `γ`** (persistent; the header). -/
opaque authStoreAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (st : Loc) (γ : Cluster) (γa : AuthNames) : IProp GF := iprop(True)

/-- **The writer: the store's current state is its `i`-th, `a`** (exclusive). -/
opaque authCur [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γa : AuthNames) (i : Nat) (a : AuthState) : IProp GF := iprop(True)

/-- **The store's `i`-th state is `a`** (persistent). -/
opaque authAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γa : AuthNames) (i : Nat) (a : AuthState) : IProp GF := iprop(True)

/-- **Every view of the store is at its `i`-th state or later, from now on** (persistent). -/
opaque authLb [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γa : AuthNames) (i : Nat) : IProp GF := iprop(True)

/-- **The store's provider has assigned no token of an `Authenticate` index above `n`**
(exclusive; the simple provider's once-only right, the header). -/
opaque tokFrom [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γa : AuthNames) (n : Nat) : IProp GF := iprop(True)

/-- **The store's provider issues root tokens without a collision** (persistent: the no-op and JWT
providers; not the simple one). -/
opaque rootTokOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γa : AuthNames) : IProp GF := iprop(True)

/-- **`ctx.Value(key)` returns `v`** (persistent): `context`'s `Context.ctxValueIs` (second pass:
was a transparent WP of this package's; client-core's predicate is what `WithValue.spec` gives,
kept by children and other keys' `WithValue`s, and `Context.ctxValueIs_wp` is that WP). -/
abbrev ctxValIs (ctx key v : GoInterface) : IProp GF := Context.ctxValueIs ctx key v

/-- **`ctx` is an `Authenticate` context for `name` at the entry index `idx`** (transparent,
persistent; verify round, A9 3d F4: it was opaque with no introduction): `ctx` carries
`AuthenticateParamIndex{} = uint64(idx)` (`idx ≠ 0`) and `AuthenticateParamSimpleTokenPrefix{} = p`
(a string without `.`: the proposer's `GenTokenPrefix`, letters), and the cluster issued the simple
token `p.idx` to `name` (`tokenUser`: 2d's, the committed entry `idx` is an
`InternalAuthenticateRequest` for `name` with prefix `p`; 3a's `authnIdx`). The applier
(`apply/backend.go:158`: `context.WithValue` twice over `Background()`) proves it. The JWT and no-op
providers read neither value; the simple one reads both (`simple_token.go:219,222`). -/
def authnCtx (γ : Cluster) (ctx : GoInterface) (name : GoString) (idx : Nat) : IProp GF :=
  iprop(∃ p : GoString,
    ctxValIs ctx
      (interface.mkOk go_etcd_io.etcd.server.v3.auth.AuthenticateParamIndex.ty
        #(zero_val go_etcd_io.etcd.server.v3.auth.AuthenticateParamIndex))
      (interface.mkOk go.uint64 #(W64 idx)) ∗
    ctxValIs ctx
      (interface.mkOk go_etcd_io.etcd.server.v3.auth.AuthenticateParamSimpleTokenPrefix.ty
        #(zero_val go_etcd_io.etcd.server.v3.auth.AuthenticateParamSimpleTokenPrefix))
      (interface.mkOk go.string #p) ∗
    ⌜0 < idx ∧ idx < 2 ^ 64 ∧ (46#8) ∉ p⌝ ∗ tokenUser γ (simpleTok p idx) name)

/-- **`tp` is a token provider for the cluster `γ`** (exclusive: given to one store), able to issue
root tokens without a collision if `rt`, whose `info` may be called once `R` holds (the simple
provider's index waiter is the server's `applyWait.Wait`, usable only once the server started:
`R := srvStarted`; verify round, A9 3d F7). Its methods' contract (a bundle over the
`TokenProvider` interface, PRINCIPLES "an interface value gets a bundle"): `info(ctx, tok, rev)`
(with `□ R`) returns `(ai, true)` only for a token of a user `u` with `tokenUser γ tok u`, `ai`
naming `u`; `assign(ctx, name, rev)` from an `authnCtx` returns a token of `name` or an error;
`enable`, `disable`, `invalidateUser`, `genTokenPrefix` do not panic. Stated in Lean as
`Internal.lean`'s laws (`tokenProviderAt_open`, `tp_info`, `tp_assign`, `tp_assignRoot`,
`tp_enable`, ...), proved from the concrete providers' method specs (`simple_provider`,
`nop_provider`). -/
opaque tokenProviderAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (tp : GoInterface) (γ : Cluster) (R : IProp GF) (rt : Bool) : IProp GF := iprop(True)

/-- **The store's token checks may run once `R` holds** (persistent; `NewAuthStore`'s, from its
provider's `tokenProviderAt tp γ R rt`): `AuthInfoFromCtx` takes it with `□ R`. Verify round (A9
3d F7). -/
opaque authGate [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γa : AuthNames) (R : IProp GF) : IProp GF := iprop(True)

/-- **The store's backend is `be`** (exclusive, timeless: the writer's; `NewAuthStore`'s, moved by
`Recover`): which backend the writer's batch locks run the post-lock hook of (the admin methods
take it beside `authBeHook be`).
Verify round (A9 3d F4). -/
opaque authBeCur [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γa : AuthNames) (be : GoInterface) : IProp GF := iprop(True)

/-- **The auth backend `be`'s batch lock (`LockInsideApply`) runs its post-lock hook from `Pre` to
`Q`** (one use; verify round, A9 3d F4). Stated over the `AuthBackend` value the store is given, as
the lessor's `Lease.beHookRun` over its backend value; introduced by 4a (as its `LeaseBackend.lean`
does the lessor's: requested), from `be = schema.NewAuthBackend(lg, beIface b)`'s post and 4a's
`∀ q, Backend.hookRun γb q Pk f Pre Q` with `Backend.beHook γb DFrac.discard f`. -/
opaque authBeHook [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (be : GoInterface) (Pre Q : IProp GF) : IProp GF := iprop(True)

/-- **`be` is an auth backend whose buckets hold the auth
state `a`** (3d's own: 4b declined a slot, `req/go_etcd_io_etcd_server_v3_auth.md`, "from 4b";
intended realization: `be` is `NewAuthBackend`'s wrapper of a backend, with 4a's parts of the
`auth`, `authUsers`, `authRoles` buckets holding `a`'s flag and revision (`Schema.authEnabledOf`,
`authRevOf`) and its records (`recsWf`, `userName`/`roleName`), and the backend's read and batch
transactions' contracts (`Schema.retOk`, `rdSect`, `wrSect`, `txRd`, `txRange`, `txWr`)) (exclusive: the store's share of the backend; users' passwords `a`'s credentials, roles' and permissions' lists up to order, users' roles sorted), with the contracts of its
`BatchTx`, `ReadTx`, `GetUser`, ... . Introduced (verify round, A9 3d F4) by a law of 4a/4b over
`NewAuthBackend`'s post and the backend's parts of the three auth buckets holding `a` (requested, as
`LeaseBackend.lean`'s `leaseBeLeases_intro`; the realization above). -/
opaque authBackendAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (be : GoInterface) (a : AuthState) : IProp GF := iprop(True)

/-- **`ctx`'s incoming metadata is `o`** (persistent): grpc's `Grpc.ctxInMD`
(`metadata.FromIncomingContext`'s answer; `none` for a context with none, as `s.ctx` and the internal
requesters'). Verify round (A9 3d F5): it was an opaque of this package's with no introduction;
grpc's has the laws (`rpcCtx_inMD`, `ctxInMD_background`, `_child`, `_value`). -/
abbrev ctxInMD (ctx : GoInterface) (o : Option Grpc.MD) : IProp GF := Grpc.ctxInMD ctx o

/-- **The token `ctx` carries** (`mdToken` of its incoming metadata, whose token keys have values,
`tokKeysOk`: the caller's, a run's context by `Grpc.rpcCtx_vals`; verify round, it was in the
provisional `ctxInMD`'s meaning, which grpc's does not have). -/
def ctxToken (ctx : GoInterface) (o : Option GoString) : IProp GF :=
  iprop((∃ md, ctxInMD ctx (some md) ∗ ⌜o = mdToken md ∧ tokKeysOk md⌝) ∨
    (ctxInMD ctx none ∗ ⌜o = none⌝))

/-- **The TLS client identity `AuthInfoFromTLS` reads** (persistent): grpc's transparent
`Grpc.ctxCertUser`, the peer's common name when the incoming metadata is present and has no
`grpcgateway-accept` key, `none` otherwise. Verify round (A9 3d F5): was an opaque of this
package's. -/
abbrev ctxCertUser (ctx : GoInterface) (c : Option GoString) : IProp GF := Grpc.ctxCertUser ctx c

/-- **The TLS client identity of `ctx`'s peer, whatever its metadata** (persistent): grpc's
`Grpc.ctxPeerCN` (none for no peer: `Background()`-derived contexts, the server's `s.ctx`). What
`WithRoot`'s new context exposes. Verify round (A9 3d F5): was an opaque of this package's. -/
abbrev ctxPeerCN (ctx : GoInterface) (c : Option GoString) : IProp GF := Grpc.ctxPeerCN ctx c

/-- (provisional, 3h's) **The request message `r` asks `rq`, with the credential `cred`** (persistent: read-only;
`*pb.Auth<Kind>Request`). For `userAdd name pw noPw` and `userChangePassword name pw`: `Name = name`,
`Options.NoPassword = noPw` (nil options: `false`), and, with a password, `HashedPassword = b64
cred` (non-empty) with W0's `pwHash pw cred` (the server's form: the proposer hashed it). A pre-3.5
entry's plain `Password` with an empty `HashedPassword` (rehashed at the apply with a fresh salt, so
no one next state) is out of scope (a scope restriction: this server never proposes it). For
`roleGrantPermission name perm`: `Perm` non-nil, of `perm`'s type (one of the three), key and range
end (a nil or unknown-typed `Perm` from a client has no `Req`: `req/go_etcd_io_etcd_api_v3.md`, "from
3d, round 1"). `cred` is `[]` for the other requests. Intended realization: `∃ c, Proto.msgAt
(EtcdServerPb.reqType rq) r DFrac.discard c ∗ ⌜EtcdServerPb.reqHolds c rq⌝` with the
`HashedPassword` field's content `b64 cred`; 3h's `reqHolds` does not say which hash the field holds
(W0's `Req.userAdd` carries the password), so this stays opaque (integration I5). -/
opaque authReqAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) (rq : Req) (cred : Bytes) : IProp GF := iprop(True)

/-- (provisional, 3h's) **`p` is a fresh `*pb.<Kind>Response` for the answer `res` to `rq`** (owned;
its `Header` nil, which the applier sets): `UserGet`'s roles, `RoleGet`'s permissions, the lists, in
the store's order (a permutation of the model's). Intended realization: `∃ c, Proto.msgAt _ p
(DFrac.own 1) c ∗ ⌜EtcdServerPb.bodyHolds c b⌝` for `res = .ok b`, with the `Header` field nil. -/
opaque authRespAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (rq : Req) (res : Resp) (p : Loc) : IProp GF := iprop(True)

/-- (provisional, 3h's) **`p` is a fresh `*pb.AuthenticateResponse` carrying the token `tok`**
(owned; its `Header` nil). -/
opaque authnRespAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (tok : GoString) : IProp GF := iprop(True)

/-- **The `AuthInfo` at `ai` names `u` at the auth revision `rev`** (its two fields at fraction
`dq`: `DFrac.discard` for one nobody writes, as `AuthInfoFromCtx`'s; a share for the applier's own
`aa.authInfo`, which it rewrites per request). -/
def authInfoAt (ai : Loc) (dq : DFrac) (u : GoString) (rev : w64) : IProp GF :=
  iprop(ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
    ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev)

/-- **A recorded state is reached** (transparent shorthand). -/
def authReached (γ : Cluster) (a : AuthState) : IProp GF :=
  iprop(∃ σ : State, etcdLb γ σ ∗ ⌜σ.auth = a⌝)

/-- **`v` is the value of the package's error variable of `ae`** (persistent: read-only for good;
the sentinel encoding of the verify round, `init`). -/
def errIs (ae : AuthErr) (v : GoInterface) : IProp GF := iprop(globalAddr ae.global ↦□ v)

/-! ### Laws -/

def authStoreAt_persistent.spec : Prop := ∀ st γ γa, Persistent (authStoreAt (GF := GF) st γ γa)
def authAt_persistent.spec : Prop := ∀ γa i a, Persistent (authAt (GF := GF) γa i a)
def authLb_persistent.spec : Prop := ∀ γa i, Persistent (authLb (GF := GF) γa i)
def rootTokOk_persistent.spec : Prop := ∀ γa, Persistent (rootTokOk (GF := GF) γa)
def authnCtx_persistent.spec : Prop := ∀ γ ctx name idx, Persistent (authnCtx (GF := GF) γ ctx name idx)
def errIs_persistent.spec : Prop := ∀ ae v, Persistent (errIs (GF := GF) ae v)
def authGate_persistent.spec : Prop := ∀ γa R, Persistent (authGate (GF := GF) γa R)
def authBeCur_timeless.spec : Prop := ∀ γa be, Timeless (authBeCur (GF := GF) γa be)
def authBeCur_excl.spec : Prop := ∀ γa be be',
  authBeCur (GF := GF) γa be ∗ authBeCur γa be' ⊢ iprop(False)

/-- **Any holder of the store may read it from its first state** (every view is at state `0` or
later; verify round, A9's second tier: the watch server's and v3rpc's checks outside the read
slot have no other source of a lower bound). -/
def authStoreAt_lb.spec : Prop := ∀ st γ γa, authStoreAt (GF := GF) st γ γa ⊢ authLb γa 0
def authReqAt_persistent.spec : Prop := ∀ r rq c, Persistent (authReqAt (GF := GF) r rq c)

/-- A response is a real pointer (the applier sets its `Header`: the field law is 3h's). -/
def authRespAt_ne_null.spec : Prop := ∀ rq res p, authRespAt (GF := GF) rq res p ⊢ ⌜p ≠ null⌝
def authnRespAt_ne_null.spec : Prop := ∀ p tok, authnRespAt (GF := GF) p tok ⊢ ⌜p ≠ null⌝
def authCur_timeless.spec : Prop := ∀ γa i a, Timeless (authCur (GF := GF) γa i a)
def authAt_timeless.spec : Prop := ∀ γa i a, Timeless (authAt (GF := GF) γa i a)
def authLb_timeless.spec : Prop := ∀ γa i, Timeless (authLb (GF := GF) γa i)

def authCur_excl.spec : Prop := ∀ γa i i' a a',
  authCur (GF := GF) γa i a ∗ authCur γa i' a' ⊢ iprop(False)

def tokFrom_excl.spec : Prop := ∀ γa n n',
  tokFrom (GF := GF) γa n ∗ tokFrom γa n' ⊢ iprop(False)

/-- The writer's state is recorded, and every view is at it. -/
def authCur_at.spec : Prop := ∀ γa i a,
  authCur (GF := GF) γa i a ⊢ authCur γa i a ∗ authAt γa i a ∗ authLb γa i

/-- A store has one cluster and one set of ghost names (3a's integration request). -/
def authStoreAt_agree.spec : Prop := ∀ st γ γ' γa γa',
  authStoreAt (GF := GF) st γ γa ∗ authStoreAt st γ' γa' ⊢ ⌜γ = γ' ∧ γa = γa'⌝

def authAt_agree.spec : Prop := ∀ γa i a a',
  authAt (GF := GF) γa i a ∗ authAt γa i a' ⊢ ⌜a = a'⌝

/-- Nothing is recorded past the writer's state (between its calls). -/
def authAt_le.spec : Prop := ∀ γa i j a b,
  authAt (GF := GF) γa j b ∗ authCur γa i a ⊢ ⌜j ≤ i⌝

def authLb_le.spec : Prop := ∀ γa i j a,
  authLb (GF := GF) γa j ∗ authCur γa i a ⊢ ⌜j ≤ i⌝

def authLb_mono.spec : Prop := ∀ γa i j, j ≤ i → authLb (GF := GF) γa i ⊢ authLb γa j

/-- The history is a chain of admin steps. -/
def authAt_reach.spec : Prop := ∀ γa j j' a a', j ≤ j' →
  authAt (GF := GF) γa j a ∗ authAt γa j' a' ⊢ ⌜AuthReach a a'⌝

/-- **Every recorded state is one the cluster reached.** -/
def authAt_reached.spec : Prop := ∀ st γ γa j a,
  authStoreAt (GF := GF) st γ γa ∗ authAt γa j a ⊢ authReached γ a

/-- Every recorded state's permissions are valid ranges (the grants check them). -/
def authAt_valid.spec : Prop := ∀ γa j a, authAt (GF := GF) γa j a ⊢ ⌜validPerms a⌝

end res

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The package's error variables** (`store.go:46-68`, `errors.New` at init; verify round, the
sentinel encoding of A3 F4: they were the values of an opaque Lean function `errOf`, which no
realization can prove, `errors.New` allocating a fresh pointer): their values, given
existentially as a function `ev` of the error, read-only (`errIs`), each `errors.New` of its
message (Perennial's `errors.newVar`: a `*errors.errorString`, what `errors.Is` with it as the
target and `Error()` need), pairwise distinct and non-nil. A spec returning one of them returns the
value the global holds (`errIs ae err`); a caller's `errors.Is(err, auth.ErrX)` reads the global
and compares (2a, 2b, 2c). -/
def init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
    ∃ ev : AuthErr → GoInterface,
      (□ ∀ ae, errIs ae (ev ae) ∗ errors.newVar ae.global ae.msg) ∗
      ⌜(∀ ae ae', ev ae = ev ae' → ae = ae') ∧ ∀ ae, ev ae ≠ GoInterface.nil⌝

/-- **An admin method's return** for the answer `res` of `rq`: the fresh response and `nil`, or `nil`
and the package's error of the answer's `EtcdErr` (the global's value). -/
def admReply (rq : Req) (res : Resp) (resp : Loc) (err : GoInterface) : IProp GF :=
  match res with
  | .ok _ => iprop(⌜err = GoInterface.nil⌝ ∗ authRespAt rq res resp)
  | .err e => iprop(⌜resp = null⌝ ∗ ∃ ae, ⌜ae.etcd = some e⌝ ∗ errIs ae err)

/-! ## Shapes shared by the specs -/

/-- **The post-lock hook's outcome** of a writer call that may lock the batch transaction of the
backend `be` once: `Q` (it locked) or `Pre` back with the unused hook run of `be` (it did not: an
early refusal, or a method reading through the read transaction). The hook is the backend's
(`authBeHook be`), not the store's: re-review N1, a store-indexed hook given back unused would
survive `Recover` and name a backend the store no longer has. -/
def hookOut (be : GoInterface) (Pre Q : IProp GF) : IProp GF :=
  iprop(Q ∨ (Pre ∗ authBeHook be Pre Q))

/-- **An admin method** `e` of the store `st` for the request `rq` with the credential `cred` (its
message described by `P`): the writer supplies that the one next state, `storeNext rq cred a`, is
reached and fits bbolt (2d: the committed entry's next state; `recordsFit` is the scope
restriction of `issues/etcd-auth-useradd-long-name-fatal.md`), and the hook run of the store's
current backend `be` (`authBeCur γa be ∗ authBeHook be Pre Q`, from `Pre`: the batch transaction's
`LockInsideApply` runs it, integration I5; re-review N1: the store's backend named in the same
premise, given back); the store moves there (recorded as its `(i+1)`-th state) with an answer W0's
step allows there, and replies. -/
def AdminTriple (e : Expr) (P : IProp GF) (st : Loc) (rq : Req) (cred : Bytes) : Prop :=
  ∀ (γ : Cluster) (γa : AuthNames) (i : Nat) (a : AuthState) (be : GoInterface) (Pre Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ P ∗
      authStoreAt st γ γa ∗ authCur γa i a ∗ authReached γ (storeNext rq cred a) ∗
      ⌜recordsFit (storeNext rq cred a)⌝ ∗ authBeCur γa be ∗ Pre ∗ authBeHook be Pre Q }}
    e
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); P ∗ authBeCur γa be ∗
      hookOut be Pre Q ∗
      ∃ res : Resp, ⌜admStep rq a (storeNext rq cred a) res⌝ ∗
        authCur γa (i + 1) (storeNext rq cred a) ∗ admReply rq res resp err }}

/-- **What a permission check of `u` (revision `rev`) on `t` over `rng` returns**, from the lower
bound `i0`: its three views' recorded states (the flag at `jf`, the backend at `jx`, the cache at
`jc`, each at or after `i0`), and `nil` (`checkOk`; with auth on at the flag, the store's revision
read at `jr` is at most the request's: 3a's round-1 item 5), `ErrUserEmpty` (no user: revision `0`),
`ErrAuthOldRevision` (the request's revision below the store's, read at `jr`), or `ErrPermissionDenied` (`checkDenied`).
The revision is read before the backend and the cache, so `jx`, `jc` are not bounded by `jr`: a
reader's passing checks need not see one state (`nonissues/etcd-auth-revision-before-visible.md`);
the writer's do (`authCur_at`, `authAt_le`). -/
def checkPost (γa : AuthNames) (i0 : Nat) (u : GoString) (rev : w64) (t : PermType)
    (rng : KeyRange) (err : GoInterface) : IProp GF :=
  iprop(∃ (jf jx jc jr : Nat) (af ax ac ar : AuthState), ⌜i0 ≤ jf ∧ i0 ≤ jx ∧ i0 ≤ jc ∧ i0 ≤ jr⌝ ∗
    authAt γa jf af ∗ authAt γa jx ax ∗ authAt γa jc ac ∗ authAt γa jr ar ∗
    (⌜err = GoInterface.nil ∧ checkOk u rev t rng af ax ac ∧ (af.enabled = true → ar.rev ≤ uint.nat rev)⌝ ∨
     (errIs .userEmpty err ∗ ⌜af.enabled = true ∧ rev = W64 0⌝) ∨
     (errIs .authOldRevision err ∗ ⌜af.enabled = true ∧ rev ≠ W64 0 ∧ uint.nat rev < ar.rev⌝) ∨
     (errIs .permissionDenied err ∗ ⌜checkDenied u rev t rng af ax ac⌝)))

/-- **What `IsAdminPermitted` returns** for the user `u` (`""` for none), from the lower bound
`i0`: the flag at `jf` and the backend at `jx`; `nil` (auth off, or `u` of the root role),
`ErrUserEmpty`, `ErrUserNotFound`, `ErrPermissionDenied` (W0's `adminErr` at one state when
`jf = jx`). -/
def adminPost (γa : AuthNames) (i0 : Nat) (u : GoString) (err : GoInterface) : IProp GF :=
  iprop(∃ (jf jx : Nat) (af ax : AuthState), ⌜i0 ≤ jf ∧ i0 ≤ jx⌝ ∗
    authAt γa jf af ∗ authAt γa jx ax ∗
    (⌜err = GoInterface.nil ∧ (af.enabled = false ∨ (af.enabled = true ∧ ax.isRoot u))⌝ ∨
     (errIs .userEmpty err ∗ ⌜af.enabled = true ∧ u = []⌝) ∨
     (errIs .userNotFound err ∗ ⌜af.enabled = true ∧ u ≠ [] ∧ ax.users u = none⌝) ∨
     (errIs .permissionDenied err ∗ ⌜af.enabled = true ∧ u ≠ [] ∧ ax.users u ≠ none ∧
        ¬ ax.isRoot u⌝)))

/-- **A channel any goroutine may receive on** (only ever closed). -/
def recvOk (ch : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, isChan ch γc Unit ∗
    □ ∀ Φ : Unit → Bool → IProp GF, (∀ v ok, Φ v ok) -∗ recvAu γc Unit Φ)

/-- **The simple provider's index waiter** (`func(uint64) <-chan struct{}`: the server's
`applyWait.Wait`), gated on `R`: once `R` holds, callable from any goroutine, it returns a channel
any goroutine may receive on. Verify round (A9 3d F7): it was callable from the call of
`NewTokenProvider` on, false of the server's closure (`srv.applyWait` is set in `start()`,
`server.go:568`; before, the call is a method call on a nil interface); the gate is the
checkpointer's (`Lease.ckptOk`): `R := srvStarted`, which every request-path spec holds. -/
def waiterOk (iw : GoFunc) (R : IProp GF) : IProp GF :=
  iprop(□ ∀ (i : w64) (Φ : val → IProp GF), R -∗ (∀ ch : Loc, recvOk ch -∗ Φ #ch) -∗
    WP (App (Val #iw) (Val #i)) {{ Φ }})

/-- (provisional, the JWT boundary's and 2d's) **The cluster `γ`'s tokens include the JWTs that
`opts`' keys verify, each naming the user of its claims** (`tokenUser γ tok u` for such a token):
what makes the JWT provider's `info` meet `tokenProviderAt`. Every member is configured with the
same keys (`--auth-token`), and 2d realizes W0's `tokenUser` accordingly. -/
opaque jwtTokOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (opts : GoString) : IProp GF := iprop(True)

end init

/-- The token provider's kind in an `--auth-token` option string: what precedes the first comma. -/
def optsKind (opts : GoString) : GoString := opts.takeWhile (fun b => decide (b ≠ 44#8))

/-- The state `NewAuthStore` starts from: a backend's state, with revision `1` for a fresh
backend's `0` (`commitRevision`). -/
def normRev (a : AuthState) : AuthState := if a.rev = 0 then { a with rev := 1 } else a

end Auth
end EtcdGrove
end Perennial
