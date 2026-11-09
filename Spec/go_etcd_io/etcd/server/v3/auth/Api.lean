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
`rngInverted` (W0's `KeyRange.inverted`), `validPerms` (W0's `KeyRange.validPerm` of every
permission), `recordsFit` (opaque: bbolt's limits, 4b's `Schema.putFits` of 3h's `authpb` encoding), `admStep rq a a' res` (W0's `authStep` effect of an admin request at an authorized
caller), `storeNext rq cred a` (the store's next state, a function), `AuthReach`,
`checkOk`/`checkDenied`, `mdToken`, `trimBearer`, `b64` (opaque, provisional: `encoding/base64`'s
boundary).

Resources: `AuthNames` (opaque ghost names); `authStoreAt st γ γa` (persistent: `st` is a member's
store over cluster `γ`); `authCur γa i a` (exclusive: the writer); `authAt γa i a`, `authLb γa i`
(persistent); `tokFrom γa n` (exclusive), `rootTokOk γa`, `authnCtx γa ctx name idx` (persistent);
`tokenProviderAt tp γ rt` (exclusive: a provider not yet given to a store; `rt`: it can issue root
tokens without a collision); `authBackendAt be a` (exclusive, provisional: 4b's `AuthBackend`
holding `a`; 3d's own, over 4b's schema specs); `authHook γa Pre Q` (provisional, 4a/2d: the
backend's post-lock hook, one use; `hookOut`); `authReqAt r rq cred`, `authRespAt rq res p`,
`authnRespAt p tok` (provisional: 3h's messages), `authInfoAt ai dq u rev` (the `AuthInfo`);
`ctxInMD ctx o`, `ctxCertUser ctx c`, `ctxPeerCN ctx c` (provisional: 2a's grpc boundary;
`ctxToken` transparent over them); `errOf e` (the error variables' values, 2c's `srvErrVal` for the
mapped ones). From W0: `pwHash`/`pwMatch`, `tokenUser` (`tokenUser_agree`), `authStep` (its `lo`
only matters for `authenticate`, which no admin method takes), `State.invertedDeny`,
`State.permittedSince`, `etcdLb_noEmptyUser`.

## Intended realization

* `AuthNames`: the history's `mono_list` (`γa.hist`), the cluster `γ`, the token map's ghost
  (`γa.tok`: each assigned simple token's user and index), the provider's kind.
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
  to lock the batch transaction (4b), `bcryptCost`.
* `tokFrom γa n`: the simple provider's map holds no token of an index above `n` (the half of the
  index bound; the other half in the map's lock invariant). JWT and no-op: `True`.
* `authnCtx γa ctx name idx`: `ctx` carries `AuthenticateParamIndex{} = idx` (a `uint64`, `idx ≠ 0`)
  and `AuthenticateParamSimpleTokenPrefix{} = p` (a `string` without `.`: the proposer's
  `GenTokenPrefix`, letters or empty, so `p.idx` determines `idx`), and `tokenUser γ (p ++ "." ++
  decimal idx) name` (2d: the committed entry `idx` is an `InternalAuthenticateRequest` for `name`
  with prefix `p`); for JWT, `True` (its tokens' `tokenUser` is their signature, the provider's
  premise). Introduced by the applier that builds the context (3a, `apply/backend.go`'s
  `Authenticate`: `context.WithValue` twice), from 2d's entry.

## Laws

`authStoreAt_persistent`, `authAt_persistent`, `authLb_persistent`, `authCur_timeless`,
`authAt_timeless`, `authLb_timeless`, `rootTokOk_persistent`, `authnCtx_persistent`,
`ctxInMD_persistent`, `ctxCertUser_persistent`, `authReqAt_persistent`; `authCur_excl`,
`authCur_at`, `authAt_agree`, `authAt_le`, `authLb_le`, `authLb_mono`, `authAt_reach`,
`authAt_reached`, `authAt_valid`, `tokFrom_excl`, `authStoreAt_agree`; `errOf_ne_nil`, `errOf_inj`, `errOf_srvErrVal`, `init`;
`storeNext_adm`, `authRespAt_ne_null`, `authnRespAt_ne_null`.

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
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.errors.Api
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

/-- Incoming metadata (grpc's `Grpc.MD`, the same shape: lowercase keys, their values). -/
abbrev MD := List (GoString × List GoString)

/-- The values of key `k` (grpc's `Grpc.MD.get`, the same shape: lowercase keys). -/
def mdGet (md : MD) (k : GoString) : List GoString :=
  (md.filter (fun e => decide (e.1 = k))).flatMap (·.2)

/-- **The token `AuthInfoFromCtx` reads from the incoming metadata `md`**: the first value of
`token` (`rpctypes.TokenFieldNameGRPC`), else of `authorization` (`TokenFieldNameSwagger`), with a
`Bearer ` prefix removed; none if neither key is there. -/
def mdToken (md : MD) : Option GoString :=
  match mdGet md go!"token" with
  | t :: _ => some (trimBearer t)
  | [] =>
    match mdGet md go!"authorization" with
    | t :: _ => some (trimBearer t)
    | [] => none

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

/-- **`ctx` is an `Authenticate` context for `name` at the entry index `idx`** (persistent; the
header's realization). -/
opaque authnCtx [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γa : AuthNames) (ctx : GoInterface) (name : GoString) (idx : Nat) : IProp GF :=
  iprop(True)

/-- **`tp` is a token provider for the cluster `γ`** (exclusive: given to one store), able to issue
root tokens without a collision if `rt`. Its methods' contract (a bundle over the `TokenProvider`
interface, PRINCIPLES "an interface value gets a bundle"): `info(ctx, tok, rev)` returns `(ai,
true)` only for a token of a user `u` with `tokenUser γ tok u`, `ai` naming `u`; `assign(ctx, name,
rev)` from an `authnCtx` returns a token of `name` or an error; `enable`, `disable`,
`invalidateUser`, `genTokenPrefix` do not panic. Stated in Lean as `Internal.lean`'s laws
(`tokenProviderAt_open`, `tp_info`, `tp_assign`, `tp_assignRoot`, `tp_enable`, ...), proved from the
concrete providers' method specs (`simple_provider`, `nop_provider`). -/
opaque tokenProviderAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (tp : GoInterface) (γ : Cluster) (rt : Bool) : IProp GF := iprop(True)

/-- **`be` is an auth backend whose buckets hold the auth
state `a`** (3d's own: 4b declined a slot, `req/go_etcd_io_etcd_server_v3_auth.md`, "from 4b";
intended realization: `be` is `NewAuthBackend`'s wrapper of a backend, with 4a's parts of the
`auth`, `authUsers`, `authRoles` buckets holding `a`'s flag and revision (`Schema.authEnabledOf`,
`authRevOf`) and its records (`recsWf`, `userName`/`roleName`), and the backend's read and batch
transactions' contracts (`Schema.retOk`, `rdSect`, `wrSect`, `txRd`, `txRange`, `txWr`)) (exclusive: the store's share of the backend; users' passwords `a`'s credentials, roles' and permissions' lists up to order, users' roles sorted), with the contracts of its
`BatchTx`, `ReadTx`, `GetUser`, ... . -/
opaque authBackendAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (be : GoInterface) (a : AuthState) : IProp GF := iprop(True)

/-- (provisional, 2a's grpc boundary) **`ctx`'s incoming metadata is `o`** (persistent;
`metadata.FromIncomingContext`'s answer: `none` for a context with none, as `s.ctx` and the internal
requesters'; every key with at least one value, as grpc's transports and `metadata.New` make them,
`nonissues/etcd-auth-token-md-empty.md`). 2a's `Grpc.rpcCtx ctx md` should give `some md` (with
`Grpc.rpcCtx_vals`: non-empty values); 2a's `FromIncomingContext.spec` covers only a run's context,
and there is no law yet (integration I5: still requested, `req/google_golang_org_grpc.md`, "from
3d"). -/
opaque ctxInMD [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ctx : GoInterface) (o : Option MD) : IProp GF := iprop(True)

/-- **The token `ctx` carries** (`mdToken` of its incoming metadata). -/
def ctxToken (ctx : GoInterface) (o : Option GoString) : IProp GF :=
  iprop((∃ md, ctxInMD ctx (some md) ∗ ⌜o = mdToken md⌝) ∨ (ctxInMD ctx none ∗ ⌜o = none⌝))

/-- (provisional, 2a's grpc `peer`/`credentials` boundary) **The TLS client identity of `ctx`**
(persistent): `some cn`, the common name of the first verified chain's leaf of a TLS peer, for a
request whose incoming metadata is present (`metadata.FromIncomingContext` succeeds) and has no
`grpcgateway-accept` key; `none` otherwise (no peer, not TLS, no verified chain, no incoming
metadata, a gateway request). What `AuthInfoFromTLS` reads. -/
opaque ctxCertUser [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ctx : GoInterface) (c : Option GoString) : IProp GF := iprop(True)

/-- (provisional, 2a's grpc `peer`/`credentials` boundary) **The TLS client identity of `ctx`'s
peer, whatever its metadata** (persistent): `some cn` for a TLS peer with a non-empty verified chain
whose leaf's common name is `cn`, `none` otherwise (no peer: `Background()`-derived contexts, the
server's `s.ctx`). `ctxCertUser` is it when the incoming metadata is present and has no
`grpcgateway-accept` key. What `WithRoot`'s new context exposes (integration I5: `WithRoot.spec`
claimed `ctxCertUser ctx none → ctxCertUser ctx' none`, false for a TLS peer without incoming
metadata, which `NewIncomingContext` adds). -/
opaque ctxPeerCN [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ctx : GoInterface) (c : Option GoString) : IProp GF := iprop(True)

/-- (provisional, 4a's and 2d's) **The store's backend's post-lock hook takes `Pre` to `Q`** (one
use): the auth store's batch transaction locks with `LockInsideApply` (4b's `authBatchTx.Lock`:
`callOk tx "LockInsideApply" P Q`), which runs the backend's post-lock hook (the server's
`getTxPostLockInsideApplyHook`, set after `NewAuthStore`, `server.go:409`, and on a snapshot's
backend before `Recover`, `server.go:1098`). Intended realization: for the backend the store holds
(its invariant records 4a's names of it, the hook `f` and the batch lock's invariant `Pk`), 4a's
`∀ q, Backend.hookRun γb q Pk f Pre Q` (as the lessor's `Lease.beHookRun`; integration Y: mvcc's
`Mvcc.hookRun` now names mvcc's storage). The writer (3a, from 2d's apply loop) supplies it per call,
from the server's hook proved once over 4a's contract at every share; its introduction needs the
store's backend's names, `authBackendAt`'s realization (3d's, recorded). -/
opaque authHook [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γa : AuthNames) (Pre Q : IProp GF) : IProp GF := iprop(True)

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

/-! ### Laws -/

def authStoreAt_persistent.spec : Prop := ∀ st γ γa, Persistent (authStoreAt (GF := GF) st γ γa)
def authAt_persistent.spec : Prop := ∀ γa i a, Persistent (authAt (GF := GF) γa i a)
def authLb_persistent.spec : Prop := ∀ γa i, Persistent (authLb (GF := GF) γa i)
def rootTokOk_persistent.spec : Prop := ∀ γa, Persistent (rootTokOk (GF := GF) γa)
def authnCtx_persistent.spec : Prop := ∀ γa ctx name idx, Persistent (authnCtx (GF := GF) γa ctx name idx)
def ctxInMD_persistent.spec : Prop := ∀ ctx o, Persistent (ctxInMD (GF := GF) ctx o)
def ctxCertUser_persistent.spec : Prop := ∀ ctx c, Persistent (ctxCertUser (GF := GF) ctx c)
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

section errs
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- **The value of the package's error variable `e`** (`auth.ErrPermissionDenied`, ...). -/
opaque errOf (e : AuthErr) : GoInterface := GoInterface.nil

def errOf_ne_nil.spec : Prop := ∀ e, errOf e ≠ GoInterface.nil

def errOf_inj.spec : Prop := ∀ e e', errOf e = errOf e' → e = e'

/-- **The error variables `togRPCError` maps are the server's sentinels** (2c's `srvErrVal`, its
round-1 item 3, `req/go_etcd_io_etcd_server_v3_auth.md`): with 2c's `srvErrOf_val`, `srvErrVal_leaf`,
an auth error the store returns is a mapped leaf. -/
def errOf_srvErrVal.spec : Prop := ∀ ae e, ae.etcd = some e → errOf ae = EtcdServer.srvErrVal e

end errs

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

open go_etcd_io.etcd.server.v3.auth in
/-- **The package's error variables hold `errOf`'s values** (read-only; `errors.New` at init), for
the callers' `errors.Is(err, auth.ErrX)` (2a, 2b, 2c). -/
def init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
    globalAddr ErrRootUserNotExist ↦□ errOf .rootUserNotExist ∗
    globalAddr ErrRootRoleNotExist ↦□ errOf .rootRoleNotExist ∗
    globalAddr ErrUserAlreadyExist ↦□ errOf .userAlreadyExist ∗
    globalAddr ErrUserEmpty ↦□ errOf .userEmpty ∗
    globalAddr ErrUserNotFound ↦□ errOf .userNotFound ∗
    globalAddr ErrRoleAlreadyExist ↦□ errOf .roleAlreadyExist ∗
    globalAddr ErrRoleNotFound ↦□ errOf .roleNotFound ∗
    globalAddr ErrRoleEmpty ↦□ errOf .roleEmpty ∗
    globalAddr ErrPermissionNotGiven ↦□ errOf .permissionNotGiven ∗
    globalAddr ErrAuthFailed ↦□ errOf .authFailed ∗
    globalAddr ErrNoPasswordUser ↦□ errOf .noPasswordUser ∗
    globalAddr ErrPermissionDenied ↦□ errOf .permissionDenied ∗
    globalAddr ErrRoleNotGranted ↦□ errOf .roleNotGranted ∗
    globalAddr ErrPermissionNotGranted ↦□ errOf .permissionNotGranted ∗
    globalAddr ErrAuthNotEnabled ↦□ errOf .authNotEnabled ∗
    globalAddr ErrAuthOldRevision ↦□ errOf .authOldRevision ∗
    globalAddr ErrInvalidAuthToken ↦□ errOf .invalidAuthToken ∗
    globalAddr ErrInvalidAuthOpts ↦□ errOf .invalidAuthOpts ∗
    globalAddr ErrInvalidAuthMgmt ↦□ errOf .invalidAuthMgmt

/-- **An admin method's return** for the answer `res` of `rq`: the fresh response and `nil`, or `nil`
and the package's error of the answer's `EtcdErr`. -/
def admReply (rq : Req) (res : Resp) (resp : Loc) (err : GoInterface) : IProp GF :=
  match res with
  | .ok _ => iprop(⌜err = GoInterface.nil⌝ ∗ authRespAt rq res resp)
  | .err e => iprop(⌜resp = null ∧ ∃ ae, ae.etcd = some e ∧ err = errOf ae⌝)

/-! ## Shapes shared by the specs -/

/-- **The post-lock hook's outcome** of a writer call that may lock the batch transaction once:
`Q` (it locked) or `Pre` back with the unused hook (it did not: an early refusal, or a method
reading through the read transaction). -/
def hookOut (γa : AuthNames) (Pre Q : IProp GF) : IProp GF :=
  iprop(Q ∨ (Pre ∗ authHook γa Pre Q))

/-- **An admin method** `e` of the store `st` for the request `rq` with the credential `cred` (its
message described by `P`): the writer supplies that the one next state, `storeNext rq cred a`, is
reached and fits bbolt (2d: the committed entry's next state; `recordsFit` is the scope
restriction of `issues/etcd-auth-useradd-long-name-fatal.md`), and the backend's post-lock hook
(`authHook`, from `Pre`: the batch transaction's `LockInsideApply` runs it, integration I5); the
store moves there (recorded as its `(i+1)`-th state) with an answer W0's step allows there, and
replies. -/
def AdminTriple (e : Expr) (P : IProp GF) (st : Loc) (rq : Req) (cred : Bytes) : Prop :=
  ∀ (γ : Cluster) (γa : AuthNames) (i : Nat) (a : AuthState) (Pre Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ P ∗
      authStoreAt st γ γa ∗ authCur γa i a ∗ authReached γ (storeNext rq cred a) ∗
      ⌜recordsFit (storeNext rq cred a)⌝ ∗ Pre ∗ authHook γa Pre Q }}
    e
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); P ∗ hookOut γa Pre Q ∗
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
    ⌜(err = GoInterface.nil ∧ checkOk u rev t rng af ax ac ∧ (af.enabled = true → ar.rev ≤ uint.nat rev)) ∨
     (err = errOf .userEmpty ∧ af.enabled = true ∧ rev = W64 0) ∨
     (err = errOf .authOldRevision ∧ af.enabled = true ∧ rev ≠ W64 0 ∧ uint.nat rev < ar.rev) ∨
     (err = errOf .permissionDenied ∧ checkDenied u rev t rng af ax ac)⌝)

/-- **What `IsAdminPermitted` returns** for the user `u` (`""` for none), from the lower bound
`i0`: the flag at `jf` and the backend at `jx`; `nil` (auth off, or `u` of the root role),
`ErrUserEmpty`, `ErrUserNotFound`, `ErrPermissionDenied` (W0's `adminErr` at one state when
`jf = jx`). -/
def adminPost (γa : AuthNames) (i0 : Nat) (u : GoString) (err : GoInterface) : IProp GF :=
  iprop(∃ (jf jx : Nat) (af ax : AuthState), ⌜i0 ≤ jf ∧ i0 ≤ jx⌝ ∗
    authAt γa jf af ∗ authAt γa jx ax ∗
    ⌜(err = GoInterface.nil ∧ (af.enabled = false ∨ (af.enabled = true ∧ ax.isRoot u))) ∨
     (err = errOf .userEmpty ∧ af.enabled = true ∧ u = []) ∨
     (err = errOf .userNotFound ∧ af.enabled = true ∧ u ≠ [] ∧ ax.users u = none) ∨
     (err = errOf .permissionDenied ∧ af.enabled = true ∧ u ≠ [] ∧ ax.users u ≠ none ∧
        ¬ ax.isRoot u)⌝)

/-- **A channel any goroutine may receive on** (only ever closed). -/
def recvOk (ch : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, isChan ch γc Unit ∗
    □ ∀ Φ : Unit → Bool → IProp GF, (∀ v ok, Φ v ok) -∗ recvAu γc Unit Φ)

/-- **The simple provider's index waiter** (`func(uint64) <-chan struct{}`: the server's
`applyWait.Wait`): callable from any goroutine, it returns a channel any goroutine may receive on. -/
def waiterOk (iw : GoFunc) : IProp GF :=
  iprop(□ ∀ (i : w64) (Φ : val → IProp GF), (∀ ch : Loc, recvOk ch -∗ Φ #ch) -∗
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
