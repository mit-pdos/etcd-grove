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
state is the read's state".

**Tokens** name users as the cluster issued them: W0's `tokenUser γ tok u`. A token the store
accepts (`AuthInfoFromCtx`) maps to a user `u` with `tokenUser γ tok u`; a token it assigns
(`Authenticate`, `WithRoot`) is one. The simple provider's tokens are `prefix.index` with `index` the
`Authenticate` entry's log index: assigning one twice panics (`assignSimpleTokenToUser`), so its
right is the once-only `tokFrom γa n` (no index above `n` assigned yet), and `WithRoot`'s index `0`
token needs `rootTokOk γa` (`nonissues/etcd-auth-withroot-token-collision-panic.md`: two random
prefixes may collide; the simple provider does not give it).

**Passwords**: the model keeps a user's password; the store keeps a bcrypt hash of it
(`Bcrypt.hashOf`), which the proposer computed and base64-encoded into the request
(`hashedPw hp pw`). `CheckPassword` passes for the user's password and may pass for others (bcrypt's
72-byte limit and collisions: the boundary assumes no rejection).

**Mode.** Auth on and off are values of `a.enabled`, not two specs (`auth-component.md`).

## Vocabulary

Pure: `AuthErr` (the package's error variables) with `AuthErr.etcd` (`togRPCError`'s table),
`rngInverted`, `validPerms`, `recordsFit` (opaque, provisional: 4a's
bbolt limits), `admStep rq a a' res` (W0's `authStep` effect of an admin request at an authorized
caller), `AuthReach`, `checkOk`/`checkDenied`, `mdToken`, `trimBearer`, `hashedPw` (opaque),
`b64` (opaque, provisional: `encoding/base64`'s boundary).

Resources: `AuthNames` (opaque ghost names); `authStoreAt st γ γa` (persistent: `st` is a member's
store over cluster `γ`); `authCur γa i a` (exclusive: the writer); `authAt γa i a`, `authLb γa i`
(persistent); `tokFrom γa n` (exclusive), `rootTokOk γa`, `authnCtx γa ctx name idx` (persistent);
`tokenProviderAt tp γ rt` (exclusive: a provider not yet given to a store; `rt`: it can issue root
tokens without a collision); `authBackendAt be a` (exclusive, provisional: 4b's `AuthBackend`
holding `a`); `authReqAt r rq`, `authRespAt rq res p`, `authnRespAt p tok`, `authInfoAt ai dq u rev` (messages and the
`AuthInfo`); `ctxInMD ctx o`, `ctxCertUser ctx c` (provisional: 2a's grpc boundary; `ctxToken`
transparent over them); `errOf e` (the error variables' values).

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
`authAt_reached`, `authAt_valid`, `tokFrom_excl`; `errOf_ne_nil`, `errOf_inj`, `init`;
`hashedPw_intro`.

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

/-- **An inverted range**: a proper `rangeEnd` (not `""`, not `"\x00"`) at or below a non-empty key.
The model's `covers` holds of it vacuously (it has no key); the permission cache's interval tree
may refuse it (`Contains` of an empty interval), so a refusal says nothing about the model there. -/
def rngInverted (r : KeyRange) : Prop :=
  r.rangeEnd ≠ [] ∧ r.rangeEnd ≠ [0#8] ∧ r.key ≠ [] ∧ keyLe r.rangeEnd r.key

/-- **Every permission's range is one `RoleGrantPermission` accepts** (`isValidPermissionRange`): a
non-empty key, and a single key, a proper range, or open-ended. -/
def validPerms (a : AuthState) : Prop :=
  ∀ r ps, a.roles r = some ps → ∀ p ∈ ps,
    p.range.key ≠ [] ∧ (p.range.rangeEnd = [] ∨ p.range.rangeEnd = [0#8] ∨ keyLt p.range.key p.range.rangeEnd)

/-- (provisional, 4a's and 3h's) **Every user's and role's record of `a`, encoded, fits bbolt's
limits** (its name at most `MaxKeySize`, `32768` bytes; its `authpb` encoding at most
`MaxValueSize`): a write past them is fatal on every member
(`issues/etcd-auth-useradd-long-name-fatal.md`, `nonissues/etcd-auth-record-too-large-fatal.md`),
and its revision fits the `uint64` atomic (`a.rev < 2 ^ 64`: the cluster's step budget, W0).
A scope restriction of the admin steps (the request was committed; the apply cannot refuse it). -/
opaque recordsFit (a : AuthState) : Prop

/-- **The effect of the admin request `rq` on the auth state**: W0's `authStep` at a caller who may
make it (the store does not check who calls: its applier does, before, `apply/auth.go`). Vacuous at
a state where nobody may (none is reachable: `AuthEnable` needs `root` with the root role, which
nothing removes while auth is on). -/
def admStep (rq : Req) (a a' : AuthState) (res : Resp) : Prop :=
  ∀ (who : Principal) (σ : State), σ.auth = a → a.mayCall who rq →
    authStep who rq σ { σ with auth := a' } res

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

/-- (provisional, the `encoding/base64` boundary's) `base64.StdEncoding.EncodeToString(h)`. -/
opaque b64 (h : List w8) : GoString

/-- **`hp` carries a bcrypt hash of the password `pw`**: `b64 h` for some `h` with
`Bcrypt.hashOf h pw` (what `EtcdServer.UserAdd`/`UserChangePassword` put in `HashedPassword`). -/
opaque hashedPw (hp : GoString) (pw : Bytes) : Prop

/-- Introduction (2c's proposals): the base64 of a bcrypt hash of `pw`. -/
def hashedPw_intro.spec : Prop := ∀ (h : List w8) (pw : Bytes), Bcrypt.hashOf h pw → hashedPw (b64 h) pw

/-! ## Resources -/

/-- Ghost names of one auth store: opaque. -/
opaque AuthNames : Type := Unit

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`st` is a member's auth store over the cluster `γ`** (persistent; the header). -/
opaque authStoreAt (st : Loc) (γ : Cluster) (γa : AuthNames) : IProp GF := iprop(True)

/-- **The writer: the store's current state is its `i`-th, `a`** (exclusive). -/
opaque authCur (γa : AuthNames) (i : Nat) (a : AuthState) : IProp GF := iprop(True)

/-- **The store's `i`-th state is `a`** (persistent). -/
opaque authAt (γa : AuthNames) (i : Nat) (a : AuthState) : IProp GF := iprop(True)

/-- **Every view of the store is at its `i`-th state or later, from now on** (persistent). -/
opaque authLb (γa : AuthNames) (i : Nat) : IProp GF := iprop(True)

/-- **The store's provider has assigned no token of an `Authenticate` index above `n`**
(exclusive; the simple provider's once-only right, the header). -/
opaque tokFrom (γa : AuthNames) (n : Nat) : IProp GF := iprop(True)

/-- **The store's provider issues root tokens without a collision** (persistent: the no-op and JWT
providers; not the simple one). -/
opaque rootTokOk (γa : AuthNames) : IProp GF := iprop(True)

/-- **`ctx` is an `Authenticate` context for `name` at the entry index `idx`** (persistent; the
header's realization). -/
opaque authnCtx (γa : AuthNames) (ctx : GoInterface) (name : GoString) (idx : Nat) : IProp GF :=
  iprop(True)

/-- **`tp` is a token provider for the cluster `γ`** (exclusive: given to one store), able to issue
root tokens without a collision if `rt`. Its methods' contract (a bundle over the `TokenProvider`
interface, PRINCIPLES "an interface value gets a bundle"): `info(ctx, tok, rev)` returns `(ai,
true)` only for a token of a user `u` with `tokenUser γ tok u`, `ai` naming `u`; `assign(ctx, name,
rev)` from an `authnCtx` returns a token of `name` or an error; `enable`, `disable`,
`invalidateUser`, `genTokenPrefix` do not panic. -/
opaque tokenProviderAt (tp : GoInterface) (γ : Cluster) (rt : Bool) : IProp GF := iprop(True)

/-- (provisional, 4b's `schema.AuthBackend`) **`be` is an auth backend whose buckets hold the auth
state `a`** (exclusive: the store's share of the backend; users' passwords as bcrypt hashes of
`a`'s, roles' and permissions' lists up to order, users' roles sorted), with the contracts of its
`BatchTx`, `ReadTx`, `GetUser`, ... . -/
opaque authBackendAt (be : GoInterface) (a : AuthState) : IProp GF := iprop(True)

/-- (provisional, 2a's grpc boundary) **`ctx`'s incoming metadata is `o`** (persistent;
`metadata.FromIncomingContext`'s answer: `none` for a context with none, as `s.ctx` and the internal
requesters'; every key with at least one value, as grpc's transports and `metadata.New` make them,
`nonissues/etcd-auth-token-md-empty.md`). 2a's `Grpc.rpcCtx ctx md` gives `some md`. -/
opaque ctxInMD (ctx : GoInterface) (o : Option MD) : IProp GF := iprop(True)

/-- **The token `ctx` carries** (`mdToken` of its incoming metadata). -/
def ctxToken (ctx : GoInterface) (o : Option GoString) : IProp GF :=
  iprop((∃ md, ctxInMD ctx (some md) ∗ ⌜o = mdToken md⌝) ∨ (ctxInMD ctx none ∗ ⌜o = none⌝))

/-- (provisional, 2a's grpc `peer`/`credentials` boundary) **The TLS client identity of `ctx`**
(persistent): `some cn`, the common name of the first verified chain's leaf of a TLS peer, for a
request without a `grpcgateway-accept` header; `none` otherwise (no peer, not TLS, no verified
chain, a gateway request). What `AuthInfoFromTLS` reads. -/
opaque ctxCertUser (ctx : GoInterface) (c : Option GoString) : IProp GF := iprop(True)

/-- **The request message `r` asks `rq`** (persistent: read-only; `*pb.Auth<Kind>Request`). For
`userAdd name pw noPw` and `userChangePassword name pw`: `Name = name`, `Options.NoPassword = noPw`
(nil options: `false`), and either `HashedPassword = hp` with `hashedPw hp pw` and `Password = ""`
(the server's form) or `HashedPassword = ""` and `Password = pw`, at most 72 bytes (a pre-3.5
entry). For `roleGrantPermission name perm`: `Perm` non-nil, of `perm`'s type, key and range end. -/
opaque authReqAt (r : Loc) (rq : Req) : IProp GF := iprop(True)

/-- **`p` is a fresh `*pb.<Kind>Response` for the answer `res` to `rq`** (owned; its `Header` nil,
which the applier sets): `UserGet`'s roles, `RoleGet`'s permissions, the lists, in the store's order
(a permutation of the model's). -/
opaque authRespAt (rq : Req) (res : Resp) (p : Loc) : IProp GF := iprop(True)

/-- **`p` is a fresh `*pb.AuthenticateResponse` carrying the token `tok`** (owned; its `Header`
nil). -/
opaque authnRespAt (p : Loc) (tok : GoString) : IProp GF := iprop(True)

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
def authReqAt_persistent.spec : Prop := ∀ r rq, Persistent (authReqAt (GF := GF) r rq)
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

/-- **The writer's premise for an admin step**: each state the step may move to (other than `a`)
is one the cluster reached, and its records fit bbolt (`recordsFit`). The apply thread has it from
the committed entry it applies (2d: the history's next state is fixed at the commit). -/
def admNext (γ : Cluster) (rq : Req) (a : AuthState) : IProp GF :=
  iprop(□ ∀ (a' : AuthState) (res : Resp), ⌜admStep rq a a' res ∧ a' ≠ a⌝ -∗
    authReached γ a' ∗ ⌜recordsFit a'⌝)

/-- **An admin method** `e` of the store `st` for the request `rq` (its message described by `P`):
from the writer's state, the step `admStep` (W0's effect) to `a'`, recorded as the next state, and
the reply. -/
def AdminTriple (e : Expr) (P : IProp GF) (st : Loc) (rq : Req) : Prop :=
  ∀ (γ : Cluster) (γa : AuthNames) (i : Nat) (a : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ P ∗
      authStoreAt st γ γa ∗ authCur γa i a ∗ admNext γ rq a }}
    e
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); P ∗
      ∃ (a' : AuthState) (res : Resp), ⌜admStep rq a a' res⌝ ∗ authCur γa (i + 1) a' ∗
        admReply rq res resp err }}

/-- **What a permission check of `u` (revision `rev`) on `t` over `rng` returns**, from the lower
bound `i0`: its three views' recorded states (the flag at `jf`, the backend at `jx`, the cache at
`jc`, each at or after `i0`), and `nil` (`checkOk`), `ErrUserEmpty` (no user: revision `0`),
`ErrAuthOldRevision` (a revision below the store's), or `ErrPermissionDenied` (`checkDenied`). -/
def checkPost (γa : AuthNames) (i0 : Nat) (u : GoString) (rev : w64) (t : PermType)
    (rng : KeyRange) (err : GoInterface) : IProp GF :=
  iprop(∃ (jf jx jc : Nat) (af ax ac : AuthState), ⌜i0 ≤ jf ∧ i0 ≤ jx ∧ i0 ≤ jc⌝ ∗
    authAt γa jf af ∗ authAt γa jx ax ∗ authAt γa jc ac ∗
    ⌜(err = GoInterface.nil ∧ checkOk u rev t rng af ax ac) ∨
     (err = errOf .userEmpty ∧ af.enabled = true ∧ rev = W64 0) ∨
     (err = errOf .authOldRevision ∧ af.enabled = true ∧ rev ≠ W64 0) ∨
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
opaque jwtTokOk (γ : Cluster) (opts : GoString) : IProp GF := iprop(True)

end init

/-- The token provider's kind in an `--auth-token` option string: what precedes the first comma. -/
def optsKind (opts : GoString) : GoString := opts.takeWhile (fun b => decide (b ≠ 44#8))

/-- The state `NewAuthStore` starts from: a backend's state, with revision `1` for a fresh
backend's `0` (`commitRevision`). -/
def normRev (a : AuthState) : AuthState := if a.rev = 0 then { a with rev := 1 } else a

end Auth
end EtcdGrove
end Perennial
