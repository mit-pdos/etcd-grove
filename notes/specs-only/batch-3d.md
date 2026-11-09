# Batch 3d: etcd's auth store (`server/auth`)

Author's report (2026-11-09). All files build (`etc/specs-build.sh --dir
Spec/go_etcd_io/etcd/server/v3/auth Spec/golang_org/x/crypto/bcrypt`: 59 modules OK); the snippets
vet (`go vet ./specreq/auth/`, gofmt clean).

## Files

- `Spec/go_etcd_io/etcd/server/v3/auth/Api.lean`: the vocabulary (namespace `Auth`).
- `Spec/go_etcd_io/etcd/server/v3/auth/Internal.lean`: the package's internal vocabulary (its
  helpers' specs only).
- 54 spec files, one per function of the old tree (`specs-ref`'s 54, none left out):
  - **admin, the writer's** (one `AdminTriple` each): `authStore__{UserAdd, UserDelete,
    UserChangePassword, UserGrantRole, UserGet, UserList, UserRevokeRole, RoleAdd,
    RoleGrantPermission, RoleGet, RoleRevokePermission, RoleDelete, RoleList}`; `AuthEnable`,
    `AuthDisable`, `Authenticate`, `HasRole`, `Recover`;
  - **readers** (any goroutine, from a lower bound `authLb`): `IsAuthEnabled`, `Revision`,
    `IsPutPermitted`, `IsRangePermitted`, `IsDeleteRangePermitted`, `IsAdminPermitted`,
    `CheckPassword`, `AuthInfoFromCtx`, `AuthInfoFromTLS` (assumed: names only), `WithRoot`,
    `GenTokenPrefix`, `BcryptCost`, `Close`;
  - **constructors**: `NewAuthStore`, `NewTokenProvider`, `newTokenProviderSimple`,
    `newTokenProviderNop`, `newTokenProviderJWT` (assumed);
  - **internal helpers** (mirror the code): `lockedReadTx`, `isOpPermitted`, `isRangeOpPermitted`,
    `refreshRangePermCache`, `getMergedPerms`, `checkKeyPoint`, `checkKeyInterval`, `isOpenEnded`,
    `isValidPermissionRange`, `hasRootRole`, `commitRevision`, `setRevision`,
    `setupMetricsReporter`, `authInfoFromToken`, `decomposeOpts`; assumed (untranslated):
    `selectPassword`, `redactToken`, `tokenSimple.genTokenPrefix`.
- `Spec/golang_org/x/crypto/bcrypt/{Api, GenerateFromPassword, CompareHashAndPassword}.lean`: the
  bcrypt trust boundary (namespace `Bcrypt`, new): `hashOf h pw`; generation fails only above 72
  bytes or cost 31; a hash accepts its own password (nothing about others).
- Snippets: `examples/specreq/auth/{check,token,admin,boot}.go` (13 requirement functions).
- Non-issues (new): `nonissues/etcd-auth-revision-before-visible.md` (blocks-proof: yes),
  `nonissues/etcd-auth-withroot-token-collision-panic.md` (yes),
  `nonissues/etcd-auth-password-72-byte-prefix.md` (no). `nonissues/INDEX.md` needs
  `etc/issues-status.py --index` (not run: a shared generated file).

## The design, in short

- **The store's state is W0's `AuthState`**, and the store keeps a numbered **history** of its
  states (`authAt γa i a`, persistent). **Every recorded state is a reached state of the cluster**
  (`authAt_reached`: an `etcdLb γ σ` with `σ.auth = a`), because the only writer supplies that fact
  for each step (`admNext`). The history is a chain of admin steps (`authAt_reach`).
- **One writer**, `authCur γa i a` (the apply thread). Each admin method is `admStep rq a a' res`:
  W0's `authStep` effect at an authorized caller (the applier checks first). Between writer calls
  every view is at the current state (`authCur_at` gives `authLb γa i`), so the writer's checks
  answer at exactly `a`.
- **Readers see four views that move at different moments** (the flag, the revision atomic, the
  backend's read transaction, the permission cache). Each reader's post names the recorded state of
  each view it read, from its lower bound: `checkPost` (flag `jf`, backend `jx`, cache `jc`). A
  **pass** is `State.permits` at one recorded (reached) state: 2b's and 2c's need. A **denial** is
  stated over the three views (exact): at one state only when they coincide (the writer).
- **Tokens** are W0's `tokenUser γ tok u`: `AuthInfoFromCtx` maps a context's token
  (`ctxToken`, over 2a's `ctxInMD`) to such a user; `Authenticate` and `WithRoot` assign such tokens.
  The simple provider's once-only right is `tokFrom γa n`; root tokens need `rootTokOk`.
- **One spec per function for every mode** (auth on and off are values of `a.enabled`). The old
  per-mode verdicts (`permVerdict M`, `adminVerdict M`, `authStoreKit`'s off axiom) are gone.

## Exported vocabulary (`Api.lean`)

Pure:
- `AuthErr` (the package's error variables), `AuthErr.etcd` (`togRPCError`'s table; `none` for
  `ErrNoPasswordUser`, `ErrInvalidAuthOpts`).
- `rngInverted r`: a proper range end at or below a non-empty key (the cache may refuse it).
- `validPerms a`: every permission's range is one `RoleGrantPermission` accepts.
- `recordsFit a` (opaque, provisional 4a/3h): every record fits bbolt's limits, the revision a `uint64`.
- `admStep rq a a' res`: W0's `authStep` at a caller who may make the request.
- `AuthReach a a'`: a chain of `admStep`s.
- `checkOk`/`checkDenied u rev t rng af ax ac`: a check's pass/denial over its three views.
- `trimBearer`, `MD`, `mdGet`, `mdToken md`: the token `AuthInfoFromCtx` reads.
- `b64 h` (opaque, provisional `encoding/base64`), `hashedPw hp pw` (opaque): the proposal's hash form.
- `optsKind opts`, `normRev a`.

Resources (persistent unless said):
- `AuthNames` (opaque); `authStoreAt st γ γa`: `st` is a member's store over cluster `γ`.
- `authCur γa i a` (exclusive, timeless): the writer's state.
- `authAt γa i a`: the `i`-th recorded state; `authLb γa i`: every view at `i` or later.
- `tokFrom γa n` (exclusive): no token of an index above `n` assigned.
- `rootTokOk γa`: root tokens do not collide (not the simple provider).
- `authnCtx γa ctx name idx`: an `Authenticate` context (3a introduces it from 2d's entry).
- `tokenProviderAt tp γ rt` (exclusive): a provider bundle (interface contract).
- `authBackendAt be a` (exclusive, provisional 4b): an `AuthBackend` holding `a`.
- `ctxInMD ctx o`, `ctxCertUser ctx c` (provisional 2a); `ctxToken ctx o` (transparent).
- `authReqAt r rq`, `authRespAt rq res p` (exclusive), `authnRespAt p tok` (exclusive)
  (provisional 3h); `authInfoAt ai dq u rev` (transparent); `authReached γ a` (transparent).
- `errOf e` (the variables' values); `jwtTokOk γ opts` (provisional: JWT/2d).
- Shapes: `admNext γ rq a`, `AdminTriple e P st rq`, `admReply`, `checkPost`, `adminPost`,
  `recvOk`, `waiterOk iw`.

Laws: `authStoreAt_persistent`, `authAt_persistent`, `authLb_persistent`, `rootTokOk_persistent`,
`authnCtx_persistent`, `ctxInMD_persistent`, `ctxCertUser_persistent`, `authReqAt_persistent`,
`authCur_timeless`, `authAt_timeless`, `authLb_timeless`; `authCur_excl`, `tokFrom_excl`,
`authCur_at` (the writer's state recorded, every view at it), `authAt_agree`, `authAt_le` (nothing
recorded past the writer's state), `authLb_le`, `authLb_mono`, `authAt_reach` (the history is a
chain of admin steps), `authAt_reached` (every recorded state is reached), `authAt_valid`;
`errOf_ne_nil`, `errOf_inj`, `init` (the error variables), `hashedPw_intro`.

Internal (`Internal.lean`): `txAt`, `rdTx` (with `rdTx_txAt`, `rdTx_RUnlock`), `wrStep`, `wrRec`,
`cacheEntry`, `cacheOwn`, `optsMapAt`, `userRolesAt`, `tpOpen`.

## Main changes from the old specs

- **Modes merged**: no `AuthMode`, no off axiom; every spec holds at every value of `a.enabled`.
- **The reads are stated over W0's state and the cluster** (`authAt_reached`), not the store's own
  ghost history only: 2b's "nil only if a reached state permits" is `checkPost` + `authAt_reached`.
- **The check's timing is exact** (the brief's request, with `nonissues/etcd-doserialize-auth-enable-
  race.md`): three views, each at a recorded state at or after the reader's bound. Found while
  stating it: `nonissues/etcd-auth-revision-before-visible.md` (below).
- **`UserAdd`'s two specs merged** (`spec`/`specSure`): the request's hash form (`authReqAt`) rules
  out `ErrNoPasswordUser`; the name bound is `recordsFit` in `admNext` (a scope restriction:
  `issues/etcd-auth-useradd-long-name-fatal.md`).
- **bcrypt is a boundary** (new): `CheckPassword`'s success claims no password equality.
- **The reader stocks are gone** (`List.replicate actualMaxReaders RD`): readers take a `threadTok`.
- **`WithRoot`** now holds at every mode, with the premise `rootTokOk` (was auth-off only).
- **`AuthInfoFromCtx`** no longer states the `AuthInfo`'s revision (no caller can use it soundly).
- **`Close`** needs nothing but the handle (the old closer token is unneeded).
- The old premise `tp ≠ nil` is in `tokenProviderAt`; `Permission_Type_name` is the package init.

## Functions left out

None of the old 54. Not specified individually: the token providers' methods (`tokenSimple.{info,
assign, enable, disable, invalidateUser, assignSimpleTokenToUser, isValidSimpleToken}`,
`simpleTokenTTLKeeper.*`, `tokenNop.*`, `tokenJWT.*`): they are the `TokenProvider` interface's
contract, `tokenProviderAt` (a bundle, PRINCIPLES "an interface value gets a bundle"), proved from
the concrete methods inside the constructors' proofs; nothing outside the package calls them.
`permSlice.{Len,Less,Swap}` likewise (a sorter for `sort.Sort`). They had proofs in the old tree
(`Proof/.../auth/TokenSimple*.lean`, `TokenKeeperRun.lean`), so they should get specs when the
proofs are written.

## Open questions for the user

1. **`doSerialize`'s revision re-check** (`nonissues/etcd-auth-revision-before-visible.md`): an
   admin step bumps the revision atomic before publishing the new users and roles, so a simple
   token's (or a certificate's) reader can pass its check at the old state and read data written
   after the change. 2c's `Range`/`Txn`/`RangeStream` sketches assumed the opposite. Options: a fix
   on the fork (bump the atomic after the batch transaction's `Unlock`), or a disjunct in 2c's
   `srvStep` (as for the `AuthEnable` race). Same decision family as
   `nonissues/etcd-doserialize-auth-enable-race.md`.
2. **`WithRoot` with the simple provider** (etcd's default; `nonissues/etcd-auth-withroot-token-
   collision-panic.md`): two random root-token prefixes may collide and the member panics; no sound
   panic-free spec exists. The spec takes `rootTokOk` (given by the no-op and JWT providers only).
   Options: a fork fix (`assignSimpleTokenToUser` returns an error instead of panicking; `WithRoot`
   already handles it), or a probabilistic premise (against PRINCIPLES' "no false universal").
3. **W0's model** (`req/go_etcd_io_etcd_api_v3.md`, "from 3d"): `authenticate`'s success must not
   require the password to be the user's (bcrypt); `roleGet "root"` with no stored `root` role is
   `ErrRoleNotFound` in the code (**`authStore.RoleGet.spec` is false at that input until W0
   changes**); `roleGrantPermission` should succeed only for valid ranges; inverted ranges; a
   `tokenUser_agree` law; the principal of a request with both a token and a certificate.
4. **The cluster in the store's handle**: `authStoreAt st γ γa` names W0's `Cluster` (the reads give
   `etcdLb γ`, the tokens `tokenUser γ`). The alternative (a saved predicate fixed at creation, or the
   writer handing a client-owned history through an atomic update, TaDa) is more general and costs
   every caller a parameter; I chose the concrete cluster for fewer abstractions. Say if a
   cluster-free store API is wanted.

## `req/` sections written (all "## from 3d")

- `req/go_etcd_io_etcd_api_v3.md` (W0): the model items above.
- `req/go_etcd_io_etcd_server_v3_etcdserver.md` (2c, 2d, 2e): the revision race; `Authenticate`'s
  loop; `reqPrin` needs `γ`; `WithRoot`; the readers' lower bound from `srvApplied`; the hash form;
  the writer's `authCur`/`admNext`; `Recover`'s premises; `Authenticate`'s apply; boot (`waiterOk`,
  `jwtTokOk`, `authBootRes`).
- `req/google_golang_org_grpc.md` (2a): `ctxInMD` (any context; non-empty values;
  `NewIncomingContext`), `ctxCertUser`, `mdPrin`'s realization, the error table.
- `req/go_etcd_io_etcd_server_v3_etcdserver_apply.md` (3a): its slots `authOk`/`authSt`/`authRead`/
  `authRecordFits`/`permReads` mapped to this API; `admNext` to thread; `authnCtx`/`tokFrom` at
  `Authenticate`'s apply; messages.
- `req/go_etcd_io_etcd_server_v3_storage_schema.md` (4b): `authBackendAt`'s contract.
- `req/go_etcd_io_etcd_api_v3_etcdserverpb.md` (3h): `authReqAt`, `authRespAt`, `authnRespAt`.
- `req/go_etcd_io_etcd_pkg_v3_adt.md` (3f, new file): the interval tree's `Insert`, `Intersects`,
  `Contains`.

## Callers' needs, answered (`req/go_etcd_io_etcd_server_v3_auth.md`)

- 2b item 1 (`AuthInfoFromCtx`): `authStore.AuthInfoFromCtx.spec` (no credentials, a `tokenUser`
  user, or `ErrInvalidAuthToken`); the TLS fallback: `AuthInfoFromTLS.spec` over `ctxCertUser`.
- 2b item 2 (`IsRangePermitted`): `checkPost`: `nil` ⇒ `checkOk` at recorded states ⇒ one reached
  state permits (with `authAt_reached`); the errors `ErrUserEmpty`, `ErrAuthOldRevision`,
  `ErrPermissionDenied`.
- 2b item 3: `Auth.init.spec`.
- 2c items 1-4: `AuthInfoFromCtx`, `WithRoot` (with `rootTokOk`), `CheckPassword` (the backend
  view's revision), `GenTokenPrefix`, `Authenticate`'s apply (`tokenUser`), `Revision` (two equal
  reads: same users and roles, via `authAt_reach`), `IsPutPermitted`/`IsAdminPermitted`/
  `IsAuthEnabled`, bcrypt (`Bcrypt.*`, `hashedPw`).
- 2b round 1 (client certificates): the store side is `AuthInfoFromTLS.spec`; the principal's
  definition is 2a's/W0's (`req/google_golang_org_grpc.md`, item 2).
