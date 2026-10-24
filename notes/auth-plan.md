# Plan: specifying and proving etcd's authentication and authorization (auth, RBAC)

**Status.** S3 carried out (2026-10-24, branch `auth-s3`; `notes/decisions.md`, "S3 of the auth plan"):
the store's checks return the model's verdicts in every mode (`isOpPermitted`/`Is*Permitted`
`permVerdict`, `IsAdminPermitted` `adminVerdict` over an `Option AuthInfo`, `IsAuthEnabled`/`Revision`
theirs; `auth/VerdictLemmas.lean`), `isAuthStore_of_authInv` derives the apply layer's contract in the
store's mode, A2's `srvAdminNilOk` premise is derivable; A0's one-state verdict was unprovable and is
corrected (`permitted` without the revision conjunct, the refused half over the four states read,
`AuthView`/`refusedV`; `reqShape` inside the model; recorded states carry `permKeysOk`); `hasRootRole`
stays an axiom, restated to return `isRoot` (needs a `sort.SearchStrings` spec in Perennial). S1 carried out (2026-10-23, branch `auth-s1`; `notes/decisions.md`, "S1 of the auth plan"):
`authpb` translated as data (`authpb.toml`), schema's auth backend translated and its read side
proved over the buckets (`etcdserver/InvAuthBackend.lean`: `authReader`/`authRTx`/`authBE`,
`authBucketsAre`; `auth/Buckets.lean`: the records, `userOut`/`roleOut`, `authSnap`), the store's
contract `authReadTxOk` returning the model's state in the mode `M`, which now threads through
`authInv` and the 13 request-side specs; +2 trust-boundary axioms (`proto.Unmarshal` on `User` and
`Role`); not done: `GetAllUsers` (no `UnsafeForEach` spec), the write side (S4), the derivation of
`authReadTxOk` from schema's proofs (S4). A0 carried out (2026-10-23, branch `auth-a0`; `notes/decisions.md`, "A0 of the auth
plan"): the model `Proof/go_etcd_io/etcd/server/v3/auth/Model.lean` (`AuthState`, `permitted`,
`adminOk`, the history `authHist`/`authStateAt`, the mode `AuthMode` with `off`/`any`/`on γa`, the
verdicts `permVerdict`/`adminVerdict`/`enabledVerdict`/`revisionVerdict`), the contracts
`apply.isAuthStore`/`permCheck2`/`permCheck3` and `AEnv.authMode` over it, the matrix
`notes/auth-matrix.md`. What differed from the plan: the verdicts are two one-directional facts
over recorded states, not `↔` at one state (the checks' own TOCTOU, decisions); the history is
indexed by position, not by the auth revision (`AuthEnable` does not bump it); `isReqAuth` is
untouched (the token binding is S5's). A1 carried out 2026-10-23 (branch `auth-a1`: the class statement for the verified checks and the API-layer handlers, `apply/AuthClass.lean`; the method-level statement is its follow-up, `notes/decisions.md`, "A1 of the auth plan"). A1's follow-up carried out 2026-10-24 (branch `auth-a3`: the request's principal is an index of the chain's resources, the KV methods' posts state the request's class for it through the chain up to `apply.Apply`, `Apply`'s admin check passed for it, `UserGet`'s self case; `notes/decisions.md`, "A3 of the auth plan, the apply layer"). S1 carried out 2026-10-23 (branch `auth-s1`: `authpb` as data, schema's auth backend's read side proved over the buckets, the store's contract with the mode, two `proto.Unmarshal` sibling axioms; `notes/decisions.md`, "S1 of the auth plan"). A2 carried out 2026-10-23 (branch `auth-a2`: the API layer's two guards and the entry points they guard -- `Compact`, the eight maintenance wrappers, `RemoveMember`, `MemberList` -- over their inner operations as token-carrying contracts; left: the member operations that marshal JSON, the lease entry points and their key checks; `notes/decisions.md`, "A2 of the auth plan"); S2 carried out 2026-10-23 (branch `auth-s2`: the permission cache computes the model's `coversPoint`/`coversRange` of a recorded state, `getMergedPerms`/`refreshRangePermCache`/`isValidPermissionRange` proved, the bytes-affine tree's three facts axioms pending S2b; `notes/decisions.md`, "S2 of the auth plan"); S2b carried out 2026-10-24 (branch `auth-s2b`: the tree's proof generic in the key representation `adt.KeyRep`, the string- and bytes-affine results its instances, the three axioms removed, `Contains` proved; `notes/decisions.md`, "S2b of the auth plan"); S4, S5, A3's rest, A4, E not started. Prompted by etcd-io/etcd#22595 (the
proposal to revert Auth to Beta: "the feature was never really finished", a stream of security
reports) and #22540 / PR #22541 (an "auth matrix" test: every gRPC method on the client port
classified public / authenticated / RBAC / admin and probed with no token, an invalid token and an
unprivileged user).

## Why, and what the bugs look like

The 2026 advisories are all **coverage** bugs at the API layer, not bugs inside the permission
check:

| advisory | what was missing |
|---|---|
| GHSA-q8m4-xhhv-38mg (CVE-2026-33413), "multiple APIs" | `MemberList`, `Alarm`, lease APIs, `Compact` reachable without authentication or authorization; "the same underlying flaw in the gRPC API layer" |
| GHSA-rfx7-8w68-q57q, nested transactions | the RBAC walk of a `Txn` did not descend into nested `Txn`s |
| GHSA-x35m-3gp4-4fh5, `PrevKv` / lease in a nested `Put` | a `Put` with `PrevKv` reads, a `Put` with a lease touches the lease's other keys: checks missing inside transactions |
| GHSA-xg4h-6gfc-h4m8 (CVE-2026-73499), watch `RangeEnd = "\x00"` | `isWatchPermitted` let an open-ended watch through on a single-key READ grant |

The matrix test (#22541) is the right shape of specification: 49 methods, each with a privilege
class (2 public, 6 authenticated, 32 RBAC, 27 admin), and request-shape probes (open-ended
`RangeEnd`, `PrevKv` on write-only keys, leases holding keys the caller cannot write, nested
`Txn`, each `Txn` branch, serializable reads, requests whose class depends on their fields:
`Alarm` get vs activate, `UserGet`/`RoleGet` of oneself vs another). Its author says it does not
"prove there are no more security issues": that is what a proof over the same classification can
add, for the code paths this repository has translated.

## What the repository has (so the starting point is not zero)

- **The auth store's request side is proved, for memory safety only** (unit P2, 2026-10-14;
  `Proof/go_etcd_io/etcd/server/v3/auth/`): `IsPutPermitted`, `IsRangePermitted`,
  `IsDeleteRangePermitted` (through `isOpPermitted`, `isRangeOpPermitted`, the permission cache's
  `checkKeyPoint`/`checkKeyInterval`, `isOpenEnded`), `IsAdminPermitted`, `IsAuthEnabled`,
  `Revision`, `lockedReadTx`, `AuthInfoFromCtx`/`authInfoFromToken`; 14 of the package's 89
  functions, 151 of 1,359 lines. Their results "return nothing about the permission: the
  contracts only promise an error the gRPC layer can take" (`notes/decisions.md`, P2). The store's
  invariant `authInv` (`InvAuth.lean`) holds the locks and three contracts for what the store calls
  through interfaces: the backend's read transaction (`UnsafeGetUser` over an **axiomatized**
  `authpb.User`), the token provider's `info`, and the cached interval trees (`ivtQuery`, bytes
  affine: `adt.ownIvt`, the tree's proof, covers string-affine intervals only).
- **The apply layer's auth applier is proved**, same strength (`apply/auth.go`: 16 of 16
  functions; `authApplierV3.{Apply,Put,Range,DeleteRange,Txn,LeaseRevoke,UserGet,RoleGet}`,
  `checkPutAuth`, `checkTxnAuth`, `checkTxnReqsPermission`, `checkLeasePuts*`). The contract
  `apply.isAuthStore st γ P f RD on RW` (`apply/Contracts.lean`) says of a permission check only
  `applyErrIs err` and `on = false → err = nil`; the apply chain's model has an auth mode
  (`Chain.auth on`, `E.authOn`), and every closed theorem runs with `authOn = false`.
- **The gRPC layer**: `AuthInfoFromCtx` is threaded through the request path (`isReqAuth`, unit
  A2: the reader resource `E.RD` every caller holds); `v3rpc/auth.go`'s `AuthServer` is 1 of 20
  functions; the KV handlers and the watch handler (its `isWatchPermitted`) are verified at the
  memory-safety level with `E.authOn = false`; `AuthAdmin.isPermitted`/`requireAuthInfo` and the
  server's `isAdmin`-style checks (`server.go:1391`, `v3_server.go`'s lease checks) are not.
- **Names only**: `authpb` (types axiomatized; only `Permission_Type` and its three constants
  translated), the store's admin side (`AuthEnable`/`Disable`, `UserAdd` ... `RoleGrantPermission`,
  `Recover`, `refreshRangePermCache`, `getMergedPerms`), `NewAuthStore`, the token providers
  (`simple_token.go`'s TTL keeper, `jwt.go`), `AuthInfoFromTLS`, `hasRootRole` (an axiom returning
  any boolean), schema's auth backend (`storage/schema/auth*.go`: 1 of 17).
- **Seven findings in `issues/`** from the proofs so far: `NewAuthStore` with a nil token provider,
  user and role records beyond bbolt's key or value size killing every member on apply, the
  snapshot-time panic on a permission check, `AuthInfoFromTLS`'s type assertion, the empty token
  metadata list, the `AuthStatus` metric label.

## Is `auth/store` still the right place to start?

**Yes, as the first of two tracks, but the statement comes first.** The store is where
"permitted" gets its meaning: a user's roles, a role's key permissions, the root role, the
enabled flag and the revision. Nothing about authorization can be stated end to end until the
store's checks are specified as computing a function of that state rather than returning "some
error". But the known bugs are at the API layer, and a check-coverage statement there can be made
over the store's *contract* before the store's internals are proved. So:

- **A0 (first, small): the authorization model and oracle-parametrized contracts.** Shared by
  both tracks; everything else is stated in its terms.
- **S (the store): the checks compute the model**, starting exactly where P2 stopped
  (`isOpPermitted` and the permission cache), then the admin side that maintains the state.
- **A (the API layer): every method enforces its class**, the matrix as the specification, over
  the oracle; the request-shape probes become lemmas.

The two tracks are independent after A0 and can run in parallel (two sessions). The headline
result, an auth-enabled closed theorem, needs both.

## Decisions to take (recommendations)

**D-AU1. The model.** A pure `AuthState`: `enabled : Bool`, `revision : Nat`, `users : Map Name
User` (`User`: password hash opaque, `roles : List Name`, options), `roles : Map Name Role`
(`Role`: `perms : List (Key × RangeEnd × PermType)`). Derived: `rootUser u := "root" ∈ u.roles`,
`permits st u k rangeEnd ty : Prop` (the union of the user's roles' intervals covers `[k, rangeEnd)`
in the bytes-affine order, `rangeEnd = "\x00"` meaning open-ended, a point when `rangeEnd` is
empty; exactly `getMergedPerms` + `checkKeyInterval`/`checkKeyPoint`'s meaning), `adminOk st ai`,
`revisionOk st ai := ai.revision ≥ st.revision` (the `ErrAuthOldRevision` rule: a token minted
before a permission change is refused). A `Principal`: `none` (no token; with auth enabled, every
non-public method refuses it), or `(user, revision)` from a token. `permits` is the matrix's
oracle for the RBAC class; `adminOk` for admin; `principal ≠ none` for authenticated. *Rejected:*
modelling the interval trees' structure (the cache is an implementation of the union of
intervals; only the union matters); modelling password hashing (bcrypt stays a trust-boundary
contract: `CheckPassword` returns the user's revision iff the password matches, an opaque
predicate on the hash).

**D-AU2. The contracts take the model.** `apply.isAuthStore` and the store's own specs gain an
`AuthState`-valued ghost variable `γa` (the store's authority, held by the admin side; fractional
or a monotone view for readers): each check's postcondition becomes `err = nil ↔ permits st ...`
(resp. `adminOk`), under `revisionOk`; `IsAuthEnabled` returns `st.enabled`; `AuthInfoFromCtx`
returns the principal the token provider bound to the token (`tokenProviderOk` gains the binding:
`info` returns `(u, rev)` only for a token `assign` gave for `(u, rev)` and not since invalidated;
the simple provider's TTL and the JWT provider's signature check are what make that true, each a
contract with its trust-boundary part named). The `authOn` mode (`notes/decisions.md`, "`authOn`
in the model", judged "mechanical but wide") is subsumed: `on = st.enabled`.

**D-AU3. Track S, the store computes the model** (the `auth/store` start):

- S1 `authpb` translated like `raftpb` was (the getters; protobuf plumbing excluded), so `User`
  and `Role` are data; schema's `UnsafeGetUser`/`UnsafeGetRole`/`GetAllUsers`/`GetAllRoles`
  proved over the backend's buckets (`proto.Unmarshal` the existing trust-boundary axiom); the
  auth buckets' contents are the model's `users`/`roles` (as `kvInv` relates the key bucket to the
  KV model).
- S2 the permission cache: `getMergedPerms`, `refreshRangePermCache` proved to build trees whose
  `Contains`/`Intersects` are `permits` (needs the interval tree over **bytes-affine** intervals:
  either `adt.ownIvt` generalized to a comparator, or a bytes-affine instance; the tree's own
  proof is done, `btree`-style, for strings). **Done 2026-10-23** (branch `auth-s2`) with the
  bytes-affine tree's three facts as axioms (`adt/BytesIvl.lean`); the generalization is **S2b**
  (below).
- S2b the interval tree over a comparator: `adt.ownIvt`'s proof generalized to a key type with
  its Go value, its `Compare` spec and the resource a comparison needs (nothing for strings, a
  slice's read-only contents for bytes), instantiated for `StringAffineComparable` and
  `BytesAffineComparable`, replacing the three axioms; `Contains` proved (`Visit`'s visitor
  contract extended with a stop). Independent of S3-S5. **Done 2026-10-24** (branch `auth-s2b`:
  `adt.KeyRep`, the generic `ownIvtK`/`ownNode` with the key fields as atoms, the exported
  functions' generic results `<fn>_gen` with string- and bytes-affine wrappers, the internal
  specs generalized in place; `Contains` proved for both; 615 axioms; `notes/decisions.md`,
  "S2b of the auth plan").
- S3 `isOpPermitted`, `IsAdminPermitted`, `hasRootRole` (translated: `sort.SearchStrings` over a
  sorted `Roles`, so `UserGrantRole`'s sorting becomes a model invariant), `AuthInfoFromCtx` with
  the token binding: the P2 specs restated as D-AU2 and re-proved. **Done 2026-10-24** (branch
  `auth-s3`) for the checks' verdicts in every mode; `hasRootRole` restated, not translated
  (Perennial has no `sort.SearchStrings` spec); the token binding is S5's (`AuthInfoFromCtx`
  unchanged); the verdict's shape corrected (decisions, "S3 of the auth plan").
- S4 the admin side: `AuthEnable`/`AuthDisable`, `UserAdd`/`Delete`/`ChangePassword`/`GrantRole`/
  `RevokeRole`, `RoleAdd`/`Delete`/`GrantPermission`/`RevokePermission`, `Recover`, `commitRevision`:
  each a step of `AuthState`, the cache refreshed, the revision bumped; the apply layer's
  `applierV3backend.{AuthEnable, UserAdd, ...}` over them (the apply chain's `.auth` case becomes
  exact). This is where the two `issues/` fatals (record and name sizes) become premises.
- S5 `NewAuthStore` and `Authenticate`/`CheckPassword` (bcrypt the trust boundary), the token
  providers' `assign`/`info`/`invalidateUser` (simple: the TTL keeper and `indexWaiter`; JWT: the
  signature and claims as a trust-boundary contract), `WithRoot`, `HasRole`.

**D-AU4. Track A, every method enforces its class.** The matrix's table is the specification,
checked into the notes (49 rows, each with its class and, for RBAC, which keys/ranges the check
must cover):

- A1 the generic statement: for a method of class `c`, its handler's spec says the handler
  performs its effect (the apply step, the read, the stream's registration) only if the oracle
  allows the principal (`adminOk`; `permits` of every key the request reads or writes, the list
  defined per request shape: `Txn` recursively over nested transactions and both branches,
  `Put` with `PrevKv` also a read of the key, `Put` with a lease also writes of the lease's keys,
  `DeleteRange` with `PrevKv` also a read); and with auth disabled, everything is allowed. Stated
  over the **verified** handlers first (KV `Range`/`Put`/`DeleteRange`/`Txn`/`Compact`, `Watch`):
  the API layer's `AuthInfoFromCtx` and `chk` in `v3_server.go`, the apply layer's `checkTxnAuth`
  etc., so that both the pre-raft check and the apply-time check are covered (the apply-time one
  is what makes a change of permissions between proposal and apply refuse the write: the
  `ErrAuthOldRevision` rule).
- A2 the methods the advisories named: `MemberList`/`MemberAdd`/... (`Cluster`), `Alarm`,
  `LeaseGrant`/`LeaseRevoke`/`LeaseTimeToLive`/`LeaseLeases`/`LeaseKeepAlive`, `Compact`,
  `Defragment`/`Snapshot`/`Status`/`Hash*`/`MoveLeader`/`Downgrade` (`Maintenance`): translate the
  handlers (names-only today) and prove A1's statement for each; the admin check is
  `AuthAdmin.isPermitted`/`requireAuthInfo` (`v3rpc/auth.go`) and the server's `isAdmin`
  (`server.go:1391`, the TOCTOU the code comments on: the check at the API layer, the effect at
  apply; the statement makes the window explicit).
- A3 the Auth service's 17 methods (admin, but `Authenticate`, `AuthStatus` public, and
  `UserGet`/`RoleGet`/`UserChangePassword` of oneself); `Lock`/`Election` (the `v3lock`/
  `v3election` servers over the KV and lease APIs: their class follows from the calls they make).
- A4 the watch service's request shapes: `WithFromKey`, `WithPrefix`, `WithRange`, progress and
  fragment requests: `isWatchPermitted` on `Key`/`RangeEnd` as `permits` of the interval (the
  2026-07 bug is fixed at the pin; the proof is what says it stays fixed).

**D-AU5. The end-to-end result**: an example `examples/authkv` (one member, auth enabled at
start: root user, a user `u` with role `r` granted `[a, b)` READWRITE; clients as `u` and as a
user without the role; a workload of puts, ranges, deletes, transactions and watches inside and
outside `[a, b)`), with the closed theorem: the KV model's history contains no write by a
principal whom `permits` refuses at that revision, and no read's reply reveals a key outside the
principal's read permissions (watches included). This needs A1 for the KV and watch handlers, S1
to S3 for the store, S4 for enabling auth and the grants at start, S5 for `Authenticate` and the
token. The matrix's three probes (no token, invalid token, unprivileged user) are three clients of
that example.

**D-AU6. Out of scope (recorded):** TLS client certificates as identity (`AuthInfoFromTLS`,
`ClientCertAuth`: x509 is axiomatized), the gateway and proxy, `--listen-client-http-urls`'s CRL
bypass (TLS listener), JWT's cryptography (a contract), password hashing (a contract), the
`etcdctl`/clientv3 side of auth (`client/v3/auth.go`, token refresh in the retry interceptor is
already a premise of D29's refusal-freedom and would become real with S5).

## Stages and effort (rough, by analogy with past units)

| stage | what | depends on | size |
|---|---|---|---|
| A0 | `AuthState`, `permits`, `adminOk`, `revisionOk`; `isAuthStore`/`isReqAuth`/`tokenProviderOk` restated with the oracle (the 26 files that name `.auth`/`authOn`, about 100 lines, D-AU2); the matrix table in the notes | — | days |
| S1 | `authpb` translated, schema's auth backend proved, the auth buckets as the model | A0 | about a week |
| S2 | the permission cache = `permits` (bytes-affine interval tree) | S1 | about a week; **done** 2026-10-23 with the bytes-affine tree's `Insert`/`Intersects`/`Contains` as axioms (`adt/BytesIvl.lean`, +3) |
| S2b | the interval tree generalized to a comparator (string- and bytes-affine), the three axioms removed; `Contains` proved | S2 | about a week; **done** 2026-10-24 (the key fields as atoms kept the node unfoldings; `visit` re-proved for a stopping visitor and a degenerate query; 615 axioms) |
| S3 | P2's checks re-proved to compute the model; `hasRootRole`; the token binding | S1, S2 | days |
| S4 | the admin side as model steps; `Recover`; the apply layer's admin requests | S3 | one to two weeks |
| S5 | `NewAuthStore`, `Authenticate`, the token providers | S4 | about a week |
| A1 | the class statement for the verified KV and watch handlers, both layers | A0 | about a week; **done** 2026-10-23 for the checks (`checkPutAuth`, `checkTxnReqsPermission`, `checkTxnPermission`/`CheckTxnAuth`) and the API layer (`doSerialize`, `Range`, `isWatchPermitted`); the method-level statement **done** 2026-10-24 (branch `auth-a3`: the principal through `chainRes`, the class through the chain to `apply.Apply`, `Apply`'s admin pass) |
| A2 | the advisories' methods: Cluster, Lease, Maintenance, `Alarm`, `Compact` translated and proved | A1 | two weeks; **done** 2026-10-23 for the two guards and the guarded entry points (`Compact`, the eight maintenance wrappers, `RemoveMember`, `MemberList`, over their inner operations as token-carrying contracts: `notes/decisions.md`, "A2 of the auth plan"); left: `AddMember`/`UpdateMember`/`promoteMember` (`encoding/json`), the lease entry points and their key checks |
| A3 | the Auth service, Lock, Election | A2 | one to two weeks; the apply layer's part begun 2026-10-24 (branch `auth-a3`: `Apply`'s admin pass for the request's principal, `UserGet`'s self case; `RoleGet`'s has-role case waits for `HasRole`'s model) |
| A4 | the watch shapes | A1 | days |
| E | `examples/authkv`, the closed theorem | S1-S5, A1, A4 | one to two weeks |

S and A are independent after A0. The first results of value come early: A1 (the KV path enforces
its class, in both layers, on today's pin) is the proof-shaped answer to #22540 for the methods
the repository has; S3 says what "permitted" is.

## Where to start, concretely

1. A0: `Proof/go_etcd_io/etcd/server/v3/auth/Model.lean` (`AuthState`, `permits`, lemmas:
   `permits` monotone in the grants, open-ended and point cases), the matrix table
   (`notes/auth-matrix.md`, from PR #22541's list, re-derived from the handlers at the pin rather
   than copied), the contracts' restatement with the oracle (D-AU2), gates unchanged (the
   examples run with `enabled = false`).
2. S1 in `auth/store` (done 2026-10-23): `authpb.toml` as `raftpb`'s; `schema/auth*.go`
   translated with bodies; the read side proved; `authInv` takes the mode and the backend contract
   returns the state (`authReadTxOk`), "the buckets hold `st.users`/`st.roles`" being
   `authBucketsAre` (the derivation through it is S4's).
3. A1 on the KV handlers, in parallel.

## Go findings to expect

Each stage records what it finds in `issues/` (the format of `issues/README.md`). Candidates the
reading above already suggests, to confirm as they are reached: the API-layer/apply-layer TOCTOU
for membership and role changes (`server.go:1385`); `LeaseTimeToLive`'s key list reveals key names
to a user with WRITE but not READ permission (the 2023 advisory's shape, `v3_server.go:580`);
`requireAuthInfo` accepts a token-less call when auth is enabled only if `AuthInfoFromCtx` returns
`nil, nil`, which it does for a context without metadata.

## Note from the snapshot track (D22 receiver epochs, S8c, 2026-10-24)

`applySnapshot` moves the auth store to the snapshot's backend (`as.Recover`); a new trust-boundary
axiom, `auth.authStore.Recover.spec` (`Spec/go_etcd_io/etcd/server/v3/auth/authStore__Recover.lean`),
states it, in mode `.off` only, over an image whose auth buckets are the boot ones, taking
`authBeOn st oldbe` and giving `authBeOn st newbe` (S7c's backend halves). `NewAuthStore`'s
statement is unchanged: its reader resource `RD` stays valid across `Recover` in mode `.off`
because, with auth disabled, the permission checks return before reading the backend, so `RD`
names no backend's read rights (`notes/decisions.md`, "D22 receiver epochs, S8c carried out",
W2). If the auth track states the server in a mode where auth is on, `Recover` needs restating:
`RD` must then lend the current backend's read rights, and in-flight checks may still hold the old
backend's read transaction when the old backend closes (Go's `Close` waits; the backend's `Close`
spec takes all of `bOpen`).
