# Requirements on `go.etcd.io/etcd/server/v3/auth` (3d: the auth store, token providers)

## from 2b

Batch 2b (the member's gRPC watch handler) checks each watch create's read permission
(`serverWatchStream.isWatchPermitted`, `watch.go:239`), and the client's watch contract (1b's
`wireStep`) promises that a registered watch's principal **may read its range at a state the
cluster reached** (`σa.permits who [(.read, range)] []`, W0's `Model.lean`). What 2b's sketch
assumes, in plain terms:

1. **`AuthInfoFromCtx(ctx)`** (the auth store's, through `EtcdServer.AuthInfoFromCtx`, 2c), for a
   server-side context whose incoming metadata names the principal `who` (2b's `srvCtxPrin ctx who`,
   2a): `(nil, nil)` (no token), or an `*AuthInfo` whose `Username` is `who`'s user (`who = some u`)
   with its token's auth revision, or an error (an invalid token: `ErrInvalidAuthToken`, ...). No
   panic.
2. **`IsRangePermitted(info, key, rangeEnd)`**, `info` such an `*AuthInfo` or `&AuthInfo{}` (empty
   user, revision `0`), with a thread token (the store's reader lock and backend read
   transaction): `nil` **only if** some state `σa` the cluster reached (`etcdLb γ σa`, the member's
   applied auth state) has auth disabled, or has `info`'s user `u` with the root role or with read
   permission covering every key of `{key, rangeEnd}` (`AuthState.covers u .read`, `KeyRange.mem`:
   an empty `rangeEnd` the single key, `"\x00"` from the key on, as `rangePermCache` reads them);
   i.e. `σa.permits who [(.read, ⟨key, rangeEnd⟩)] []` for the `who` of item 1. Any error
   otherwise (`ErrUserEmpty`, `ErrAuthOldRevision`, `ErrPermissionDenied`). The reads of
   `IsAuthEnabled`, `Revision` and the user need not be atomic: each outcome is justified at one
   reached state (auth off at the first read; else the user read at the transaction's state).
   ```go
   return sws.ag.AuthStore().IsRangePermitted(authInfo, wcr.Key, wcr.RangeEnd)
   ```
3. `errors.Is(err, auth.ErrInvalidAuthToken)` etc. on the returned error: Perennial's `errors`
   (the package's error variables initialized, its `isPkgInit`).

Used by: `serverWatchStream.isWatchPermitted.spec`, hence `srvWireStep`'s registered-`Created`
case; snippet `examples/specreq/v3rpcwatch/protocol.go` (`ReqPermission`).

## from 2c

What the request path (2c) needs of the auth store (3d), beyond 2b's items (which 2c's `doSerialize`
and lease checks also use):

1. **`reqPrin ctx who`'s realization** (`ApiReq.lean`, = 2b's `srvCtxPrin`): `AuthInfoFromCtx(ctx)`
   (and `AuthInfoFromTLS` with `--client-cert-auth`) returns `nil`, an `AuthInfo` naming `who`'s user
   at some revision, or `ErrInvalidAuthToken`. Introductions: a context with no auth metadata
   (`none`: `s.ctx`, the internal requesters'), **`WithRoot(ctx)`** (`some root`: the lessor's
   expiry, `server.go:881`).
2. **`CheckPassword(name, pw)`** at the auth store's applied state: the checked revision and `nil`
   iff auth is enabled and `pw` is `name`'s password (`authStep`'s `authenticate`); else
   `ErrAuthNotEnabled`/`ErrAuthFailed`. **`GenTokenPrefix()`**, and the apply of an
   `InternalAuthenticateRequest` assigning the token: `tokenUser γ tok name` (W0's) for
   the token returned. **`Revision()`**: every change of the auth state bumps it, except
   `AuthEnable` (W0's model): two equal reads mean the auth state did not change in between unless
   auth was disabled at the first.
3. **`IsPutPermitted`**, **`IsAdminPermitted`**, **`IsAuthEnabled`**: as `IsRangePermitted` (2b's
   item 2), for the lease checks.
4. **`bcrypt`'s hash in `UserAdd`/`UserChangePassword`**: the apply stores the hash; W0's model keeps
   the password; the auth store's realization relates them (a trust-boundary spec of
   `bcrypt.GenerateFromPassword`/`CompareHashAndPassword`).

### from 2b, round 1: client-certificate authentication (to 3d, with 2a and W0)

`EtcdServer.AuthInfoFromCtx` (`etcdserver/v3_server.go:1206-1216`) falls back, when
`ClientCertAuthEnabled` and the context carries no token, to `AuthInfoFromTLS(ctx)`: the TLS peer
certificate's CN as the user (no auth revision check). Item 1 above (and 2b's `srvCtxPrin ctx who`)
said the result is `nil` or `who`'s user: false for a token-less stream over a client certificate
whose CN names a user while the client's `who` is `none`; the member then registers a watch that
`σa.permits none …` does not justify (and likewise for every unary request: W0's `ctxPrin`). Needed,
one of:
* the principal of a request (`srvCtxPrin`, 2a's `mdPrin`, W0's `ctxPrin`) is defined to include
  the TLS peer's CN when there is no token and client-certificate auth is on (2a's grpc boundary
  gives the peer's certificate; 3d's `AuthInfoFromTLS` reads it), so `who` is that user; or
* a configuration scope premise `ClientCertAuthEnabled = false` (2e's `NewServer`), a decision for
  the user.
Used by: `serverWatchStream.isWatchPermitted.spec`; every handler's principal (2a).

## from 2e

1. `EtcdServer.authBootRes cfg` (provisional slot of `NewServer`: the token provider's configuration,
   `AuthToken`, `TokenTTL`, `BcryptCost`; `NewTokenProvider`'s error is returned by `NewServer`).
2. `authStore.Close` once (`Cleanup`, through `srvClosers`).

## from 2d (round 1)

1. **The read slot** (2d's completeness F1): the auth store's reads (`IsRangePermitted`,
   `CheckTxnAuth`, `CheckPassword`, `Revision`) answer at a history point at or past `k` given 2d's
   `srvReadAt s γ k` (`ApiApply.lean`).
2. The simple-token waiter (`simple_token.go:240`, the closure `server.go:351-354`) receives
   `srvApplied` only from `start` on (`s.applyWait` is set there).


## from 3a

The apply layer (3a) owns the auth store's state on the apply thread (`Apply.authSt ast a`, exclusive;
`Apply.authOk ast γ`: tokens registered in W0's `γ`), and the request path reads it concurrently
(`Apply.authRead ast γ`). Its permission checks go through `Apply.permReads ast le A S` (each check
answered at a state of `S`): the apply thread's instance from `authSt` (`S` its one state, exact),
the request path's from `authRead` (`S` the reached auth states). Needed:
1. **`isOpPermitted`** (`IsRangePermitted`, `IsPutPermitted`, `IsDeleteRangePermitted`) is 3a's
   `opErr a u rev t rng`: `nil` with auth off; `ErrUserEmpty` at revision `0`; `ErrAuthOldRevision`
   below the store's revision; `ErrPermissionDenied` for a missing user; `nil` for a root user or a
   covered range (`AuthState.covers`); `ErrPermissionDenied` else. **`IsAdminPermitted`** is
   `adminErr` (no revision check); **`HasRole(u, r)`**.
2. **The administration methods** (`UserAdd` with the hash, `UserDelete`, `UserChangePassword`,
   `UserGrantRole`, `UserRevokeRole`, `UserGet`, `UserList`, `RoleAdd`, `RoleGrantPermission`,
   `RoleRevokePermission`, `RoleGet`, `RoleList`, `RoleDelete`, `AuthEnable`, `AuthDisable`,
   `IsAuthEnabled`, `Revision`): W0's `authStep` at the state (the hash in the password's place:
   W0's item 2 in `req/go_etcd_io_etcd_api_v3.md`), deterministic answers (lists in the store's key
   order).
3. **`Authenticate(ctx, name, pw)`** at the apply: `ErrAuthNotEnabled`, `ErrAuthFailed` (no such user,
   or one without a password), or a token registered in `γ` (`tokenUser γ tok name`); the state
   unchanged.
4. **`authRecordFits op`** (3a's provisional premise): the records an administration request
   writes fit bbolt's limits (`issues/etcd-auth-useradd-long-name-fatal.md`); the request path's
   size limits should give it, or it is a premise of the request path.
Used by: `applierV3backend.*` (auth methods), `authApplierV3.*`, the `check*` specs, `CheckTxnAuth.spec`.

## from 2c (round 1)

1. **`reqPrin ctx p tls`** (two principals, `ApiReq.lean`): `AuthInfoFromCtx` gives `p` (the token's
   user) with auth enabled and a token, else `tls` (`AuthInfoFromTLS` under `--client-cert-auth`) or
   `nil`; its realization is yours.
2. **`WithRoot(ctx)`'s spec** (the lessor's expiry, the health checks): from `reqPrin ctx p tls`, the
   result is `reqPrin ctx' (some root) tls` when auth is enabled at the call, the context itself
   otherwise (`auth/store.go:1175-1178`).
3. **The package variables**: `auth`'s error sentinels hold `srvErrVal e` (`errors/Api.lean`).

## from 2e, round 1

`authBootRes_intro` (provisional): at `AuthToken = "simple"` (etcd's default; this repository's
starters set it).


## from 3a (round 1)

5. `CheckTxnAuth.spec` now rests on `authStoreAt`, `authLb`, `checkPost` (thanks). For one state for
   all of a request's passing checks, `checkPost`'s pass should also report the store's revision
   against the info's (`isOpPermitted` passes only at `as.Revision() ≤ rev`: with a token's
   revision, every passing check sees the same users and roles).
