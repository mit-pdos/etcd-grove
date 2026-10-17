# etcd#22560: the Go tests and probes of the verification

The files are laid out as in etcd's repository. Each one is new, so copy it into a checkout of the
revision and run it there. The report is `../etcd-22560.md`. The `*.log` files hold the outputs
below, run on 2026-10-16/17 with `GOTOOLCHAIN=go1.27.1`.

Revisions:
- **PR head**: `7a87a72d1`, etcd-io/etcd#22560, local branch `pr-etcd-22560` in `~/etcd`.
- **Upstream base**: `f061acd09`, upstream `main`, the PR's merge base.
- **Fork branch**: `mit-pdos/etcd-grove` branch `pr-etcd-22560-goose-lean` (`69a986114`), the fork's
  `goose-lean` (`09669450f`) plus the PR's non-test changes. It applied cleanly. This is the code
  that was verified.

| File | What it shows | At PR head | At upstream base |
|---|---|---|---|
| `server/auth/renew_token_finding_test.go`: `TestRenewTokenResurrectsExpiredSimpleToken` | A simple token that the TTL keeper has expired (`AuthInfoFromCtx` says `ErrInvalidAuthToken`) is renewed by `RenewToken`, and then authenticates again. | PASS (the behavior is as described) | does not build (`RenewToken` is new) |
| same file: `TestRenewTokenJWTIgnoresExpiry` | A JWT past its `exp` (ttl 1s, after 2s) is renewed. `renew` parses with `jwt.WithoutClaimsValidation()`. | PASS | does not build |
| same file: `TestRenewTokenJWTSurvivesPasswordChange` | A JWT issued before a password change fails every permission check (`ErrAuthOldRevision`: the auth revision is how etcd revokes JWTs). `RenewToken` reissues it at the current revision, and the new token passes `IsPutPermitted`. | PASS | does not build |
| same file: `TestRenewTokenJWTDeletedUserRecreated` | A deleted user's JWT is refused (`ErrUserNotFound`), but once a user of the same name is added again, the old token is renewed for the new user. | PASS | does not build |
| same file: `TestRenewTokenInvalidateUserRacesDisable` (run with `-race`) | `RenewToken` calls `tokenProvider.invalidateUser` on the request goroutine. `invalidateUser` reads `tokenSimple.simpleTokenKeeper` without `simpleTokensMu`, and `disable` (`AuthDisable`, the apply goroutine) writes it under the mutex. A backend whose `UnsafeGetUser` reports the user missing after a delay stands for the window in which `UserDelete`'s apply has deleted the user but not yet called `invalidateUser`. | FAIL: `WARNING: DATA RACE`, read in `invalidateUser` from `RenewToken`, previous write in `disable` from `AuthDisable` (`race.log`) | does not build |
| `server/auth/revive_reviewer_test.go`: `TestReviewerRenewRevivesExpiredSimpleTokenForAllAPIs` (the reviewer subagent's) | After the TTL, `AuthInfoFromCtx` rejects the simple token. One `RenewToken` call later, it accepts the original token again on every API (the token is back in the live table). | PASS, under `-race` (`reviewer.log`) | does not build |
| `tests/integration/v3lock_auth_renew_test.go`: `TestV3LockUnlockRejectsRevokedAndExpiredJWT` | End to end, on a 1-member cluster with JWT auth (ttl 2s): user `alice` (read-write on `[foo, fop)`), whose token leaked, gets its password changed. The KV API rejects the token (`revision of auth store is old`), but `Lock.Unlock` with it deletes `foo1`. Three seconds later, with the token both revoked and expired, `Lock.Unlock` deletes `foo2`. These are fresh requests, not calls that were blocked when the token went stale. The test asserts that both are refused. | FAIL: both `Unlock`s return `<nil>` and both keys are gone (`integration.log`) | PASS: `revision of auth store is old`, then `invalid auth token` |
| `tests/integration/v3lock_auth_revision_rewatch_test.go`: `TestV3LockWaiterRewatchAfterAuthRevisionBump` | A `Lock` waiter C, holding a JWT, waits behind B and A. The auth revision moves (`RoleAdd`). B's lease is then revoked, so C's `waitDeletes` has to watch A's key. The watch wrapper renews only when `AuthInfoFromCtx` fails, and it does not fail for a stale-revision JWT, so the new watch is refused and C's `Lock` fails. The test asserts that C gets the lock after A unlocks. | FAIL: `rpc error: code = InvalidArgument desc = etcdserver: revision of auth store is old` (`rewatch.log`) | FAIL: `etcdserver: revision of auth store is old`. Same outcome, but here the KV calls fail first. |

`pr-own-tests.log`: the PR's own integration tests (`TestV3ElectionCampaignAuthTokenExpiration`,
`TestV3ElectionCampaignAuthRevisionUpdate`, `TestV3LockLockAuthTokenExpiration`) pass at the PR
head. Its unit tests (`TestRenewToken*` in `server/auth/store_test.go`) pass at the head, and the
package's tests pass in the fork branch (`go test ./auth/`).

Commands, with `<checkout>` an etcd checkout at the revision:

```
cp server/auth/renew_token_finding_test.go <checkout>/server/auth/
(cd <checkout>/server && go test -race ./auth/ -run 'TestRenewToken(Resurrects|JWTIgnores|JWTSurvives|JWTDeleted|InvalidateUser)' -v)
cp server/auth/revive_reviewer_test.go <checkout>/server/auth/
(cd <checkout>/server && go test -race ./auth/ -run TestReviewerRenewRevivesExpiredSimpleTokenForAllAPIs -v)

cp tests/integration/v3lock_auth_renew_test.go tests/integration/v3lock_auth_revision_rewatch_test.go <checkout>/tests/integration/
(cd <checkout>/tests && go test ./integration/ -run 'TestV3LockUnlockRejectsRevokedAndExpiredJWT|TestV3LockWaiterRewatchAfterAuthRevisionBump' -v)
```

The unit tests use the package's own test helpers (`testJWTOpts`, `newBackendMock`,
`dummyIndexWaiter`, `enableAuthAndCreateRoot`, `encodePassword`). The integration tests use
`authSetupRoot` and `authSetupUsers` from `tests/integration/v3_auth_test.go`.
