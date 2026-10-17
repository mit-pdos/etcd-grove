# Files for the etcd-io/etcd#22493 verification

What each file here shows, the revision it runs against and the command. The report is
`notes/pr-verify/etcd-22493.md`. Revisions:

- **PR head**: `fb1d045e88174ff8d6ccfa3b219d9daad2293022` (`git fetch https://github.com/etcd-io/etcd pull/22493/head`).
- **Upstream base**: `f061acd0902d489041448cdd19d71a345d27b9f5`, the upstream commit the fork's
  `goose-lean` is based on. The PR's own merge base, `88235ecd0`, is 7 commits later, and none
  of those 7 touches the PR's files.
- **Fork branch**: `mit-pdos/etcd-grove` branch `pr-etcd-22493-goose-lean`
  (`419e2eef3`). It is the fork's `goose-lean` (`09669450f`) plus the PR's non-test diff.

| File | Shows | Runs against | Command |
|---|---|---|---|
| `tests/integration/v3_auth_verify_only_lease_test.go` | The bug in the existing code that the PR fixes (`issues/etcd-auth-verify-only-jwt-internal-root.md`, etcd-io/etcd#14616). With a verify-only JWT provider, an expired lease is never revoked and its key stays. | Fails on the upstream base. Passes at the PR head. | `cp v3_auth_verify_only_lease_test.go <checkout>/tests/integration/ && cd <checkout>/tests && go test ./integration/ -run 'TestV3AuthLeaseExpiryVerifyOnlyJWT$' -v` |
| `integ-upstream-base.log`, `integ-upstream-pr.log` | The output of that test, filtered to the test lines and the server's revoke errors. On the base it fails, with "token signing attempted with verify-only key" and then "failed to revoke lease ... user name is empty". At the PR head it passes. | The upstream base; the PR head. | As above. |
| `server/auth/verify_only_withroot_test.go` | The mechanism of the same bug. `WithRoot` on a verify-only JWT store returns the context unchanged, `AuthInfoFromCtx` finds no user, and the permission checks return `ErrUserEmpty`. `WithRoot` itself is unchanged by the PR, so the test passes on both revisions: it documents the behaviour and does not detect the fix. | The upstream base and the PR head (passes on both). | `cp verify_only_withroot_test.go <checkout>/server/auth/ && cd <checkout>/server && go test ./auth/ -run TestWithRootVerifyOnlyJWTIsUnauthenticated -v` |
| `pr-own-tests.log` | The PR's own tests pass. These are the six `TestWithRootInternal*` unit tests in `server/auth`, run on the fork branch with the PR's `store_test.go`, and the integration tests `TestV3AuthWithRootInternalRPCIsolationJWT` and `TestV3AuthWithLeaseRevokeWithRoot{,JWT}`, run at the PR head. | The fork branch; the PR head. | `go test ./auth/ -run WithRootInternal -v` (in `server/`); `go test ./integration/ -run 'TestV3AuthWithRootInternalRPCIsolationJWT\|TestV3AuthWithLeaseRevokeWithRoot' -v` (in `tests/`) |
| `reviewer/server/auth/withrootinternal_precedence_test.go` | The reviewer's test of a behaviour difference (report, finding 2). With `WithRoot`, a context derived later with `metadata.NewIncomingContext(ctx, userToken)` runs as that user. With the JWT fast path, the root value wins over any later token. | Passes at the PR head. It does not compile on the base, which has no `WithRootInternal`. | `cp withrootinternal_precedence_test.go <checkout>/server/auth/ && cd <checkout>/server && go test ./auth/ -run TestWithRootInternalNotDowngradedByLaterToken -v` |

All commands use `GOTOOLCHAIN=go1.27.1`.
