---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#14616 issue closed: the lease half (keys under leases never expire with a verify-only JWT key); closed as stale in 2023, not fixed
  - etcd-io/etcd#22493 pr open: `WithRootInternal` gives in-process requests a root identity without a token on the JWT path, which fixes both halves (its `TestWithRootInternalVerifyOnlyJWT`)
---

# auth: with a verify-only JWT key, expired leases are never revoked (and the health range check runs unauthenticated)

- **Status**: bug (a wrong result: an expired lease and its keys are never removed; the health and
  readiness range checks run with no user). It needs a configuration etcd accepts and documents: a JWT token
  provider given only a public key, `--auth-token=jwt,pub-key=...,sign-method=...` with no
  `priv-key`, which `newTokenProviderJWT` sets up as verify-only.
- **Where**: at the pinned revision (`etc/goose.py`, etcd `09669450f`; the same in upstream
  `f061acd09`), the server's in-process requests authenticate as root with
  `authStore.WithRoot` (`server/auth/store.go:1159`), which signs a root token with the provider's
  `assign`. The verify-only JWT provider refuses to sign (`tokenJWT.assign`,
  `server/auth/jwt.go:94-95`, `ErrVerifyOnly`). `WithRoot` then logs "failed to assign token for
  lease revoking" (`store.go:1184`) and returns the context with no token. The callers are:
  - `EtcdServer.revokeExpiredLeases` (`server/etcdserver/server.go:880`), whose `LeaseRevoke`
    then runs with no user;
  - `checkAPI` (`server/etcdserver/api/etcdhttp/health.go:222`, `/health`) and `readCheck`
    (`health.go:434`, the `/readyz` and `/livez` range checks).
- **What happens**: `AuthInfoFromCtx` finds no token, so the request goes out with an empty user
  name. The apply side refuses it with `ErrUserEmpty` ("auth: user name is empty"):
  - The leader logs "failed to revoke lease" for every expired lease, at each retry. The lease
    and its keys stay until auth is disabled.
  - The health checks' range runs the same way, with no user, so it should fail with
    `ErrUserEmpty` too: `/health` would report `false` (`RANGE ERROR:...`). This half is read
    from the code and is not reproduced separately.
  Reproduction: `notes/pr-verify/etcd-22493/tests/integration/v3_auth_verify_only_lease_test.go`
  on branch `pr-verify/etcd-22493`. It is a single-member cluster with a verify-only JWT
  provider. A key is put under a 2s lease, then auth is enabled. The test fails on upstream
  `f061acd09`: the key is still there 10s later, and the log shows "token signing attempted with
  verify-only key" followed by "failed to revoke lease ... user name is empty". It passes at the
  PR head (`notes/pr-verify/etcd-22493/integ-upstream-base.log`, `integ-upstream-pr.log`). The
  unit test `notes/pr-verify/etcd-22493/server/auth/verify_only_withroot_test.go` shows the
  mechanism: `WithRoot` returns the context unchanged, `AuthInfoFromCtx` returns no info, and the
  permission check returns `ErrUserEmpty`.
- **Expected**: an expired lease is revoked whatever the token provider; the server's own
  maintenance requests do not depend on being able to sign client tokens. A verify-only provider
  is meant for setups where an external issuer signs the tokens (etcd-io/etcd#14616's use case:
  a proxy with a certificate manager).
- **How the proof handles it**: `WithRoot` and `revokeExpiredLeases` are names-only, at the
  trust boundary (`Proof/go_etcd_io/etcd/server/v3/auth/authStore__WithRoot.lean`,
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__revokeExpiredLeases.lean`). Their
  specs say only that they return, so nothing verified depends on lease revocation succeeding.
  On `pr-verify/etcd-22493`, `WithRootInternal`'s spec
  (`Spec/go_etcd_io/etcd/server/v3/auth/WithRootInternal.lean`) states that its fast path, taken
  only for the JWT provider, carries a root value of the store. `AuthInfoFromCtx`'s spec turns
  that value into root, whatever the provider can sign.
- **Possible fixes**: etcd-io/etcd#22493 (identify in-process requests by a context value rather
  than a signed token, for the JWT provider); or make `WithRoot` itself not depend on `assign`
  for in-process use; or refuse a verify-only JWT configuration at startup (mitake's suggestion
  on etcd-io/etcd#14616), which would leave that setup unsupported.
- **Found**: 2026-10-17, verifying etcd-io/etcd#22493 (`pr-verify/etcd-22493`), from the PR's
  description and its `TestWithRootInternalVerifyOnlyJWT`; reproduced end to end with the
  integration test above.
