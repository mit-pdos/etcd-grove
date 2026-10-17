# etcd-io/etcd#21909: tests and logs

Revisions: **PR head** `6f565cae6b96067b6cb47b1c0aafd387e54f28ba` (upstream, detached checkout);
**upstream base** `12caed621` (the PR's merge base with `main`); **fork branch**
`mit-pdos/etcd-grove` branch `pr-etcd-21909-goose-lean` (`8cc284932`: the fork's `goose-lean`
`09669450f` plus the PR, plus the `keyFunc` rewrite). Toolchain: `GOTOOLCHAIN=go1.26.5` upstream,
`go1.27.1` on the fork.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `client/v3/client_update_token_test.go` | `TestUpdateAuthTokenRacesWithRetry`: `UpdateAuthToken`'s write of `c.Token` races with the retry interceptor's read (`shouldRefreshToken`, retry_interceptor.go:153); `TestUpdateAuthTokenNoCredentialsPanics`: a client built without a token or user/password panics (nil `authTokenBundle`); `TestUpdateAuthTokenDisablesPasswordRefresh`: on a user/password client, it turns off re-authentication | PR head | `cp client_update_token_test.go <checkout>/client/v3/ && cd <checkout>/client/v3 && go test -race -run TestUpdateAuthToken .` |
| `client-update-token-pr.log` | the race report, and the three results (the race test fails under `-race`; the other two pass, i.e. the behaviors are confirmed) | PR head | as above |
| `tests/common/auth_jwt_recreated_user_test.go` | `TestAuthJWTOnlyRecreatedUserOldToken`: with a verify-only provider, a token (current revision claim, no `exp`) of a user that is deleted and re-created with the same name keeps working and carries the new user's roles (root). Passes at the PR head; fails at the base, where the token is rejected (`revision of auth store is old`) | PR head and upstream base | `cp auth_jwt_recreated_user_test.go <checkout>/tests/common/ && cd <checkout>/tests && go test -tags integration ./common/ -run TestAuthJWTOnlyRecreatedUserOldToken` |
| `recreated-user-pr.log` | PASS at the PR head | PR head | as above |
| `recreated-user-base.log` | FAIL at the base: `etcdserver: revision of auth store is old` | upstream base | as above |
| `pr-own-tests-fork.log` | the PR's own tests (`TestAuthJWTOnly*`, `server/auth` JWT tests) pass on the fork branch | fork branch | `cd tests && go test -tags integration ./common/ -run TestAuthJWTOnly -v`; `cd server && go test ./auth/ -run JWT -v` |
