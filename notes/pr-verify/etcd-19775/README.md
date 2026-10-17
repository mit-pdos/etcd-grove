# etcd-io/etcd#19775: tests and logs

Revisions:
- **fork**: `mit-pdos/etcd-grove` branch `pr-etcd-19775-goose-lean` (`534e22e6f`): `goose-lean` `09669450f` plus the PR, plus a rewrite of the slice for Goose.
- **PR head**: `cad46b8e7`. **PR base**: `638b41017`, the merge base with upstream `main`.
- **main**: upstream `main` `b25719d10`. It has etcd-io/etcd#21910's `strings.TrimPrefix`.

Toolchains: `GOTOOLCHAIN=go1.27.1` for the fork and main, and `GOTOOLCHAIN=go1.24.13` for the PR head and base.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `server/auth/bearer_scheme_test.go` | Exactly one leading `"Bearer "` is stripped, case-sensitively, under both metadata keys (`token`, `authorization`). `bearer `, `BEARER `, two spaces, a tab and `Bearer Bearer ` are rejected. The PR and #21910 behave the same. | fork, PR head, main | `cp server/auth/bearer_scheme_test.go <checkout>/server/auth/ && cd <checkout>/server/auth && go test -run TestBearerSchemeForms -v .` |
| `bearer-fork.log`, `bearer-pr-head.log`, `bearer-upstream-main.log` | That test, with the PR's `TestAuthInfoFromCtx`, passes on each revision. | as named | as above, `-run 'TestBearerSchemeForms$\|TestAuthInfoFromCtx$'` |
| `server/auth/ws_bearer_review_test.go` (written by the reviewer) | The path of etcd-io/etcd#19752. A websocket client sends `Sec-WebSocket-Protocol: Bearer, <tok>`. `wsproxy` turns it into `Authorization: Bearer <tok>`, which grpc-gateway forwards as `authorization` metadata, and `AuthInfoFromCtx` then authenticates the user. | fork, PR head (pass); PR base (fails, `invalid auth token`) | `cp server/auth/ws_bearer_review_test.go <checkout>/server/auth/ && cd <checkout>/server/auth && go test -run TestReviewWebsocketBearer -v .` |
| `ws-fork.log`, `ws-pr-head.log`, `ws-pr-base.log` | The output of that test on each revision. | as named | as above |
