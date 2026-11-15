---
upstream: none
checked: 2026-11-14
links: []
blocks-proof: no
---

# auth: a request with a valid token can fail with "user name is empty" while auth is being disabled

`LeaseGrant`, `LeaseRevoke`, `MemberList`, `Status` and `Alarm` GET can return
`etcdserver: user name is empty` to a client that sent a valid token, when an `AuthDisable`
commits during the request. The authenticated-user check reads the enabled flag twice:
`requireAuthInfo` reads it first (`server/etcdserver/v3_server.go:1278`, and the gRPC layer's copy
`server/etcdserver/api/v3rpc/auth.go:192`), then `authStore.AuthInfoFromCtx` reads it again and
returns no auth info and no error once it is off (`server/auth/store.go:1073-1075`); the first read
still said on, so the check answers `ErrUserEmpty`. The request fits neither order with the
disable: before it, the token passes; after it, no token is needed. The lease checks
(`checkLeaseRenew`, `checkLeaseTimeToLive`, `checkLeaseLeases`, `v3_server.go:576-586`) have the same
shape. The admin check does not: `IsAdminPermitted(nil)` reads the flag again and passes. Fork pin
`2eaeb872b`.

**Why not an issue:** no test; found by code reading (the auth-guard-completeness Scope,
`notes/auth-guard-scope.md`, 2026-11-14). The refusal is transient and fails closed: a retry after the
disable succeeds. etcd makes no promise about requests that race an `AuthDisable`.

## Proof

no: the guards' specs allow every refusal today. A converse ("a request with an accepted token is
not refused") must name this case as an allowed refusal reason: auth disabled at a recorded state
no older than the request's lower bound (`notes/auth-guard-scope.md`, section 2).
