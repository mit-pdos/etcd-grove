---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# v3rpc: an administrator's `Compact` racing `AuthEnable` can be refused for the wrong user

If `AuthEnable` is applied while a root user's `Compact` (or an `authMaintenanceServer` RPC:
`Snapshot`, `Hash`, `HashKV`, `Defragment`, ...) is being checked, the call can be refused with
`ErrUserEmpty`, although it carried a valid root token. Under `--client-cert-auth`, it can also be
refused with `ErrUserNotFound` or `ErrPermissionDenied` for the certificate's user, not the token's.

**Why not an issue:** found by code reading during the specs' re-review (2026-11-09, R-A6 N3), with
no test. The refusal is definite, but nothing is applied, and a retry after the enable succeeds. The
window is one auth-flag flip between two reads in one RPC.

**How:** `AuthAdmin.isPermitted` calls `AuthInfoFromCtx(ctx)` and then
`IsAdminPermitted(authInfo)` (`server/etcdserver/api/v3rpc/auth.go:182-189`), and each reads the
auth flag on its own (`server/auth/store.go:1072-1074`, `916-918`).
- With auth off at the first read, `AuthInfoFromCtx` returns no user from the token.
  `EtcdServer.AuthInfoFromCtx` then falls back to the TLS certificate's name
  (`server/etcdserver/v3_server.go:1206-1215`).
- With auth on at the second read, `IsAdminPermitted` checks that empty user (`ErrUserEmpty`) or the
  certificate's user.

## Proof

No: the specs state the behavior. W0's `State.adminDenied` (`api/v3/Model.lean`), which
`V3rpc.adminDenied` abbreviates, admits a denial of the principal the check read. That is the
request's own, or, when the flag was read off at some auth table, no user or any certificate user.
`AuthAdmin.isPermitted.spec` returns that denial, and `kvServer.Compact` fires it as the model's
compact answer.

## Notes

A fix: read the flag once (take the `AuthInfo` and the admin check under one auth-store read), or
re-run `AuthInfoFromCtx` when `IsAdminPermitted` sees auth on but got no user.
