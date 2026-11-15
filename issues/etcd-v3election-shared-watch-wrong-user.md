---
upstream: known
checked: 2026-11-14
links:
  - etcd-io/etcd#17502 issue closed: this bug (closed by the stale bot, not fixed)
  - etcd-io/etcd#14850 issue closed: same symptom (spurious permission denied from Election)
  - etcd-io/etcd#17623 issue closed: v3lock likely the same (comment on #17502)
  - etcd-io/etcd#17532 pr merged: workaround example (election through the client SDK)
blocks-proof: no
---

# v3election/v3lock: with auth on, a waiting Campaign or Lock is authorized as another user

With authentication enabled, when two users call the Election service's `Campaign` (or the Lock
service's `Lock`) at the same time, and both calls have to wait, the second user's call is
authorized as the first user. It fails with `permission denied` although the user holds the
permission. It succeeds when the other user is idle.

**Expected:** each request the Election and Lock services make on a caller's behalf should be
authorized as that caller, as for every other etcd RPC
([RBAC guide](https://etcd.io/docs/v3.6/op-guide/authentication/rbac/)).

**Impact:** clusters with auth enabled whose clients use the gRPC Election/Lock services (the
gRPC gateway, or non-Go clients without a concurrency SDK), with several users. Any two waiting
`Campaign`/`Lock`/`Observe` calls of different users interfere. The usual result is a spurious
denial. If the first user may read a range that the second may not, the second user's watch is
authorized as the first. Releases 3.4 to main.

**Reproduction:** `TestIssue17502ElectionWrongIdentity` in
[`issues/etcd-v3election-shared-watch-wrong-user/issue17502_test.go`](etcd-v3election-shared-watch-wrong-user/issue17502_test.go),
copied into `server/embed` at etcd-io/etcd@f061acd0902d489041448cdd19d71a345d27b9f5 (2026-10-08), go1.27.1:

```
$ go test ./embed -run TestIssue17502ElectionWrongIdentity
    issue17502_test.go:100: user2's waiting Campaign failed instead of waiting: rpc error: code = Unknown desc = rpc error: code = PermissionDenied desc = etcdserver: permission denied
--- FAIL: TestIssue17502ElectionWrongIdentity (1.88s)
```

**Cause:** the services run `client/v3/concurrency` over the in-process client (`v3client.New`). Its
watcher shares one watch stream among watches whose contexts have the same outgoing metadata
(`streamKeyFromCtx`, `client/v3/watch.go`). A server request context has only incoming metadata, so
all users' watches share one stream, opened with the first watch's context. The adapter
(`newPipeStream`, `server/proxy/grpcproxy/adapter/chan_stream.go`) gives that context to the watch
server, which authorizes every create on the stream with `AuthInfoFromCtx(stream.Context())`: the
first caller's token or TLS identity.

## Proof

no: the Lock/Election handlers are proved over a client contract that names no principal
(`v3lock.lockClientOk`), and the in-process client and adapter are not translated. No result
states the caller's identity for these services' watches. The closed auth theorems do not use
them (`etcd_auth_safe`, `etcd_auth3_safe` never call Lock or Election).

## Fix

**Branch**: none yet.
**Base**: etcd-io/etcd@f061acd0902d489041448cdd19d71a345d27b9f5

A candidate: in `v3client`'s `watchWrapper.Watch`, carry the request's incoming auth metadata
(token) into the outgoing context, so that the watcher keys streams per user and opens each with the
user's context. Or open a stream per in-process watch.

## Notes

The maintainers called it a design issue and preferred documenting it (2024-03); the docs change
was not made before the stale bot closed the issue.

Rerun 2026-11-14 at this repository's etcd pin (the fork `upamanyus/etcd` at `2eaeb872b`, copied as
`server/embed/zz_issue17502_test.go`, `GOWORK=off`, go1.27.1): the same failure,
`user2's waiting Campaign failed instead of waiting: rpc error: code = Unknown desc = rpc error:
code = PermissionDenied desc = etcdserver: permission denied` (`--- FAIL ... (1.99s)`). Found by the
bug triage of 2026-11 (branch `bug-triage/auth-2026-11`, `notes/bug-triage/etcd-17502.md`, not on
`lean`). The claim this repository made that the services' requests run as the caller's principal
(`notes/auth-matrix.md`, the `v3election`/`v3lock` `Defs.lean` docstrings) is corrected.
