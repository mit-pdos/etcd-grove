---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#17502 issue closed: this bug (maintainer: "a design issue", doc-only resolution proposed; closed by the stale bot)
  - etcd-io/etcd#17532 pr merged: an election test with auth over the Go client SDK, the maintainer's suggested pattern (not a fix)
  - etcd-io/etcd#17623 issue closed: related, not this bug (the same in-process client keeps the caller's token, which expires during a long Campaign)
  - etcd-io/etcd#22270 pr closed: documentation of the v3election/v3lock auth caveats (unmerged)
  - etcd-io/etcd#19296 issue closed: the same stream sharing in the gRPC proxy's watch (token passed as a context value, not outgoing metadata); there the first user's expired token refuses later users' watches (closed by the stale bot)
  - etcd-io/etcd#19033 pr open: the proxy-side fix (the token as outgoing metadata)
---

# v3election/v3lock: internal watches of different users share one watch stream and are authorized as its first user

- **Status**: bug (an authorization decision made with another user's credentials). Upstream
  treats it as a known design limitation of the gRPC `v3election`/`v3lock` services. The visible
  effect is a spurious `permission denied`. The opposite direction, a watch allowed by another
  user's permissions, is possible in principle. In `Campaign`/`Lock` each watch follows a `Get` of
  the same range under the caller's own token, which limits it.
- **Where** (etcd pin `107edf7e4`): `server/etcdserver/api/v3client/v3client.go:30-40`
  (`v3client.New` builds the watcher on `adapter.WatchServerToWatchClient`);
  `client/v3/watch.go:1090-1095` (`streamKeyFromCtx`: streams keyed on the *outgoing* metadata);
  `client/v3/watch.go:281-301` (`newWatcherGRPCStream`: the stream keeps the first watcher's
  context); `server/proxy/grpcproxy/adapter/chan_stream.go:142-154` (the server stream's context
  is the client stream's); `server/etcdserver/api/v3rpc/watch.go:237-247` (`isWatchPermitted`:
  every watch on a stream is checked with `AuthInfoFromCtx(stream.Context())`, which reads the
  *incoming* metadata).
- **What happens**: a `v3election.Campaign` or `v3lock.Lock` handler's context carries the
  caller's token as incoming metadata and has no outgoing metadata. Every internal watch, whatever
  the user, gets the stream key `""` and joins the one in-process stream, whose server-side
  context is that of the user who opened it. While user1's `Campaign` waits (its watch holds the
  stream open), user2's `Campaign` watch is authorized as user1. The reporter's Docker
  reproduction with basic auth is in #17502 (`etcd-issue-17502.zip`). No reproduction of ours.
- **Expected**: each internal request is authorized as the user whose RPC caused it, as the
  unary internal calls are (`Range`/`Txn` through the adapter keep the caller's context).
- **How the proof handles it**: outside the verified code (O-path). `v3election`, `v3lock`,
  `v3client` and the adapter are not translated. The verified client watch is proved over a stub
  on a gRPC connection (`Spec/go_etcd_io/etcd/api/v3/etcdserverpb/watchClient__Watch.lean`), where
  each client has its own stream context. Identity is also not in the specs:
  `streamKeyFromCtx.spec` returns some string, and `isWatchPermitted.spec` and
  `AuthInfoFromCtx.spec` return "some auth info / some error". The proposal
  `inproc-client-auth-identity` is in `notes/bug-triage/etcd-17502.md`.
- **Possible fixes**: key the in-process client's watch streams on the caller's incoming token,
  or have `v3election`/`v3lock` copy the caller's token into outgoing metadata (as the
  maintainer suggests, `client/v3/watch.go`'s `WithRequireLeader` pattern), so that the streams
  are per user; or document the services as unsupported with auth (#22270).
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#17502.
