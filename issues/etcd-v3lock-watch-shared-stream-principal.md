---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---
# v3lock/v3election: with auth enabled, a waiting `Lock` fails with permission denied while another user is waiting for a lock

With auth enabled, the lock and election services check every caller's watch as the user whose
watch opened the services' shared watch stream first. While user `a` waits for a lock under `/a/`,
user `b`, allowed only `/b/`, gets `permission denied` from a `Lock` that should wait for `b`'s own
lock under `/b/`; with `a` not waiting, the same `Lock` waits and is granted. Conversely, a user
can be let watch a prefix it may not read, and once the first user's token expires, every later
wait on the stream fails.

**Expected:** a `Lock` (or `Campaign`, `Observe`) should be checked against the caller's own
permissions, as every other request to the services is.

**Impact:** clusters with auth enabled (not the default) where two users use the lock or election
service (`etcdctl lock`, `etcdctl elect`, the gRPC gateway's `/v3/lock`) at the same time with
different permissions; a contended `Lock` fails, or a watch is admitted on a prefix the user may not
read. Every release with the services.

**Reproduction:** `TestV3LockAuthWaiterOtherUser` in
[`issues/etcd-v3lock-watch-shared-stream-principal/v3lock_auth_shared_watch_test.go`](etcd-v3lock-watch-shared-stream-principal/v3lock_auth_shared_watch_test.go),
copied into `tests/integration` at etcd-io/etcd@d622ec57cf46 (2026-11-06), go1.27.3 (also fails at
the verified fork's a4d2bb1720b9; without `a`'s waiting `Lock` the test passes):

```
$ go test ./integration -run '^TestV3LockAuthWaiterOtherUser$' -count=1
--- FAIL: TestV3LockAuthWaiterOtherUser (0.78s)
    v3lock_auth_shared_watch_test.go:78: b's second Lock returned before b's first Unlock: rpc error: code = Unknown desc = rpc error: code = PermissionDenied desc = etcdserver: permission denied
FAIL
```

**Cause:** the services run on the in-process client (`v3client.New`) with each RPC's context. A
contended `Lock` waits with a watch ([`waitDeletes`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/client/v3/concurrency/key.go#L49)),
and the client's watcher shares one stream among watches whose contexts have the same outgoing
metadata ([`streamKeyFromCtx`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/client/v3/watch.go#L1086-L1091));
the RPC contexts carry the token as incoming metadata only, so every such watch joins one stream,
opened with the first caller's context
([`newWatcherGRPCStream`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/client/v3/watch.go#L281-L282)
keeps its values). The in-process pipe hands that context to the member's watch handler
([`newPipeStream`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/server/proxy/grpcproxy/adapter/chan_stream.go#L142-L154)),
whose [`isWatchPermitted`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/server/etcdserver/api/v3rpc/watch.go#L237-L247)
reads the user from it: the first caller's token.

## Proof

no: the watch handler's spec checks the stream's principal (`srvWatchStreamAt st γ who g`), which
for the in-process stream is the first opener's; and the in-process client is outside the handler's
stream contract (`SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/ApiWatch.lean`'s header). It
matters to a per-call principal of v3lock/v3election (1d, 2e).

## Fix

Not written: key the in-process watcher's streams by the caller's token (for instance, copy the
RPC's incoming auth metadata to the outgoing metadata of the context the services pass to the
client), so that each user's watches go on a stream opened with that user's context.

## Notes

Found by code reading (the specs-only branch's review of batch 2b). Related:
[`etcd-watch-stream-key-collision`](../nonissues/etcd-watch-stream-key-collision.md) (the same
sharing through metadata that prints alike). RBAC is a secondary control in etcd's threat model;
the admission side (a user let watch a prefix it may not read, through `Observe` or `Lock`) was not
tested.
