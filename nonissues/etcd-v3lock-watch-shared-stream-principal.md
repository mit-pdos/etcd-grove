---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# v3lock/v3election: with auth on, every caller's watch is checked as the first caller's user

The lock and election services (`v3lock`, `v3election`, built on the in-process client
`v3client.New`, `embed/serve.go:148-150`) run each RPC's client operations under the RPC's context.
A contended `Lock` (`concurrency.Mutex.Lock`, `waitDeletes`) and every `Observe` create a watch
through the in-process client, whose watcher shares one stream among watches whose contexts have the
same **outgoing** metadata (`streamKeyFromCtx`, `client/v3/watch.go`); the RPC contexts carry only
**incoming** metadata, so every such watch joins the stream keyed `""`, opened with the first
caller's context (`valCtx` keeps its values). The adapter's pipe passes that context to the member's
watch handler (`proxy/grpcproxy/adapter/chan_stream.go`, `newPipeStream`), and `isWatchPermitted`
reads the principal from its incoming metadata (`authStore.AuthInfoFromCtx`): the first caller's
token. So user B's watch, while user A's waiter keeps the stream open, is checked as A: refused if A
may not read B's prefix (B's `Lock` fails with permission denied), admitted if A may although B may
not; and once A's token expires every later watch on the stream is refused.

**Why not an issue:** found by code reading (the specs-only branch's review of batch 2b,
`notes/specs-only/reviews/2b-completeness-1.md`), not run: no test yet. Move to `issues/` if the
recipe below fails.

**Test recipe** (`tests/integration`, auth on): root enables auth; users `a` and `b` with roles
granting read-write on disjoint prefixes `/a/` and `/b/` only; through the member's gRPC endpoint
with `a`'s token, `v3lockpb.Lock(name "/a/l")` twice (the second blocks: its `waitDeletes` watch on
`/a/` opens the in-process stream with `a`'s context); then with `b`'s token, `Lock("/b/l")` twice
(the second waits on a watch on `/b/`). Expected: `b`'s second `Lock` waits and is granted after
`b`'s first `Unlock`; suspected: it fails with `etcdserver: permission denied` (the watch on `/b/`
checked as `a`). A variant with `a` holding read on everything shows the admission side.

## Proof

no: the watch handler's spec checks the stream's principal (`srvWatchStreamAt st γ who g`), which
for the in-process stream is the first opener's; and the in-process client is outside the handler's
stream contract (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/ApiWatch.lean`'s header). It
matters to a per-call principal of v3lock/v3election (1d, 2e). Related:
`nonissues/etcd-watch-stream-key-collision.md` (the same sharing through metadata that prints alike).
