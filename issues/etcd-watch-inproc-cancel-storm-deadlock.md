---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#20716 issue closed: this bug (v3election Campaign storm; closed by the stale bot, not fixed)
  - etcd-io/etcd#18879 issue open: same root cause (many in-process watches dropped at once)
  - etcd-io/etcd#21064 pr closed: reproduction test (tests/integration/clientv3/watch)
  - etcd-io/etcd#21065 pr open: proposed fix (client sendLoop with bounded queues, best-effort cancels)
---

# watch: the in-process client and server watch loops deadlock on a burst of cancellations

- **Status**: bug (a permanent deadlock of the shared in-process watch stream, used by every
  `v3election`/`v3lock` RPC and any `v3client` user).
- **Where** (etcd pin `107edf7e4`): `client/v3/watch.go:688-707` (`watchGRPCStream.run` sends a
  cancel with a blocking `wc.Send` for each closed substream), `client/v3/watch.go:773-790`
  (`serveWatchClient` hands each response to `run` through the unbuffered `respc`),
  `server/etcdserver/api/v3rpc/watch.go:372-386` (`recvLoop` answers a cancel on `ctrlStream`,
  buffer 16, line 124), `:514-519` (`sendLoop` drains `ctrlStream` with a blocking `Send`),
  `server/proxy/grpcproxy/adapter/chan_stream.go:142-154` (the in-process pipe: an unbuffered
  client-to-server channel and a one-slot server-to-client channel).
- **What happens**: when more than about 16 substreams close at once (for example, the waiting
  `Campaign` callers of #20716 are killed), `run` sends their cancels one by one. `recvLoop`
  fills `ctrlStream`, then blocks. `sendLoop` blocks sending to the client, whose
  `serveWatchClient` blocks on `respc`, which only `run` reads, and `run` is blocked in `Send`.
  None of the four goroutines can proceed. New watches on the in-process client get no events, and
  the slow-watcher metrics stay up. Reproduction: upstream PR #21064's integration test. Not run
  here. Over a network connection, HTTP/2 flow-control windows make the threshold thousands of
  requests instead of 16. Not demonstrated.
- **Expected**: a cancellation burst may slow the stream but must not stop it. Cancels are best
  effort (the server drops a watcher anyway when its stream closes).
- **How the proof handles it**: the four loops are verified (`watchGRPCStream.run`,
  `serveWatchClient`, `serverWatchStream.recvLoop`, `sendLoop`), but the specs are partial
  correctness, and a goroutine blocked forever meets them. No spec here states
  liveness. The adapter is not translated, and the client's results assume a
  gRPC connection (`Spec/go_etcd_io/etcd/api/v3/etcdserverpb/watchClient__Watch.lean`). The
  safety stand-in proposed, `watch-stream-no-cyclic-wait`, is in
  `notes/bug-triage/etcd-20716.md`.
- **Possible fixes**: send requests from a separate client goroutine with bounded queues,
  dropping best-effort cancels under pressure (PR #21065); or make `recvLoop`'s control
  responses non-blocking; or buffer the adapter's pipe (this only moves the threshold).
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#20716.
