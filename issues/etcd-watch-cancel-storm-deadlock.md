---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#18879 issue open: the report (in-process client, many watches cancelled at once; new watches get no events)
  - etcd-io/etcd#20716 issue closed: the same over the election service's in-process watch (`adapter.WatchServerToWatchClient`)
  - etcd-io/etcd#21065 pr open: moves the client's sends to a goroutine with bounded queues; fixes the deadlock but drops cancel requests (notes/pr-verify/etcd-21065.md)
  - etcd-io/etcd#21064 pr closed: the reproduction test of #21065 (not merged)
---

# The client's watch stream and the server's watch stream deadlock when many watches are cancelled at once over the in-process transport

**Status**: a bug (a liveness failure: the stream stops for good) in the pinned code, known
upstream.

**Where** (fork pin `09669450f`):
- `client/v3/watch.go`: `watchGRPCStream.run` (512) is both the only sender on the gRPC stream
  and the only reader of its responses (`respc`). In the `closingc` case (688) it sends a cancel
  request with a blocking `wc.Send` (706); while it is in `Send` it reads no response.
- `server/etcdserver/api/v3rpc/watch.go`: `recvLoop` (249) answers each cancel with a response on
  `ctrlStream` (367), a channel of 16 (`ctrlStreamBufLen`, 124), and blocks when it is full;
  `sendLoop` (411) drains it with `gRPCStream.Send` (547), which blocks when the client does not
  read.
- `server/proxy/grpcproxy/adapter/chan_stream.go`: the in-process stream (`v3client`, the
  election and lock services) passes each message over an unbuffered channel (145): a `Send`
  waits for the other side's `Recv`.

**What happens**: when many watches of one client stream are closed at once, `run` sends their
cancels one after the other. The server's `recvLoop` answers each on `ctrlStream`; `sendLoop`
must send those answers (and the events) to the client, whose `run` does not read them while it
sends. Once `ctrlStream` is full, `recvLoop` stops reading the stream, so `run`'s `Send` never
returns: `run` waits for `recvLoop`, `recvLoop` for `sendLoop`, `sendLoop` for `run`. Every watch
on that client stream stops, and new watches on it are never created. Over a gRPC connection the
transport's buffers and flow-control window absorb the cancels, and the cycle does not close in
practice.

Reproduction: `notes/pr-verify/etcd-21065/v3_watch_inprocess_cancel_storm_test.go` (an
integration test; 2000 watches on one `v3client` client, all closed at once). At the pin, over
the in-process client, after the storm the watch left open gets no event and a new watch is not
created, and 1918 of the closed watches are still registered on the server
(`notes/pr-verify/etcd-21065/integ-fork-pin.log`; the same at upstream `b9ba05c8e`,
`integ-up-base.log`). Over a gRPC connection the same test passes.

**Expected**: closing watches never stops the stream; the remaining watches keep receiving
events.

**How the proof handles it**: the specs of `run` and of the server's stream handlers are partial
correctness (safety: no panic, every delivered event correct); a deadlock satisfies them. Nothing
in the proof rules it out.

**Possible fixes**: decouple `run`'s sends from its receives, as etcd-io/etcd#21065 does, but
without dropping cancel requests (a queue that does not lose them, or a retry of a dropped cancel
on the watch's next event: today `cancelSet` suppresses it); or make the server never block its
receive loop on the control channel.

**Found**: 2026-10-17, verifying etcd-io/etcd#21065 (`notes/pr-verify/etcd-21065.md`): the
integration test written for the PR's findings, run at the pin.
