# etcd-watch-id-reuse-stale-events

- **Finding**: `issues/etcd-watch-id-reuse-stale-events.md` (the fix also covers
  `issues/etcd-watch-canceled-pending-retained.md`: a canceled watcher's responses taken after its canceled response
  are now dropped instead of kept in `pending` until the stream closes)
- **Target**: etcd-io/etcd, `main`
- **Branch**: `fix/etcd-watch-id-reuse-stale-events` in `~/etcd-fixes/etcd-watch-id-reuse-stale-events`, two commits:
  7a311ab5c adds the test, which fails there; 97aa6191d is the fix. Not pushed: the fork
  (`https://github.com/upamanyus/etcd/tree/fix/etcd-watch-id-reuse-stale-events`, the branch the links in
  `issue.md` name) still has the old single commit 29b6544ed (off b25719d10) until the user approves
  `git -C ~/etcd-fixes/etcd-watch-id-reuse-stale-events push --force-with-lease=fix/etcd-watch-id-reuse-stale-events:29b6544ed origin fix/etcd-watch-id-reuse-stale-events`.
  After the push, lines 492-549 of `tests/integration/clientv3/watch/v3_watch_test.go` are the test (check on GitHub).
- **Base**: upstream `main` 22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4 (2026-10-18); `watch.go` and the watch tests
  unchanged since b25719d10, the previous base.
- **State**: draft (revised 2026-10-18 to the current skill: split into tests and fix commits, deterministic cancel
  in the test, new base)
- **Upstream issue**: —
- **PR**: —

Commit messages to rewrite (drafts): `tests: test reusing the ID of a canceled watcher` (no body);
`etcdserver: do not send a canceled watcher's events to a reused watch ID`, body "Make a watch create wait until the
events queued for the watchers canceled before it are taken, and drop those taken after the cancel."

## Security

The stale events are of a watch the client was permitted to create, on its range, on the same stream (same auth
context); the old watch would have delivered them had it not been canceled. No auth bypass, crash, hang or data
loss: a public issue.

## Duplicates checked (2026-10-16)

Searches (3): `watch id reuse cancel`, `watch pending events cancel sendLoop`, `"watch id" canceled stale events`.
No duplicate, no open PR fixing it. Related, different:

- #21880 (open PR): grpc-proxy honors the client's `WatchId` (#12819). With it, the bug would also reach clients
  behind the proxy; today the proxy assigns its own IDs (the new test skips under the proxy).
- #14296 (closed PR): a create rejected by auth used to send `Canceled` with `WatchId` 0, removing a live watch 0
  from `sendLoop`'s announced IDs; same bookkeeping (`ids`), different bug.

## Why the fix works

mvcc's watch stream has one channel (capacity 128) for all its watchers; `sendLoop` takes from it and from the
control channel (created and canceled responses, in `recvLoop`'s order) in either order. Once `Cancel` returns, mvcc
sends nothing more for that watcher (`cancelWatcher` takes the store lock that every send holds, and waits out a
victim batch being retried), so every response of the canceled watcher still to be taken is in the channel when
`recvLoop` queues the canceled response.

At the base: if `sendLoop` takes the canceled response first, it removes the ID from `ids`; each later response of
the canceled watcher finds the ID not announced and is buffered in `pending[id]`. A create with the same ID (explicit,
or automatic: mvcc's `nextID` skips only live IDs) succeeds in mvcc at once; its created response flushes
`pending[id]` to the client, and the responses taken after it are sent directly. The client sees them after the
new created response, with the new watch's ID.

With the fix: when `sendLoop` takes a canceled response, the first `len(Chan())` responses still to be taken include
all of the canceled watcher's (none can be added after the canceled response was queued). `sendLoop` drops that
ID's responses among them and, once it has taken them, closes the cancel's channel. `recvLoop` makes each create
wait for the channels of the cancels before it, so the new watcher exists only after the old one's responses are
gone, and no response of the new watcher can be dropped. The drain counts only grow (a later cancel's mark is never
before an earlier one's, since the channel is FIFO), so they complete in order.

## Reproduction and test

Over one raw gRPC watch stream, single member (the integration framework): create `WatchId: 1` on `a`; put `a` ten
times with a 100 KiB value without reading the stream (gRPC flow control blocks `sendLoop` in `Send`, so the mvcc
channel keeps the events); cancel 1; wait until the member's `etcd_debugging_mvcc_watcher_total` is 0 (the cancel
was handled; `TestV3WatchCloseCancelRace` uses the same metric); create `WatchId: 1` on `b` from the revision after
the last put of `a` (with the fix the create runs only after the client reads, after the put of `b`); put `b`; read
until the event of `b`. It asserts only the guarantee: after the second created response, the only event is `b`.

Changes from the previous test (2026-10-16): the 100 ms sleep is replaced by waiting for the cancel through the
metric, which makes the order of the cancel before the client reads deterministic; the local `watch` closure is
inlined. What remains nondeterministic at the base is `sendLoop`'s `select` between the canceled response and the
queued events (the test fails unless the canceled response is taken after every queued event, about 2^-k for k
queued events); it does not affect the test with the fix, which passes whatever the order. Waiting for the
re-create the same way is not possible: with the fix, it runs only after the client reads.

Sizes tried earlier (stale events after the created response, 3-5 runs each): 30 x 100 KB: 24-27; 10 x 100 KiB:
3-7 (never 0); 10 x 64 KiB: 4-6; 5 x 100 KB: 1-2; 5 x 64 KiB: 0-1; 2-3 x 1 MB: 0; 100 x 10 KB: 85; 1000 x 1 KB:
127-128.

Not reproduced: the variant where an automatically assigned ID equals an explicit ID canceled earlier. The fix covers
it (every create waits).

## Verification (go1.27.2 linux/amd64)

- At the tests commit 7a311ab5c: `cd tests && go test ./integration/clientv3/watch/ -run
  'TestV3WatchReuseCanceledID$' -count=20`: 20 of 20 FAIL (and 60 of 60 before committing, the same test), e.g.
  `actual  : []string{"a", "a", "a", "a", "a", "a", "a", "b"}`; 5 to 7 stale events per run.
- The finding's one-line alternative (`delete(pending, wid)` on cancel) on that commit: 10 of 10 FAIL (5-7 stale
  events), as before.
- At the fix commit 97aa6191d: the new test `-count=50` PASS; `go test -race ... -count=5` PASS; `cd server && go
  test ./etcdserver/api/v3rpc/` ok; `cd tests && go test ./integration/clientv3/watch/` (whole package, 81 s) ok;
  `go test -tags cluster_proxy ./integration/clientv3/watch/` (through the grpc-proxy, which cancels and creates
  watches on shared streams; the new test skips there) ok.
- `gofmt -l` (both files) empty; `go vet ./etcdserver/api/v3rpc/` and `go vet ./integration/clientv3/watch/` clean.

Not run: e2e, robustness, `make verify`.

`check.py`: no FAIL. WARNs kept: the seven comment lines, each says what the code does not (what `mu` guards, when a
`canceling` channel is closed, why a create waits, what `taken` and `until` count; the last two in the style of
`ids` and `pending` above them); the issue's 256 words of prose (the four steps are needed); the PR's 111 words (the
approved raft example has 136).

## If a reviewer asks

- What changes: a create request waits in `recvLoop` until `sendLoop` has taken from the mvcc channel every
  response that was queued when the canceled responses before it were taken (at most the channel's 128). With a
  client that reads its stream this is short; while the client does not read, later creates on the stream wait, as
  every request already does when the control channel (16) is full. A create with `StartRevision` 0 now starts at
  the revision when it runs, after the wait (the test therefore watches `b` from an explicit revision).
- Why every create waits, not only one reusing a canceled ID: an automatically assigned ID can equal a canceled
  explicit ID (mvcc's `watchStream.Watch` skips only live IDs), and `recvLoop` does not know the ID before mvcc
  assigns it. A narrower variant (open question for the user): wait only on a stream that has used an explicit
  `WatchId`; on a stream with only automatic IDs (the Go client, `etcdctl`, so Kubernetes) mvcc's `nextID` never
  returns to an ID, so no create there needs to wait. About four more lines; it would remove the latency change for
  the Go client entirely.
- Why responses taken after the canceled response are dropped: "No further events will be sent to the canceled
  watcher" (`rpc.proto`). Before, without a reuse, they stayed in `pending` until the stream closed.
- Why not only drop `pending[id]` on cancel: see Verification; most stale responses are taken after the new created
  response and are sent directly.
- Why not compute the drain mark in `recvLoop` and let the create run at once: `recvLoop` cannot read `sendLoop`'s
  taken count and the channel's length atomically; either order of the two reads can miss a stale response or
  count a new watcher's response as stale. `sendLoop`, the only reader of the channel, counts exactly.
- Alternatives: tag mvcc's `WatchResponse` with the watcher (a generation number from `WatchStream.Watch`; an mvcc
  API change, and `sendLoop` would compare it); reject a create whose explicit ID is still draining (changes the
  API; the client would not know when to retry); make every cancel wait instead of creates (delays every request
  after a cancel, also when no create follows).
- Backports: `release-3.6`/`3.5` have the same `sendLoop`; not checked or run there.
