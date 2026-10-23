# etcd-watch-id-reuse-stale-events

- **Finding**: `issues/etcd-watch-id-reuse-stale-events.md` (the fix also covers
  `issues/nonissues/etcd-watch-canceled-pending-retained.md`: a canceled watcher's responses taken after its canceled response
  are now dropped instead of kept in `pending` until the stream closes, on every stream; the PR does not mention it)
- **Target**: etcd-io/etcd, `main`
- **Branch**: `fix/etcd-watch-id-reuse-stale-events` in `~/etcd-fixes/etcd-watch-id-reuse-stale-events`, two commits:
  c5db1e07b adds the test, which fails there; aa5cc5002 is the fix. Rebuilt 2026-10-21 on the new base (the
  previous head, 97aa6191d, pushed to `upamanyus/etcd` on 2026-10-19, is kept as the local branch
  `backup/etcd-watch-id-reuse-stale-events-v1`); not yet force-pushed. The issue's test link (`#L492-L549`) is the
  test's lines on the new branch (doc comment to closing brace, the same range as on the pushed 97aa6191d); check it
  on GitHub after the force-push.
- **Base**: upstream `main` bf9cadf044f0531036a61c9b6dbeba8aef2a3b30 (2026-10-21); `watch.go`, `mvcc/watcher.go` and
  the watch tests unchanged since 22cc5d9ac, the previous base (the four new commits: Go 1.27.3, a `concurrency`
  session option, mvcc's Hash/Restore race).
- **State**: draft (revised 2026-10-21: creates wait only on a stream where the client has chosen a watch ID; the
  test's puts are 20 x 50 KiB; rebased)
- **Upstream issue**: —
- **PR**: —

Commit messages to rewrite (drafts): `tests: test reusing the ID of a canceled watcher` (no body);
`etcdserver: do not send a canceled watcher's events to a reused watch ID`, body "Drop a canceled watcher's queued
events, and hold back a create that may reuse its ID until they are dropped."

## Security

The stale events are of a watch the client was permitted to create, on its range, on the same stream (same auth
context); the old watch would have delivered them had it not been canceled. No auth bypass, crash, hang or data
loss: a public issue.

## Duplicates checked

2026-10-16, 3 searches: `watch id reuse cancel`, `watch pending events cancel sendLoop`, `"watch id" canceled stale
events`. 2026-10-21 (authenticated), issues and PRs: `watch id reuse`, `watch cancel sendLoop`, `watch pending
canceled`, and every watch issue/PR created since 2026-10-16. No duplicate, no open PR fixing it. Related, different:

- #21880 (open PR): grpc-proxy honors the client's `WatchId` (#12819). With it, the bug would also reach clients
  behind the proxy; today the proxy assigns its own IDs (the new test skips under the proxy).
- #14296 (closed PR): a create rejected by auth used to send `Canceled` with `WatchId` 0, removing a live watch 0
  from `sendLoop`'s announced IDs; same bookkeeping (`ids`), different bug.
- #21065 (open PR, fixes #18879 and #20716, closed not planned): in-process clients (the gRPC adapter used by the
  election and lock services, `v3client`) deadlock when `recvLoop` blocks on a full control channel while the
  client cannot read. It changes the client and `ctrlStreamBufLen` (16 to 128); `git merge-tree` with this
  branch is clean (2026-10-21). It is why creates here wait only on streams with client-chosen IDs
  (below).

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
ID's responses among them and, once it has taken them, closes the cancel's channel. The channels close in the order
of the cancels: a later cancel's mark (`taken + len(Chan())`) is never before an earlier one's, since the channel is
FIFO, and a mark with nothing left to take (closed at once) means no earlier drain is pending. So `recvLoop` keeps
only the last cancel's channel.

Dropping is always right: during a drain no new watcher has the canceled ID. On a stream where every create uses
`AutoWatchID` (the Go client, `etcdctl`, so Kubernetes; the in-process adapter), mvcc's `nextID` only grows, so an
ID is never assigned twice and no create waits. Once a create on the stream sets `WatchId` (the flag is set before
that create's own wait, so an explicit ID equal to a canceled automatic one is covered), every later create waits
for the last cancel's channel: an explicit ID can equal a canceled one, and an automatic ID can equal a canceled
explicit one, which `recvLoop` cannot know before mvcc assigns it.

## Reproduction and test

Over one raw gRPC watch stream, single member (the integration framework): create `WatchId: 1` on `a`; put `a` 20
times with a 50 KiB value without reading the stream (gRPC flow control blocks `sendLoop` in `Send`, so the mvcc
channel keeps the events); cancel 1; wait until the member's `etcd_debugging_mvcc_watcher_total` is 0 (the cancel
was handled; `TestV3WatchCloseCancelRace` uses the same metric); create `WatchId: 1` on `b` from the revision after
the last put of `a` (with the fix the create runs only after the client reads, after the put of `b`); put `b`; read
until the event of `b`. It asserts only the guarantee: after the second created response, the only event is `b`.

At the base, the test passes only if `sendLoop`'s `select` takes the canceled response after every queued event
(about 2^-k for k queued events); with the fix it passes whatever the order. Sizes measured on 2026-10-21 at the
base (stale events after the created response, 20 runs each unless noted; all runs failed unless noted): 10 x 100
KiB (the previous test): 1-7, a run with 1 left little margin; 20 x 50 KiB (chosen): 9-15 over 80 runs, about
0.3 s a run; 50 x 20 KiB: 37-42; 100 x 10 KiB: 81-86 (0.4 s, but the failure prints an 86-element list); 4 x 256
KiB: 1-2; 3 x 256 KiB: 0-1 (4 of 20 passed); 2 x 512 KiB: 0 (10 of 20 passed). Earlier (2026-10-16): 1000 x 1 KB
fills mvcc's channel (127-128), which brings in mvcc's slow-watcher path; not used.

The automatic-ID variant, reproduced 2026-10-21 with a scratch copy of the test (not committed): after the cancel of
explicit 1, create on `c` without `WatchId` (assigned 0), then on `b` without `WatchId` (assigned 1, the canceled
ID): at the base (10 x 100 KiB) 10 of 10 fail with 5-7 stale events; with the fix 20 of 20 pass. Same root cause
and fix, so one test; the issue's "who else" sentence names both ways the ID is chosen.

## Verification (go1.27.3 linux/amd64)

- At the tests commit c5db1e07b (the base plus the test): `cd tests && go test ./integration/clientv3/watch/ -run
  'TestV3WatchReuseCanceledID$' -count=80`: 80 of 80 FAIL, 9 to 15 stale events, e.g. `actual  : []string{"a", "a",
  "a", "a", "a", "a", "a", "a", "a", "a", "a", "a", "a", "a", "a", "b"}`.
- At the fix commit aa5cc5002: the new test `-count=50` PASS; `go test -race ... -count=5` PASS; the automatic-ID
  variant (scratch) 20 of 20 PASS; `cd server && go test ./etcdserver/api/v3rpc/` ok; `cd tests && go test ./integration/clientv3/watch/` (whole
  package, 83 s) ok; `go test -tags cluster_proxy ./integration/clientv3/watch/` (through the grpc-proxy, which
  cancels and creates watches on shared streams; the new test skips there) ok; `go test ./integration/ -run 'TestV3Election|TestV3Lock|TestElection|TestMutex'` (the election and lock
  services, through the in-process adapter) ok; `go test ./integration/clientv3/concurrency/...` ok.
- `gofmt -l` (both files) empty; `go vet ./etcdserver/api/v3rpc/` and `go vet ./integration/clientv3/watch/` clean.
- Earlier (2026-10-18, previous fix): the finding's one-line alternative (`delete(pending, wid)` on cancel) fails 10
  of 10.

Not run: e2e, robustness, `make verify`; no test of an in-process client (the reasoning below is from the code).

`check.py` (2026-10-21): no FAIL. WARNs kept: the eight added comment lines, each says what the code does not (what
`mu` guards, when a `canceling` channel is closed, why and when a create waits and why one channel suffices, what
`taken` and `until` count; the last two in the style of `ids` and `pending` above them); the issue's 262 words of
prose (the four steps and the who-else sentence, which now names the automatic-ID case); the PR's 117 words (the
approved raft example has 136).

## If a reviewer asks

- What changes: a canceled watcher's responses still queued at its cancel are dropped (before: sent before the
  canceled response, or buffered after it, kept until the stream closed, or flushed to a new watch with the same ID).
  On a stream where the client has set `WatchId` on some create, a create waits in `recvLoop` until `sendLoop` has
  taken from mvcc's channel every response queued when the last earlier cancel's canceled response was taken (at
  most the channel's 128). There, a create with `StartRevision` 0 starts at the revision when it runs, after the wait
  (the test therefore watches `b` from an explicit revision).
- Why creates do not wait on every stream (the previous version of this branch did): while a create waits,
  `recvLoop` reads no request, and the drain needs the client to read. A client that sends from the goroutine that
  also consumes responses (the Go client's `run` loop; with the in-process adapter, whose channels are unbuffered,
  each send waits for `recvLoop`) can then deadlock: the next cancel or create blocks the client, which stops reading,
  so `sendLoop` stays blocked in `Send` and the drain never ends. At the base the same deadlock needs 16 queued
  control responses (#18879, #20716, #21065); waiting on every stream would bring it down to one create after a
  cancel with responses queued. Only streams with client-chosen IDs can reuse an ID, and no client in etcd uses them.
- Why responses taken after the canceled response are dropped: "No further events will be sent to the canceled
  watcher" (`rpc.proto`). Before, without a reuse, they stayed in `pending` until the stream closed.
- Why not only drop `pending[id]` on cancel: see Verification; most stale responses are taken after the new created
  response and are sent directly.
- Why not compute the drain mark in `recvLoop` and let the create run at once: `recvLoop` cannot read `sendLoop`'s
  taken count and the channel's length atomically; either order of the two reads can miss a stale response or
  count a new watcher's response as stale. `sendLoop`, the only reader of the channel, counts exactly.
- Other layers: mvcc's `WatchResponse` carries only the ID, and its `Watch` doc says the ID "appears as WatchID in
  events that are sent to the created watcher", without promising an ID is not reused; tagging responses with the
  watcher (a generation number returned by `WatchStream.Watch`, compared in `sendLoop`) would need no wait but
  changes mvcc's `WatchStream` API and its callers, a larger change. Keying
  `ids`/`pending` by watcher in `sendLoop` needs that same tag (or mapping client IDs to internal mvcc IDs that are
  never reused, which moves ID assignment and duplicate checks out of mvcc into `v3rpc`). Rejecting a create whose
  explicit ID is still draining changes the API (the client would not know when to retry). Making every cancel wait
  instead of creates delays every request after a cancel, on every stream (the deadlock above).
- Backports: `release-3.6`/`3.5` have the same `sendLoop`; not checked or run there.
