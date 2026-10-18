# etcd-watch-id-reuse-stale-events

- **Finding**: `issues/etcd-watch-id-reuse-stale-events.md`
- **Target**: etcd-io/etcd, `main`
- **Branch**: `fix/etcd-watch-id-reuse-stale-events` in `~/etcd-fixes/etcd-watch-id-reuse-stale-events` (commit 29b6544ed), pushed 2026-10-18 to `upamanyus/etcd`
  (`https://github.com/upamanyus/etcd/tree/fix/etcd-watch-id-reuse-stale-events`), the branch the links in `issue.md` name.
- **Base**: upstream `main` b25719d10cdc41fb707b0d9f819c2529dec5d590 (2026-10-16); `sendLoop`/`recvLoop` unchanged
  from the finding's revision.
- **State**: draft
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-16)

Searches (3): `watch id reuse cancel`, `watch pending events cancel sendLoop`, `"watch id" canceled stale events`.
No duplicate, no open PR fixing it. Related, different:

- #21880 (open PR): grpc-proxy honors the client's `WatchId` (#12819). With it, the bug would also reach clients
  behind the proxy; today the proxy assigns its own IDs (the new test skips under the proxy).
- #14296 (closed PR): a create rejected by auth used to send `Canceled` with `WatchId` 0, removing a live watch 0
  from `sendLoop`'s announced IDs; same bookkeeping (`ids`), different bug.

## Reproduction

The finding came from a proof's model, not a run; it reproduces. Over one raw gRPC watch stream, single member:
create `WatchId: 1` on `a`; put `a` 10 times with a 100 KiB value without reading the stream (gRPC flow control
blocks `sendLoop` in `Send`, so the mvcc channel keeps the events); cancel 1; create `WatchId: 1` on `b` from the
next revision; sleep 100 ms (so `recvLoop` handles both before the client reads); put `b`; read. At the base, after
the second created response, watch 1 receives 3-7 events of `a` (revisions below its start revision, outside its
key), then `b`. 10/10 runs failed at the base (and 20/20 of an earlier variant of the test).

Sizes tried (stale events after the created response, 3-5 runs each): 30 x 100 KB: 24-27; 10 x 100 KiB: 3-7 (20
runs, never 0); 10 x 64 KiB: 4-6; 5 x 100 KB: 1-2; 5 x 64 KiB: 0-1; 2-3 x 1 MB: 0; 100 x 10 KB: 85; 1000 x 1 KB:
127-128.

The finding's suggested fix (`delete(pending, wid)` on cancel) does not fix it: 10/10 runs still failed. Most of the
canceled watcher's responses are taken after the new created response, when the ID is announced again, and are
sent directly, not from `pending`.

Not reproduced: the finding's variant where an automatically assigned ID equals an explicit ID canceled earlier
(mvcc's `nextID` skips only live IDs). The fix covers it (every create waits).

Security: the stale events are of a watch the client was permitted to create, on its range; the old watch would
have delivered them had it not been canceled. No auth bypass.

## Verification

- New test, at the base (fix reverted): `cd tests && go test ./integration/clientv3/watch/ -run
  TestV3WatchReuseCanceledID -count=10` — 10/10 FAIL, e.g. `actual  : []string{"a", "a", "a", "a", "a", "a", "a",
  "b"}`.
- With the fix: `-count=20` PASS; `go test -race ... -count=5` PASS.
- `cd server && gofmt -l etcdserver/api/v3rpc && go vet ./etcdserver/api/v3rpc/ && go test
  ./etcdserver/api/v3rpc/` — clean, ok.
- `cd tests && go vet ./integration/clientv3/watch/`; `go test ./integration/clientv3/watch/` (whole package), `go
  test ./integration/ -run Watch`, `go test ./integration/clientv3/ -run Watch`: all ok (the watch package in 82 s;
  the other two match few or no tests). Rerun after the last amend (a comment removed): the new test `-count=10`,
  `./etcdserver/api/v3rpc/`, `gofmt`, `go vet`.

`check.py`: no FAIL; the seven comment WARNs kept, each says what the code does not (what `mu` guards, when a
`canceling` channel is closed, why a create waits, what `taken` and `until` count).

Not run: e2e, robustness, `make verify`, the integration tests through the grpc-proxy (`-tags cluster_proxy`).

## If a reviewer asks

- What changes: a create request waits in `recvLoop` until `sendLoop` has taken from the mvcc channel every
  response that was queued when the canceled responses before it were taken (at most the channel's 128). With a
  client that reads its stream this is short; while the client does not read, later requests on the stream wait,
  as they already do when the control channel (16) is full. A create with `StartRevision` 0 now starts at the
  revision when it runs, after the wait (the test therefore watches `b` from an explicit revision).
- Why every create waits, not only one reusing a canceled ID: an automatically assigned ID can equal a canceled
  explicit ID (mvcc's `watchStream.Watch` skips only live IDs), and `recvLoop` does not know the ID before mvcc
  assigns it.
- Why responses taken after the canceled response are dropped: "No further events will be sent to the canceled
  watcher" (`rpc.proto`). Before, without a reuse, they stayed in `pending` until the stream closed.
- Why not only drop `pending[id]` on cancel: see Reproduction; most stale responses come after the new created
  response.
- Alternatives: tag mvcc's `WatchResponse` with the watcher (an mvcc API change: `WatchStream.Watch` would return
  it, and `sendLoop` would compare); reject a create whose explicit ID was canceled on the stream (changes the API,
  needs a set of every canceled ID; the client would not know when to retry); make every cancel wait instead of
  creates (delays every cancel, also those no create follows).
- Backports: `release-3.6`/`3.5` have the same `sendLoop`; not checked or run there.
