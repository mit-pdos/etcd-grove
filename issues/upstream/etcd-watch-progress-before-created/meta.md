# etcd-watch-progress-before-created

- **Finding**: `issues/etcd-watch-progress-before-created.md`
- **Target**: etcd-io/etcd, `main`
- **Branch**: `fix/etcd-watch-progress-before-created` in `~/etcd-fixes/etcd-watch-progress-before-created`, two
  commits: 0c15820c4 adds the test, which fails there; 77e38c1b1 is the fix. Not pushed; the issue's test link
  (`#L1536-L1598`, the doc comment to the closing brace in the local file) is to be checked on GitHub after the push.
- **Base**: upstream `main` 22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4 (2026-10-18); `v3rpc/watch.go`, the client's
  `watch.go`, `mvcc/watchable_store.go` and the watch integration tests are unchanged since f061acd09, the base of
  the fork's first fix (`watch-progress-before-created`, c267e0ffe).
- **State**: draft (2026-10-19)
- **Upstream issue**: —
- **PR**: —

Commit messages to rewrite (drafts): `tests: test a progress response sent after a watch is created` (no body);
`etcdserver: send queued progress responses before a created response`, body "A progress response to a request
received before a watch was created could be sent after the watch's created response, and clients applied it to the
new watch."

## Security

A wrong order of responses on the client's own stream, for watches it is permitted to create: no crash, hang, data
loss or auth bypass. A public issue.

## Duplicates checked (2026-10-19)

Searches (5): `progress notification created watch order`, `RequestProgress new watch`, `progress notify before
events`, `progress notify broadcast watcher`, `sendLoop progress is:open`. No duplicate, no open PR fixing it.
Related, different:

- #15220 (closed issue): requested progress responses were sent on `ctrlStream` and could overtake a watch's queued
  events (a progress request after the create). The reverse order here.
- #15237 (merged PR, the fix of #15220): requested progress goes through mvcc's watch channel (`RequestProgressAll`),
  sent only when every watcher of the stream is synced. It leaves the created response on `ctrlStream`, which is
  what overtakes the progress response here.
- #15248 (closed PR): the client's `nextRev` on a progress response; not about the order.

## Why the fix works

At the base, `recvLoop` handles a stream's requests one at a time. A progress request calls `RequestProgressAll`,
which, if every watcher of the stream is synced, puts a response with watch ID -1 at the store's current revision `r`
on the stream's mvcc channel at once (or drops it if the channel is full; if a watcher is unsynced, nothing is sent:
no response is deferred). A later create request registers the watcher (unsynced if it starts below `r`) and puts its
created response on `ctrlStream`. `sendLoop` selects between the two channels; when both are ready Go picks at
random, so the created response can be sent before the progress response. The Go client moves the new substream
into `substreams` on its created response and broadcasts a -1 progress response to every substream, the new one
included: the new watch receives "progress at `r`" before its events below `r`.

With the fix, when `sendLoop` takes a created response it first sends the `len(Chan())` responses on the mvcc channel.
The progress response was put there before the created response was put on `ctrlStream` (same goroutine, in
order), so it is either already sent or among those. `sendLoop` is the channel's only reader, so the `n` receives do
not block. Responses of the new watcher among them are buffered in `pending` as before (its ID is not yet announced)
and flushed after its created response, so its own order is unchanged.

The drain is bounded by the channel's length when the created response is taken (at most 128, `chanBufLen`), not
"until empty": on a busy stream an unbounded drain could hold a created response back indefinitely. (The fork's first
fix, c267e0ffe, drained until empty, for a reason specific to how it is checked there; both pass the same tests.)

## Reproduction and test

Over one raw gRPC watch stream, single member (the integration framework): put `b` (rev 2); create a watch on `a`;
put `a` ten times with a 100 KiB value without reading (gRPC flow control blocks `sendLoop` in `Send`, so mvcc's
channel keeps the events; the watcher on `a` stays synced, as its events fit the channel); send a progress request
(answered at once, at revision 12, queued behind the events); create a watch on `b` from revision 2; wait until
`etcd_debugging_mvcc_watcher_total` is 2 (the create was handled; the sibling `TestV3WatchReuseCanceledID` uses the
same metric); read until the event of `b`. It asserts only the guarantee: no progress response after the created
response of the watch on `b` and before its event. At the base, the created response must lose `sendLoop`'s random
select against every queued event and the progress response to pass, about 2^-k for k queued responses.

The finding's Go-client reproduction (`TestWatchProgressBeforeCreatedRace` in the finding: 500 trials of
`RequestProgress` then `Watch(WithRev(2), WithProgressNotify())` while 30 puts go to another watch on the stream) is
mentioned in the issue as the Go client's case; it is not added to the branch (random, up to 500 trials).

## Verification (go1.27.2 linux/amd64)

- At the tests commit 0c15820c4: `cd tests && go test ./integration/clientv3/watch/ -run
  'TestV3WatchProgressBeforeCreated$' -count=20`: 20 of 20 FAIL, each `Should be zero, but was 12`.
- At the fix commit 77e38c1b1: the new test `-count=50` PASS; `go test -race ... -count=5` PASS; `cd server && go test
  ./etcdserver/api/v3rpc/` ok; `cd tests && go test ./integration/clientv3/watch/ -count=1` (whole package, 82 s) ok;
  `go test -tags cluster_proxy ./integration/clientv3/watch/ -count=1` (79 s; the new test skips there, as the other
  progress-request tests do) ok.
- The finding's Go-client reproduction, by `go test -overlay` (the test file added; for the base, `v3rpc/watch.go`
  replaced by the base's, i.e. the fix branch's file minus the fix): at the base 3 of 3 runs hit, at trials 55, 1
  and 18; with the fix, no hit in 2 × 500 trials.
- `gofmt -l` (both files) empty; `go vet ./etcdserver/api/v3rpc/` and `go vet ./integration/clientv3/watch/` clean.

Not run: e2e, robustness, `make verify`.

`check.py`: no FAIL. WARNs kept: the comment lines, all but two existing comments moved into the closure (indented
once less), the closure's doc (what `false` means) and the drain's comment (why the created response waits); the
issue's 305 words of prose (about 45 are the form's headings); the PR's 98 words (the approved raft example has
136).

## Sibling: etcd-watch-id-reuse-stale-events

Both change `sendLoop`. `git merge-tree` of the two branches: no conflict. The merged tree builds, and both new
tests (`-count=20`) and the v3rpc unit tests pass on it. Semantically the merge is right: the sibling counts the
responses taken from mvcc's channel (`taken`) in the main loop, and this fix's drain does not count them, but the
sibling makes every create wait in `recvLoop` until the drains of the cancels before it are done, so no drain is
pending whenever `sendLoop` takes a created response, and none of the responses drained here is stale or needs
counting. Hence no conflict note in either PR.

## If a reviewer asks

- Why a closure: the code that sends a mvcc response is needed in two places (the main loop and the drain); `git diff
  -w` shows the change is the drain plus `continue`/`return` becoming `return true`/`return false`.
- Why not answer the progress request on `ctrlStream`: that was the bug of #15220 (it overtakes queued events).
- Why not in the client (broadcast only to substreams created before the request): the client cannot match a
  response to its request, since the server sends none while a watcher is unsynced; and older servers would still
  send the response late.
- Why not make `recvLoop` wait until the progress response is sent before handling the next request: needs a signal
  from `sendLoop` per progress request, and delays every request after a progress request.
- Cost: a created response waits for at most 128 queued responses, which `sendLoop` sends anyway.
- The `rpc.proto` wording ("all future events received in this stream" have a higher revision than a progress
  response) cannot hold for a watch created later from an earlier revision, with or without the fix; asked in the
  issue as a question.
- etcd's own `cache` package reads a progress notification as "the cache has every event up to this revision"
  (it raises its revision and releases waiting consistent `Get`s). By code reading, not reproduced: a cache whose
  watch is (re)created on a client stream that has another synced watcher (e.g. two caches over one client), right
  after a progress request on that stream, can serve a stale consistent `Get` until the skipped events arrive and
  it resyncs. Not in the issue, which keeps to the reproduced symptom.
- Backports: `release-3.6`/`3.5` have the same `sendLoop` structure; not checked or run there.
