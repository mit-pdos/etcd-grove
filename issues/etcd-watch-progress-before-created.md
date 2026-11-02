---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#15220 issue closed: related, different: a requested progress response overtook a watch's queued events (progress request after the create)
  - etcd-io/etcd#15237 pr merged: the fix of #15220 (progress responses through mvcc's watch channel); leaves the created response on the control channel, which overtakes the progress response here
  - etcd-io/etcd#20229 pr merged: related, different trigger (a lagging member's progress below a watch's start revision); its check covers only watchers that exist when the progress is computed
blocks-proof: yes
---

# watch: a progress notification requested before a watch is created can reach that watch before its events

A watch created right after a progress request, from a revision below the current one, can receive
the progress notification (revision R) before its own events below R. A client that trusts the
notification ("every event up to R has been delivered") then misses those events: on one stream,
`RequestProgress` followed by `Watch(WithRev(old))` is enough, while the member still has responses
queued for the stream.

**Expected:** a progress notification at revision R on a watch should mean the watch has received
every event of its range up to R, as `rpc.proto` says of a progress response ("all future events
received in this stream" have a higher revision) and as `clientv3.WithProgressNotify` and
`RequestProgress` document; a watch created after the progress request was answered should not
receive it.

**Impact:** any client that sends a progress request and then creates a watch from a past revision
on the same stream, while the stream is busy; the Go client shares one stream among all watches with
the same context metadata and broadcasts a progress response to every watch it holds when the
response arrives. Readers that serve reads from a watch's progress (Kubernetes' watch cache with
`RequestProgress`, etcd's own `cache` package) can serve a stale read. Two further consequences,
each with its own test: etcd's `cache` answers a watch "from now" with a spurious `ErrCompacted`
([cache-stale-progress-compacts-newest-watch](cache-stale-progress-compacts-newest-watch.md)), and
the Go client resumes a watch from a future revision below its start after a reconnect
([etcd-watch-resume-below-start-revision](etcd-watch-resume-below-start-revision.md)). Reproduced at
`main`; release branches not checked.

**Reproduction:** `TestV3WatchProgressBeforeCreated` in
[`issues/etcd-watch-progress-before-created/watch_progress_before_created_test.go`](etcd-watch-progress-before-created/watch_progress_before_created_test.go),
copied into `tests/integration/clientv3/watch` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3 linux/amd64. Over one
raw watch stream: put `b` (revision 2), watch `a`, put `a` ten times with 100 KiB values without
reading, send a progress request, create a watch on `b` from revision 2, then read.

```
$ go test ./integration/clientv3/watch/ -run '^TestV3WatchProgressBeforeCreated$' -count=1
--- FAIL: TestV3WatchProgressBeforeCreated (0.23s)
    watch_progress_before_created_test.go:87:
        	Error:      	Should be false
        	Messages:   	progress response at revision 12 after the created response of the watcher on b, before its event at revision 2
FAIL
```

**Cause:** `recvLoop` answers a progress request by queuing mvcc's progress response on the watch
channel
([L395-L400](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3rpc/watch.go#L395-L400)),
computed over the watchers the stream has then, and a later create by queuing the created response on
`ctrlStream`
([L367](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3rpc/watch.go#L367)).
`sendLoop` takes from the two channels in either order
([L435](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3rpc/watch.go#L435),
[L514](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3rpc/watch.go#L514)),
so the created response can go first, and the client
[broadcasts](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/watch.go#L737-L738)
the later progress response to the new watch, which it does not cover.

## Proof

yes: the verified fork carries the fix (`upamanyus/etcd` `09669450f`, cherry-picked from
`c267e0ffe`): `sendLoop`'s proof states mvcc's progress response for the watchers registered when it
is computed, and the client's broadcast contract needs it sent before any later created response
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvWatchStream.lean`).

## Fix

**Branch**: `fix/etcd-watch-progress-before-created` in `~/etcd-fixes/etcd-watch-progress-before-created` (upamanyus/etcd, not pushed): 983eb5c36 test, 165c936b6 fix
**Base**: etcd-io/etcd@3aaab3479b6c4f5fe1b2b8f33437093c2caae88a

**PR draft**:

Title: etcdserver: send queued progress responses before a created response

`recvLoop` answers a progress request by queuing mvcc's progress response on the watch channel ([L395-L400](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/api/v3rpc/watch.go#L395-L400)), and a later create request by queuing the created response on `ctrlStream` ([L367](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/api/v3rpc/watch.go#L367)). `sendLoop` takes from the two in either order ([L435](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/api/v3rpc/watch.go#L435), [L514](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/api/v3rpc/watch.go#L514)), and the client [passes](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/client/v3/watch.go#L737-L738) a progress response arriving after the created response to the new watch, which it does not cover. This PR makes `sendLoop` send the responses already on the watch channel before a created response.

Fixes: the issue, once filed.

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

This PR changes `sendLoop`, as the fix of the watch ID reuse issue (#22673) does; whichever merges second needs a rebase in which every response taken from the watch channel, including those taken before a created response, is counted and checked for a canceled watcher. I can combine both fixes in one PR if you prefer.

**If a reviewer asks**: the drain is bounded by `len(Chan())` at the created response (upstream's
style; the fork drains until empty, which its proof needed). Alternatives: answer progress requests on
`ctrlStream`, or have `recvLoop` wait until the progress response is sent (blocks request handling),
or have the client broadcast only to watches created before the request (does not help other
clients). The other PR is [etcd-watch-id-reuse-stale-events](etcd-watch-id-reuse-stale-events.md)'s;
a plain merge of the two is textually clean but wrong (this drain bypasses that fix's counting);
the resolution, moving the counting into `sendWatch`, is the local branch
`merge/etcd-watch-progress-and-id-reuse` (`e970b7079`).

## Notes

`rpc.proto`'s wording ("all future events received in this stream") cannot hold for a watch created
later from an earlier revision; the issue draft asks whether it should say "the watches created
before the progress request".
