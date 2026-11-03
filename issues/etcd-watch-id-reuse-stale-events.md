---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#22673 issue open: this bug, filed by someone else 2026-10-30 (with the retained-pending consequence, nonissues/etcd-watch-canceled-pending-retained.md)
  - etcd-io/etcd#22674 pr open: failing tests for #22673 (no fix)
  - etcd-io/etcd#21880 pr open: grpc-proxy honors the client's WatchId (#12819); related, not a fix: with it the bug would also reach clients behind the proxy
  - etcd-io/etcd#21065 pr open: in-process watch deadlock when recvLoop blocks (#18879, #20716); related, not a fix: why our fix's creates wait only on streams with client-chosen ids
blocks-proof: no
---

# watch: a watch created with the ID of a canceled watch receives the canceled watch's queued events

On one watch stream, a client that cancels watch X and creates a new watch with the same ID X (set by
the client, or assigned by the member when an earlier explicit ID is reused) can receive, on the new
watch, events of the canceled watch that were still queued at the member: events of another key, at
revisions below the new watch's start.

**Reproduction:** `TestV3WatchReuseCanceledID` in
[`issues/etcd-watch-id-reuse-stale-events/watch_reuse_canceled_id_test.go`](etcd-watch-id-reuse-stale-events/watch_reuse_canceled_id_test.go),
copied into `tests/integration/clientv3/watch` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3 linux/amd64. Over one
raw watch stream: watch 1 on `a`, twenty 50 KiB puts of `a` without reading, cancel 1, create 1 on
`b` from the next revision, put `b`.

```
$ go test ./integration/clientv3/watch/ -run '^TestV3WatchReuseCanceledID$' -count=1
--- FAIL: TestV3WatchReuseCanceledID (0.19s)
    watch_reuse_canceled_id_test.go:85:
        	Error:      	Not equal:
        	            	actual  : []string{"a", "a", "a", "a", "a", "a", "a", "a", "a", "a", "a", "a", "a", "a", "a", "b"}
        	Messages:   	events received after watcher 1 was created on b
FAIL
```

## Proof

no: `sendLoop`'s proof attributes each mvcc response to its watcher, not to its ID
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/WatchSendModel.lean`), and the client hop does
not identify a watch by its ID across a cancel; the Go client never sets `WatchId`.

## Fix

**Branch**: `fix/etcd-watch-id-reuse-stale-events` in `~/etcd-fixes/etcd-watch-id-reuse-stale-events` (upamanyus/etcd, not pushed; the fork has the older 97aa6191d under this name): d6f96d4cb test, 2e9028084 fix
**Base**: etcd-io/etcd@3aaab3479b6c4f5fe1b2b8f33437093c2caae88a

**PR draft**:

Title: etcdserver: do not send a canceled watcher's events to a reused watch ID

`sendLoop` takes mvcc's watch responses and the created and canceled responses in either order ([L433-L435](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/api/v3rpc/watch.go#L433-L435), [L514](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/api/v3rpc/watch.go#L514)). It buffers a response whose watch ID is not announced until that ID's created response ([L470-L476](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/api/v3rpc/watch.go#L470-L476), [L538-L553](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/api/v3rpc/watch.go#L538-L553)), assuming, as its comment says, that the ID is "not yet announced". After a cancel ([L534-L537](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/api/v3rpc/watch.go#L534-L537)), the ID's queued responses are the canceled watcher's, and a new watcher with that ID receives them. This PR drops a canceled watcher's queued responses and, on a stream where the client has set a watch ID, makes a create wait until they are taken.

Fixes #22673

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

This PR changes `sendLoop`, as the fix of the progress-response ordering issue (a progress response overtaken by a created response) does; whichever merges second needs a rebase in which every response taken from the watch channel, including those taken before a created response, is counted and checked for a canceled watcher. I can combine both fixes in one PR if you prefer.

**If a reviewer asks**: dropping `pending[X]` on cancel alone is not enough (still fails 10 of 10:
most stale responses are taken after the new created response and sent directly). Creates wait only
on streams where the client has set `WatchId`, because a wait on every stream would bring back the
in-process deadlock of #20716. Alternatives: tag mvcc responses with the watcher (changes mvcc's
`WatchStream` API), reject a create of a draining ID (the client cannot know when to retry), or a
documentation-only rule in `rpc.proto` (a stream sets `watch_id` on every create or on none, and
never reuses a canceled one), which the user suggested on 2026-10-23 and the issue draft asked the
maintainers about. The sibling PR is
[etcd-watch-progress-before-created](etcd-watch-progress-before-created.md)'s; the merge resolution
is the local branch `merge/etcd-watch-progress-and-id-reuse` (`e970b7079`).

## Notes

#22673 was filed by someone else after our draft was ready; our branch can go up as the fix PR for
it. The Go client and `etcdctl` never set `WatchId`, so Kubernetes is not affected; a stream mixing
an explicit ID with automatic ones can get the canceled ID reassigned by the member (mvcc's
`nextID` skips only live IDs), reproduced 10 of 10 on 2026-10-21 with a scratch variant of the test.
