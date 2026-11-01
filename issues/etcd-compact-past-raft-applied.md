---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#9079 issue closed: the same panic message (etcd 3.1.9), but after raft restored a leader snapshot, not etcd's compaction; closed as stale
  - etcd-io/etcd#12134 pr merged: made MsgTimeoutNow go through the unapplied conf-change scan that panics here; related, not this bug
  - etcd-io/etcd#7470 issue closed: compaction racing an incoming snapshot; related, different path
  - etcd-io/etcd#18825 pr merged: in-memory snapshots every 100 entries (v3.6.0), which make the restart trigger reachable with default settings
  - etcd-io/etcd#17098 issue closed: proposes compacting the raft log after every apply (#18459 closed, unmerged); would widen this window to every batch
blocks-proof: yes
---

# etcdserver: a restarted member panics on a leader transfer to it while it applies the entries replayed from its WAL

A member that has just restarted, and is applying the entries it replays from its WAL, panics if a
leader transfer to it (or an election it starts) lands in a short window after it applies a batch:
`error scanning unapplied entries [1, 159): requested index is unavailable due to compaction`. Only
that member crashes, and a restart recovers it.

**Expected:** the member should take the leadership or refuse the transfer, and keep serving, as
raft's [`MemoryStorage.Compact`](https://github.com/etcd-io/raft/blob/b867cf13f6bc0dae21204302df97bc2355c3af55/storage.go#L265-L267)
requires of the application ("It is the application's responsibility to not attempt to compact an
index greater than raftLog.applied").

**Impact:** default configuration, any cluster size. A member restarted with no snapshot on disk
(fewer than `--snapshot-count` entries since the last one) and more than 100 entries to replay
compacts its raft log above raft's applied index while it applies the first batch; a
`MoveLeader` to it or an election timeout in that window crashes it. In steady state the window
opens only for a batch of more than `--snapshot-catchup-entries` (5000) entries. The window is
short (from the end of a batch's apply to raft's `Advance`); how often it is hit without a
failpoint was not measured. Affects v3.6 and later (the in-memory snapshots of #18825).

**Reproduction:** `TestMoveLeaderToRestartedMember` in
[`issues/etcd-compact-past-raft-applied/move_leader_restarted_test.go`](etcd-compact-past-raft-applied/move_leader_restarted_test.go),
copied into `tests/integration` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef
(2026-10-28), go1.27.3, after `gofail enable server/etcdserver/` (gofail v0.2.0, as `make
gofail-enable`); it widens the window with the existing failpoint `raftBeforeFollowerSend`:

```
$ (cd tests && go test ./integration -run '^TestMoveLeaderToRestartedMember$' -count=1)
panic: error scanning unapplied entries [1, 159): requested index is unavailable due to compaction
go.etcd.io/raft/v3.(*raft).hasUnappliedConfChanges(0x33fd740f3200)
	/home/ubuntu/go/pkg/mod/go.etcd.io/raft/v3@v3.7.0/raft.go:1018 +0x1cc
go.etcd.io/raft/v3.(*raft).hup(0x33fd740f3200, {0x10148ca, 0x10})
	/home/ubuntu/go/pkg/mod/go.etcd.io/raft/v3@v3.7.0/raft.go:983 +0x105
go.etcd.io/raft/v3.stepFollower(0x33fd740f3200, 0x33fd75a2c0d0)
	/home/ubuntu/go/pkg/mod/go.etcd.io/raft/v3@v3.7.0/raft.go:1763 +0x5df
FAIL	go.etcd.io/etcd/tests/v3/integration	1.086s
```

**Cause:** for each `Ready`, `raftNode.start` hands the committed entries to the apply loop
([raft.go#L232](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/raft.go#L232)),
signals `notifyc`, and only then calls `Advance`
([raft.go#L331](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/raft.go#L331)),
which moves raft's applied index. `applyAll` waits only for `notifyc` before
`snapshotIfNeededAndCompactRaftLog`
([server.go#L989-L991](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/server.go#L989-L991)),
which compacts at `appliedi - SnapshotCatchUpEntries`, or at 1
([server.go#L2146-L2150](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/server.go#L2146-L2150)):
after a restart raft's applied index is 0. A campaign in between runs `hasUnappliedConfChanges`,
which scans from the applied index and panics on `ErrCompacted`
([raft.go#L995-L1018](https://github.com/etcd-io/raft/blob/b867cf13f6bc0dae21204302df97bc2355c3af55/raft.go#L995-L1018)).

## Proof

yes: the verified fork carries the fix below (`goose-lean` `06aa6e6e`): raft publishes the floor the
application may compact to, which `applyAll` waits for (`notes/audit.md`; `notes/decisions.md`, D19i).

## Fix

**Branch**: `fix/etcd-compact-past-raft-applied` in `~/etcd-fixes/etcd-compact-past-raft-applied` (upamanyus/etcd, not pushed): e0846e9f3 test, 70f92483e fix
**Base**: etcd-io/etcd@3aaab3479b6c4f5fe1b2b8f33437093c2caae88a

**PR draft**:

Title: etcdserver: compact the raft log only after raft advances

After applying a batch of entries, [`applyAll`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/server.go#L986-L991) waits for the raft routine to persist them and then [compacts the raft log](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/server.go#L2144-L2150). The raft routine calls [`Advance`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/raft.go#L330-L336) only after that, so the compaction can pass raft's applied index, which [`MemoryStorage.Compact`](https://github.com/etcd-io/raft/blob/b867cf13f6bc0dae21204302df97bc2355c3af55/storage.go#L265-L267) forbids; a campaign in between [scans the log from the applied index](https://github.com/etcd-io/raft/blob/b867cf13f6bc0dae21204302df97bc2355c3af55/raft.go#L1002-L1018) and panics. This PR closes `raftAdvancedC` after every `Advance`, and `applyAll` waits for it before compacting.

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

**If a reviewer asks**: raft tolerating `ErrCompacted` in the scan would skip unapplied conf
changes and needs a raft release; bounding the compact index by the applied index before the
batch keeps the window; `Advance` before `notifyc` is wrong for a follower's conf changes. The new
wait cannot deadlock or block shutdown (the raft routine reaches `Advance` before the scheduler's
`Stop` returns) and costs no throughput (the next batch waits for this `Advance` anyway).

## Notes

A restart clears the crash (checked 2026-10-23: the panicked member's data directory restarts with
every applied entry and campaigns without panicking), but each restart with no disk snapshot reopens
the window (code reading); no crash loop is expected.
