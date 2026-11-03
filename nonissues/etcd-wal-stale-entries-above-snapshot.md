---
upstream: none
checked: 2026-11-02
links:
blocks-proof: yes
---
# etcd: a member restarted after installing a snapshot gets back the log entries the snapshot discarded

A follower whose log holds uncommitted entries of an old term above index `k`, and which then
installs a leader's snapshot at `k` of a later term, discards those entries in memory (raft's
`raftLog.restore`, `MemoryStorage.ApplySnapshot`). Its WAL keeps them: `wal.ReadAll` returns every
entry record whose index is above the start snapshot's, wherever the record sits relative to the
snapshot record (`server/storage/wal/wal.go`, `ReadAll`: `if e.GetIndex() > w.start.GetIndex()`).
If the member restarts before any entry above `k` reaches it (an appended entry truncates the
stale ones in `ReadAll`), `bootstrap` rebuilds its `MemoryStorage` as the snapshot at `k` (term `t`)
followed by the old entries, whose terms are below `t`: a log whose terms go down, unlike any log
raft builds.

**Why not an issue:** the test shows the WAL's behavior with etcd's own sequence of calls (the
raft loop's `SaveSnap` of a received snapshot, then `Save` of its hard state with no entries), but
no harm at the raft level has been shown: the restarted member's last term is lower than its
snapshot's, so it is less up to date in elections (it may grant votes a member holding only the
snapshot would refuse), and a leader's next append overwrites the stale tail. Whether a vote it
should have refused can elect a leader missing a committed entry is open.

`TestReadAllKeepsEntriesAboveLaterSnapshot` in
[`nonissues/etcd-wal-stale-entries-above-snapshot/wal_stale_test.go`](etcd-wal-stale-entries-above-snapshot/wal_stale_test.go),
run in `examples/` (whose `go.mod` replaces etcd by the goosed fork, `etc/goose.py`'s pin; the WAL
code is upstream's), go1.27.1, fails:

```
wal_stale_test.go:50: entry index 4 term 1
wal_stale_test.go:50: entry index 5 term 1
wal_stale_test.go:52: hard state term 2 commit 3
wal_stale_test.go:54: ReadAll after a snapshot at 3 (term 2) returned 2 entries of the old log above it
```

Upstream not searched (no GitHub access from the session that found it, 2026-11-02).

**The fork's fix** (branch `goose-lean-walsnap` of `upamanyus/etcd`, on the pin `ab3c28d9a`; the
user's choice, 2026-11-02; `6293455e0`, revised by `ce3dbc097` after review): `ReadAll` reads the
records as the log they write. An entry written at or below the start snapshot's index truncates
the entries above it (`ReadAll` ignored such writes, a second way to keep stale entries), and at
the start snapshot's record the entries above it go when the snapshot is above the commit index
saved before it: exactly a received snapshot (raft installs one only past its commit; the server's
own snapshots are of applied entries). The first version decided by the WAL's entry at the
snapshot's index, but raft decides on its in-memory log, which a newer leader's appends may have
changed. `ReadAll` also restores the WAL's hard state, which a cut repeats at the head of the next
file. Tests in `server/storage/wal/wal_test.go` (`TestReadAllDropsEntriesAReceivedSnapshotDiscards`,
`TestReadAllDropsEntriesAboveReceivedSnapshotTheWALMatches`, `TestReadAllTruncatesAtEntryBelowStart`,
`TestReadAllRestoresState` fail without the fix; `TestReadAllKeepsEntriesAboveOwnSnapshot`).

## Proof

yes: the restart plan's image of a stopped member (`srvDiskImage`, `InvRestart.lean`) says the WAL's
records hold the node's durable state (`StorageHolds S σ`, what raft's `RestartNode` checks), and
raft's durable state after a snapshot has no entries above it (`RaftState.next`). A member stopped
in the window above has WAL records with the stale tail, so the image is false of it, and the
durability of a restart (R2b-1, `notes/restart-plan.md`) cannot be proved as stated. Found while
drafting R2b-1 (2026-11-02); the proof needs the fork's fix above (the user's choice among the
options in `notes/restart-plan.md`, "R2b-1: the WAL's records"), whose `ReadAll` the WAL's
trust-boundary model describes.
