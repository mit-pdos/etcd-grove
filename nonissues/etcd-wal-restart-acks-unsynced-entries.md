---
upstream: none
checked: 2026-11-06
links:
  - etcd-io/etcd#22709 issue open: related, different: ReadAll's ZeroToEnd is not fsynced (a machine crash at boot, not a process restart)
  - etcd-io/etcd#10219 issue closed: related, different: the "tocommit out of range" panic a follower that lost acknowledged entries hits
blocks-proof: no
---

# wal: a follower restarted without a sync acknowledges entries that are only in the page cache

A follower killed after writing entries to its WAL but before their `fdatasync`, and restarted
while the machine stays up, reads those entries back from the page cache and acknowledges them to
the leader without ever syncing them: they are already in its log, so the append is a no-op, raft's
`MustSync` is false and `WAL.Save` does not sync. A power loss before the segment's next sync or
writeback then loses entries the leader counted as replicated: the follower panics on the next
heartbeat ("tocommit(i) is out of range"), and an entry committed on that acknowledgement survives
only on the leader.

**Why not an issue:** no test, found by code reading (`notes/restart-vs-crash.md`, Q1(a)); it needs
a process restart without a sync followed by a power loss within the writeback window (~30 s),
which etcd's documentation does not exclude but no test harness here reaches.

## Execution

At upamanyus/etcd@673da07c (the pinned `goose-lean`, same lines as upstream `main` for the code
involved apart from the fork's comments) and its raft, upamanyus/etcd@565c2bd (raft v3.7.0 plus the
fork's fixes). Three voters L, F, G; G lagging or down.

1. L appends entry *i* (term *t*) and sends `MsgApp[i]` to F. F writes *i* into its last segment
   (`encoder.flush` in `WAL.sync`, `server/storage/wal/wal.go:906-910`) and is killed before
   `fileutil.Fdatasync` (`wal.go:918`). No acknowledgement was sent (the follower sends after
   `storage.Save` returns, `server/etcdserver/raft.go:264`, `:329`).
2. F restarts on the page cache. Nothing at boot syncs: `wal.Open`/`ReadAll` (`wal.go:351`,
   `:369-406`, `:478-623`) read through the page cache, `ReadAll` sets the WAL's saved hard state
   from what it read (`wal.go:602`), and raft's storage and `prevHardSt` are loaded from it. On F's
   next heartbeat response L, with F in `StateReplicate` at `Next = i+1`, sends an append
   (`raft.go:1611-1612`): empty at `{Index: i, LogTerm: t}`, or *i* again after a probe.
3. F's `handleAppendEntries` (`raft.go:1806-1818`) matches the log in `maybeAppend`
   (`log.go:109-131`), appends nothing and answers `MsgAppResp{Index: i}`. `MustSync`
   (`rawnode.go:191-198`) is false (no entries, term and vote unchanged), so `WAL.Save`
   (`wal.go:1032-1074`, `:1047`) writes the commit-only hard state and returns without syncing;
   the acknowledgement is sent.
4. L sets `Match(F) = i`, commits *i* on {L, F} and answers the client.
5. Power loss at F before its next sync of the segment (an idle follower sees only heartbeats and
   commit-only saves).
6. F restarts on the disk: *i* is gone. L's next heartbeat carries `commit ≥ i` and F's
   `raftLog.commitTo` panics (`log.go:322-326`) until L steps down; if L is then lost, F and G
   elect a leader without *i*, an acknowledged write lost.

Under machine crashes alone it cannot happen: an entry reaches raft's storage at boot only if it was
on disk.

## Proof

no: the Linux file extension assumes a restart follows a machine restart or a `sync(2)` of what
the old process left (`GooseLang/Ext/Fs/Impl.lean`, header "Restarts"), so a process restart is a
machine crash and every generation boots on a durable state; this execution is outside the
theorem, by that stated assumption.

## Fix

The note's proposal (`notes/restart-vs-crash.md`, Q7 and conclusion 4): `fdatasync` the WAL tail
(and `fsync` the WAL directory and its parent) at the end of `ReadAll`, or in
`openWALFromSnapshot` (`server/etcdserver/bootstrap.go:668`), before raft starts. That one sync
also closes `nonissues/etcd-wal-restart-purge-below-unsynced-snapshot.md` and
`nonissues/etcd-wal-restart-unsynced-renames.md`.

## Notes

A related, theoretical case of the same baseline (`notes/restart-vs-crash.md`, Q1(b)): a vote
written and not synced is re-granted after the restart without a sync, so after a power loss the
member can vote twice in one term; it needs the candidate's `MsgVote` delivered twice.
