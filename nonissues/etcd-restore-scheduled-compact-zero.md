---
upstream: none
checked: 2026-11-02
links:
  - etcd-io/etcd#17780 issue closed: related, not this bug (the same restore path: a crash during a compaction made the revision go back; fixed by reading the scheduled record for the current revision)
blocks-proof: no
---

# mvcc: a member restored mid-way through a compaction at revision 0 has compaction revision -1, where the others have 0

A client's `Compact(0)` on a fresh cluster sets every member's compaction revision to `0`. A member
restored from a backend in which that compaction is scheduled but not finished (a snapshot taken
while the compaction job runs, or a crash before its last batch is committed) comes back with
compaction revision `-1` and does not resume it: `restore()` reads the scheduled revision `0` as
"no scheduled compaction". The members then differ: a re-issued `Compact(0)` succeeds on one and
fails with `ErrCompacted` on the others, and `HashKV` reports different compact revisions (which
the periodic corruption check, when enabled, reads as a follower ahead of its leader if the leader
is the restored member).

**Why not an issue:** reached only by a client's explicit `Compact(0)` as a cluster's first
compaction, followed by a crash or a snapshot inside that compaction's short job; no etcd
compactor issues `Compact(0)` (the periodic one compacts at a revision it read, at least `1`; the
revision one skips revisions at or below `0`), it deletes nothing, and the
next compaction at a positive revision makes the members agree again. The test builds the
unfinished-compaction backend by hand.

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; `EtcdServer.Compact.spec` takes the scope restriction `1 ≤ r` (no compaction at revision `0`,
`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Compact.lean`), which etcd does not enforce;
without it, `store.Restore`'s premise `c ≤ c'` is false in this corner.

## Notes

`TestRestoreScheduledCompactZero` in
[`nonissues/etcd-restore-scheduled-compact-zero/restore_scheduled_compact_zero_test.go`](etcd-restore-scheduled-compact-zero/restore_scheduled_compact_zero_test.go)
(copied into `server/storage/mvcc`) fails at etcd-io/etcd@a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5
(2026-11-02, go1.27.3):

```
$ (cd server && go test ./storage/mvcc -run '^TestRestoreScheduledCompactZero$' -count=1)
    restore_scheduled_compact_zero_test.go:57: after Restore: compactMainRev = -1, want 0 (the log's compaction revision)
    restore_scheduled_compact_zero_test.go:60: after Restore: re-issued Compact(0) = <nil>, want ErrCompacted (as on the member that applied it)
--- FAIL: TestRestoreScheduledCompactZero (0.03s)
```

A fix: resume when the scheduled record is found and above the compaction revision (use
`UnsafeReadScheduledCompact`'s found flag), or reject `Compact` at a revision `≤ 0` (it deletes
nothing). A test through a cluster (a member crashing in the job, with a failpoint such as
`compactBeforeSetFinishedCompact`) could promote it, if the false corruption alarm is judged worth
reporting.
