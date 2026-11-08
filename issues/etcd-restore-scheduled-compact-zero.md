---
upstream: none
checked: 2026-11-04
links:
  - etcd-io/etcd#17780 issue closed: related, not this bug (the same restore path: a crash during a compaction made the revision go back; fixed by reading the scheduled record for the current revision)
blocks-proof: no
---

# mvcc: a member that crashes during a compaction at revision 0 restarts with compact revision -1, and the corruption check then alarms

After a client's `Compact(0)` on a cluster that has never been compacted, a member that crashes
before its compaction job records the compaction as finished restarts with compact revision `-1`,
where the other members have `0`, and does not resume the compaction. The members then disagree:
`HashKV` reports different compact revisions, a re-issued `Compact(0)` succeeds through that member
but is refused as compacted by the others, and with the periodic corruption check on, once that
member is the leader, the check raises a `CORRUPT` alarm and the cluster refuses writes, although
no member's data differs.

**Expected:** a member restarted after a crash during a compaction should resume it and come back
with the compact revision of the members that applied it, as it does for a compaction at any
revision above `0` (`restore` resumes the scheduled compaction, the fix of
[#17780](https://github.com/etcd-io/etcd/issues/17780)); `HashKV`'s
[`compact_revision`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/api/etcdserverpb/rpc.proto#L728-L729)
is what the corruption check compares between members.

**Impact:** a cluster whose first compaction is a client's explicit `Compact(0)` (accepted, and
it deletes nothing; no etcd compactor issues it: the periodic one compacts at a revision it read,
the revision one skips revisions at or below `0`), with a member crashing inside the window
between the compaction being persisted as scheduled and the finished record being committed
(the job's last batch, then up to the backend's commit interval, 100ms by default, for a
compaction that is not physical). By reading, not reproduced: a follower that installs a snapshot
taken in the same window (before the job's last batch) restores the same way. With
`--corrupt-check-time` (off by default) the false `CORRUPT` alarm stops writes on the whole cluster
until it is disarmed; without it, the disagreement lasts until the next compaction at a positive
revision. Reproduced on `main`; release branches not checked.

**Reproduction:** `TestCompactZeroCrashCompactRevision` and `TestCompactZeroCrashCorruptAlarm` in
[`issues/etcd-restore-scheduled-compact-zero/compact_zero_crash_test.go`](etcd-restore-scheduled-compact-zero/compact_zero_crash_test.go),
copied (as `zz_compact_zero_crash_test.go`) into `tests/e2e` at
etcd-io/etcd@4b0b745025716b893c64dbee443e3f969931a16b (2026-11-02), go1.27.3 linux/amd64, against
binaries built at that commit with failpoints enabled (`gofail enable` on `server/etcdserver/`,
`server/storage/backend/`, `server/storage/mvcc/`, as `tests/robustness/Makefile` does). A
3-member cluster, one put; the follower the client talks to panics at
`compactBeforeSetFinishedCompact` (as in `TestReproduce17780`) during `Compact(0)` and is
restarted; the second test then moves the leadership to it, with a 10s corruption check period:

```
$ (cd tests && go test ./e2e -run '^TestCompactZeroCrash' -count=1 -args -bin-dir=<failpoint binaries>)
--- FAIL: TestCompactZeroCrashCompactRevision (3.03s)
    zz_compact_zero_crash_test.go:64: compact revisions: [0 -1 0] (member 1 restarted)
    zz_compact_zero_crash_test.go:65:
        	Error:      	Not equal:
        	            	expected: 0
        	            	actual  : -1
        	Messages:   	the restarted member's compact revision should be the leader's
    zz_compact_zero_crash_test.go:70:
        	Error:      	An error is expected but got nil.
        	Messages:   	Compact(0) through the restarted member should be refused as compacted
--- FAIL: TestCompactZeroCrashCorruptAlarm (17.08s)
    zz_compact_zero_crash_test.go:116:
        	Error:      	Should be empty, but was [memberID:8279989642402899767 alarm:CORRUPT]
        	Messages:   	no member's data differs, so no alarm should be raised
    zz_compact_zero_crash_test.go:118:
        	Error:      	Received unexpected error:
        	            	etcdserver: corrupt cluster
        	Messages:   	writes should be accepted
FAIL
```

The restarted leader logs `compact revision from follower must be less than or equal to
leader's` with `leader-compact-revision: -1`, `follower-compact-revision: 0`. Three runs, the same
failures. Both tests pass with `fix.patch` applied.

**Cause:** [`updateCompactRev`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/kvstore.go#L207-L232)
accepts `Compact(0)` on a store never compacted (`0 > compactMainRev = -1`) and persists `0` as
the scheduled compaction revision. On restart,
[`restore`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/kvstore.go#L340-L352)
finds no finished record (so `compactMainRev` stays `-1`) and reads the scheduled one ignoring its
found flag; it then uses `0` as "no scheduled compaction"
([L399-L401](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/kvstore.go#L399-L401),
[L421](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/kvstore.go#L421)),
so the scheduled compaction at `0` is not resumed. Once the job has committed the finished record
(`0`), `restore` sets `compactMainRev = 0` and the members agree. The corruption check
[alarms](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/etcdserver/corrupt.go#L238-L246)
when a follower's compact revision is above the leader's.

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; `EtcdServer.Compact.spec`
takes the scope restriction `1 ≤ r` (no compaction at revision `0`,
`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Compact.lean`), which etcd does not
enforce; without it, `store.Restore`'s premise `c ≤ c'` is false in this corner, and the mvcc API's
snapshot image cannot be produced mid-job of `Compact(0)` (`image_crev0_impossible` in
`notes/mvcc-api-probes/SnapImageProbe.lean`): its snapshot law will take a premise or a weaker post.

## Fix

[`fix.patch`](etcd-restore-scheduled-compact-zero/fix.patch): in `restore`, decide whether to resume
with `UnsafeReadScheduledCompact`'s found flag instead of the value `0` (resume when the scheduled
record is present and above the restored compact revision). Alternatively, reject `Compact` at a
revision `≤ 0`, which deletes nothing; that would also close
[`etcd-mvcc-hashbyrev-zero-stored`](etcd-mvcc-hashbyrev-zero-stored.md).

## Notes

Another edge of a compaction at revision 0:
[`etcd-mvcc-hashbyrev-zero-stored`](etcd-mvcc-hashbyrev-zero-stored.md) (after `Compact(0)`,
`HashKV(0)` returns the stored hash of revision 0). The alarm test delays the first corruption
check until the restarted member leads because of it: an earlier check, by a leader that finished
the compaction, answers `HashKV(0)` from that stored hash and alarms through that bug instead (it
does so even with `fix.patch`). The first test asks `HashKV` at the put's revision, which no stored
hash has. Range and Watch are not affected: at revision `0` they read the latest revision, and no
revision above `0` is below either compact revision.

Until 2026-11-04 this was a non-issue: its test built the unfinished-compaction backend by hand in
`server/storage/mvcc`; the e2e test reaches it with a crash, as `TestReproduce17780` does.
