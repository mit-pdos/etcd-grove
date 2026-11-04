---
upstream: known
checked: 2026-11-04
links:
  - etcd-io/etcd#22517 issue open: this bug (HashKV changes while a compaction deletes every key); no end-to-end false alarm reproduced there
  - etcd-io/etcd#22515 pr open: the fix for #22517 (filter with the compaction's keep set when `Keep(rev)` is empty)
  - etcd-io/etcd#20706 pr merged: related; the hashkv integration tests wait for every member's compaction before comparing hashes
blocks-proof: no
---

# mvcc: with the periodic corruption check on, compacting an empty key space raises a false CORRUPT alarm

On a member with the periodic corruption check enabled (`--corrupt-check-time`), when no key is live
at the current revision (every key deleted) and a compaction is deleting the old revisions from the
backend, `HashKV` of the same revision and compact revision changes with each compaction batch: the
leader's check sees its own two hashes differ and raises a CORRUPT alarm against itself, which makes
the cluster refuse writes. With one key live, the hash is stable and no alarm is raised.

**Reproduction:** `TestPeriodicCheckNoCorruptAlarmDuringCompaction` in
[`issues/etcd-mvcc-hashbyrev-empty-keyspace-compaction-progress/corrupt_compaction_test.go`](etcd-mvcc-hashbyrev-empty-keyspace-compaction-progress/corrupt_compaction_test.go),
copied (as `zz_corrupt_compaction_test.go`) into `tests/integration` at
etcd-io/etcd@4b0b745025716b893c64dbee443e3f969931a16b (2026-11-02), go1.27.3 linux/amd64: one member
restarted with the check every 20ms and a compaction batch of 1 (1ms apart), 2000 puts of one key,
its delete, a compaction at the delete's revision, then `AlarmList` polled for 10s; 8 of 8 runs fail
(`-count=5` and three single runs), and the same test with a second key left live passes (one run):

```
$ (cd tests && go test ./integration -run '^TestPeriodicCheckNoCorruptAlarmDuringCompaction$' -count=1 -v)
    logger.go:146: ... INFO	m0	compact tree index	{"member": "m0", "revision": 2002}
    logger.go:146: ... WARN	m0	found hash mismatch	{"member": "m0", "revision-1": 2002, "compact-revision-1": 2002, "hash-1": 754934624, "revision-2": 2002, "compact-revision-2": 2002, "hash-2": 1045421906}
    zz_corrupt_compaction_test.go:53: CORRUPT alarm raised on a healthy member during compaction: memberID:201926395449959763  alarm:CORRUPT
    logger.go:146: ... INFO	m0	finished scheduled compaction	{"member": "m0", "compact-revision": 2002, "took": "3.495868389s", "number-of-keys-compacted": 2000, ...}
--- FAIL: TestPeriodicCheckNoCorruptAlarmDuringCompaction (11.62s)
```

The store-level cause, deterministically: `TestHashByRevDuringCompaction` in
[`hashbyrev_compaction_test.go`](etcd-mvcc-hashbyrev-empty-keyspace-compaction-progress/hashbyrev_compaction_test.go),
copied into `server/storage/mvcc` at the same commit, holds the compaction job behind a job queued
first on the store's scheduler and calls `HashByRev(0)` before and after it:

```
$ (cd server && go test ./storage/mvcc -run '^TestHashByRevDuringCompaction$' -count=1)
--- FAIL: TestHashByRevDuringCompaction (0.01s)
    --- FAIL: TestHashByRevDuringCompaction/no_key_live (0.01s)
        zz_hashbyrev_compaction_test.go:75: HashByRev(0) at revision 21, compact revision 21: hash 2398553855 before the compaction job, 1084519789 after
```

**Cause:** [`kvHasher.WriteKeyValue`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/hash.go#L60-L90)
skips a revision at or below the compaction revision that the compaction does not keep only
`if ... len(h.keep) > 0`; [`hashByRev`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/kvstore.go#L177-L205)
passes `s.kvindex.Keep(rev)`, empty when no key is live at `rev`, so it hashes every compacted
revision still in the backend, and [`scheduleCompaction`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/kvstore_compaction.go#L28-L105)
deletes those in batches, after `Compact` has already set the compact revision both hashes report.
[`PeriodicCheck`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/etcdserver/corrupt.go#L179-L218)
alarms when `HashByRev(0)` before and after a linearizable read differ at the same revision and
compact revision; it also alarms against a follower at the leader's compact revision with another
hash ([L250](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/etcdserver/corrupt.go#L250)),
which a follower further along (or behind) in the same compaction reports.

## Proof

no: hashing is outside the verified results: `kvHasher.WriteKeyValue` is a trust-boundary spec that
leaves the hash opaque (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/kvHasher__WriteKeyValue.lean`),
no spec of `HashByRev` states a value, and no top-level result reads `HashKV` or the corruption alarms.

## Notes

The corruption check is off by default (`--corrupt-check-time` 0). The window is the physical
compaction (with the defaults, 1000 revisions per batch, 10ms apart, so it grows with the number of
revisions compacted); the test shrinks the batch so that a small key space has the same window. The
stored-hash path of `hashStorage.HashByRev` does not interfere: it matches `rev == h.Revision`, and
the check asks for revision 0. #22517 reports the `HashKV` change and the possible alarm but says it
did not reproduce the alarm end to end; this test does, and could go to #22517 as a comment.
