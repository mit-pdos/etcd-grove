---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#13777 issue closed: related, not this bug (stabilizing the compaction-batch-limit flag; no validation discussed)
blocks-proof: yes
---

# mvcc: a negative --compaction-batch-limit makes every compaction run forever

With `--compaction-batch-limit` set to a negative number, which etcd accepts without a warning, the
first compaction never finishes: it rescans the compacted range in a loop, force-committing the
backend every 10 ms, never records that it finished, and every later compaction waits behind it, so
the database is never compacted again.

**Expected:** the flag should be rejected at startup, as etcd's
[`Config.Validate`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/embed/config.go#L1022-L1024)
rejects a non-positive `--compact-hash-check-time`, or read as the default, as `0` is; its help
("Sets the maximum revisions deleted in each compaction batch") gives a negative value no meaning.

**Impact:** only a member started with a negative value, a misconfiguration; nothing is lost, but
compaction (manual or automatic) silently stops working, so the database grows until the space
quota alarm, and the `Compact` call that started it never returns when `physical` is set. All
releases since the flag was added.

**Reproduction:** `TestCompactionNegativeBatchLimit` in
[`issues/etcd-compaction-negative-batch-limit/compaction_negative_batch_limit_test.go`](etcd-compaction-negative-batch-limit/compaction_negative_batch_limit_test.go),
copied (as `zz_compaction_negative_batch_limit_test.go`) into `server/storage/mvcc` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3; the flag's value
reaches `StoreConfig.CompactionBatchLimit` unchanged:

```
$ (cd server && go test ./storage/mvcc -run '^TestCompactionNegativeBatchLimit$' -count=1)
--- FAIL: TestCompactionNegativeBatchLimit (5.03s)
    --- FAIL: TestCompactionNegativeBatchLimit/limit=-1 (5.00s)
        zz_compaction_negative_batch_limit_test.go:48: compaction with batch limit -1 still running after 5s
FAIL
```

**Cause:** `NewStore` replaces only a zero limit by the default
([kvstore.go#L91](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/storage/mvcc/kvstore.go#L91)),
and the flag is an unvalidated `fs.IntVar`
([config.go#L739](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/embed/config.go#L739)).
The compaction job reads batches of `batchNum` keys and stops when a batch has fewer than `batchNum`
([kvstore_compaction.go#L47-L68](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/storage/mvcc/kvstore_compaction.go#L47-L68));
the backend reads a non-positive limit as no limit
([batch_tx.go#L207](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/storage/backend/batch_tx.go#L207)),
and no length is below a negative number, so the loop never exits.

## Proof

yes: `NewStore`'s spec takes `0 ≤ cfg.CompactionBatchLimit` as a premise, which etcd's flag
handling does not ensure (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/NewStore.lean`).

## Fix

`Config.Validate` rejects `CompactionBatchLimit < 0` (beside the `--compact-hash-check-time` check),
and `NewStore` defaults a limit `<= 0`, for library users of `mvcc`.

## Notes

Triage of the sibling flags (2026-10-23): `Validate` rejects the values that crash or wedge the
server (zero heartbeat/election, non-positive `--compact-hash-check-time`, an unknown compaction
mode); this is the only `int` flag whose negative value hangs the server's work. Other unvalidated
negatives: `--corrupt-check-time` (a startup panic), `--downgrade-check-time` and
`--backend-batch-interval` (busy loops); one PR could cover them.
