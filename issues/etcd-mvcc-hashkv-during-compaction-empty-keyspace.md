---
upstream: known
checked: 2026-11-09
links:
  - etcd-io/etcd#22517 issue open: same bug (HashKV changes while a compaction deletes every key)
  - etcd-io/etcd#22515 pr open: fix for #22517 (filter an empty Keep(rev) with Keep(compactRev)); the test here passes with it applied
blocks-proof: no
---

# mvcc: when no key exists at the hashed revision, HashKV depends on how far a running compaction has gone

If no key exists at the latest revision, two members that have applied the same compaction report
the same revision and compact revision but different `HashKV` hashes while one of them is still
removing the compacted revisions (in batches of `--experimental-compaction-batch-limit`, with
`--experimental-compaction-sleep-interval` between them). The periodic corruption check
(`--corrupt-check-time`) compares exactly these hashes.

**Reproduction:** `TestHashByRevIndependentOfCompactionProgressWhenKeyspaceEmpty` in
[`issues/etcd-mvcc-hashkv-during-compaction-empty-keyspace/hash_compaction_progress_test.go`](etcd-mvcc-hashkv-during-compaction-empty-keyspace/hash_compaction_progress_test.go),
copied (as `zz_hash_compaction_progress_test.go`) into `server/storage/mvcc` at
etcd-io/etcd@d622ec57cf46c119f1a550343c34b26327cead0f (2026-11-06), go1.27.3 linux/amd64 (two
stores: put `a` at 2, put `b` at 3 and 4, delete `a` at 5 and `b` at 6, compact at 4; one finishes,
the other has `CompactionBatchLimit: 1` and an hour between batches, so revision 3 is still stored;
both hash the latest revision):

```
$ (cd server && go test ./storage/mvcc -run '^TestHashByRevIndependentOfCompactionProgressWhenKeyspaceEmpty$' -count=1)
--- FAIL: TestHashByRevIndependentOfCompactionProgressWhenKeyspaceEmpty (0.01s)
    zz_hash_compaction_progress_test.go:66:
        	Error:      	Not equal:
        	            	expected: 0xd983c16f
        	            	actual  : 0x5c724225
        	Test:       	TestHashByRevIndependentOfCompactionProgressWhenKeyspaceEmpty
        	Messages:   	same revision and compact revision should give the same hash
FAIL
```

## Proof

no: the corruption checker is outside the proved results, and the mvcc proof treats a hash as an
opaque value (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/kvHasher__WriteKeyValue.lean`; `HashByRev`
has no spec yet, `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`, "Still out").

## Notes

Found again by this repository's randomized mvcc tester (`examples/mvccfull`) while recording
[`etcd-mvcc-compact-hash-empty-keyspace`](etcd-mvcc-compact-hash-empty-keyspace.md), the same
`len(h.keep) > 0` rule reached through the compaction hash check, which #22515 does not fix. The
test passes with #22515 applied (checked at the same commit).
