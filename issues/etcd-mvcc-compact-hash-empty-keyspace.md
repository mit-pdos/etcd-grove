---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#22517 issue open: related, same `len(h.keep) > 0` rule with a different trigger (a member still running a compaction; etcd-mvcc-hashkv-during-compaction-empty-keyspace), not this one
  - etcd-io/etcd#22515 pr open: fix for #22517; does not fix this one (the test here still fails with it applied)
blocks-proof: no
---

# mvcc: when every key has been deleted, a follower that has not yet applied a compaction reports a different hash than the leader's compaction hash

If every key was deleted between two compactions, the hash a member stores when it compacts at
revision R differs from the hash `HashKV` returns at R on a member with the same data that has not
yet applied that compaction, although both report the same revision and compact revision. With the
compaction hash check enabled, the leader takes the follower's hash for a sign of corruption and
raises the cluster-wide `CORRUPT` alarm.

**Expected:** the two hashes should be equal: the compaction hash check "raises alarm if 2 or more
members at the same compact revision have different hashes"
([`CompactHashCheck`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/server/etcdserver/corrupt.go#L266-L276)),
and mvcc's own
[`TestCompactionHash`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/server/storage/mvcc/testutil/hash.go#L72-L82)
asserts that `HashByRev(R)` before `Compact(R)` equals the hash stored by it (on histories that
always leave a key).

**Impact:** clusters with the `CompactHashCheck` feature gate on (alpha, off by default) in which
the whole keyspace is deleted between two compactions (some key live at the previous compaction,
none at the new one). When the leader checks a stored compaction hash while a follower has applied
the deletes but not yet the compaction request (apply lag), it compares the two hashes and
[`checkPeerHashes`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/server/etcdserver/corrupt.go#L302-L390)
logs "Detected compaction hash mismatch" and raises `CORRUPT`: for the lagging followers if the
other members are a majority, for the leader (and the members agreeing with it) if the lagging
followers are a majority, for member 0 (the whole cluster) if there is no majority, e.g. in a
2-member cluster. While the alarm is active every member rejects puts, ranges, deletes, txns,
compactions and lease grants with `etcdserver: corrupt cluster`. By reading, not reproduced end to
end; the test reproduces the two hashes. Reproduced on `main`; release branches not checked.

**Reproduction:** `TestHashByRevMatchesCompactionHashWhenKeyspaceEmpty` in
[`issues/etcd-mvcc-compact-hash-empty-keyspace/hash_empty_keyspace_test.go`](etcd-mvcc-compact-hash-empty-keyspace/hash_empty_keyspace_test.go),
copied (as `zz_hash_empty_keyspace_test.go`) into `server/storage/mvcc` at
etcd-io/etcd@d622ec57cf46c119f1a550343c34b26327cead0f (2026-11-06), go1.27.3 linux/amd64 (two
stores with the same history: put `foo` at 2, compact at 2, delete `foo` at 3; the leader compacts
at 3 and stores its hash; the follower answers `HashByRev(3)`):

```
$ (cd server && go test ./storage/mvcc -run '^TestHashByRevMatchesCompactionHashWhenKeyspaceEmpty$' -count=1)
--- FAIL: TestHashByRevMatchesCompactionHashWhenKeyspaceEmpty (0.02s)
    zz_hash_empty_keyspace_test.go:62:
        	Error:      	Not equal:
        	            	expected: 0x41898927
        	            	actual  : 0x94693eb5
        	Test:       	TestHashByRevMatchesCompactionHashWhenKeyspaceEmpty
        	Messages:   	same revision and compact revision should give the same hash
FAIL
```

**Cause:** [`kvHasher.WriteKeyValue`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/server/storage/mvcc/hash.go#L69-L76)
skips a revision at or below the compact revision that is not in `keep` only when `keep` is
non-empty. The compaction hashes with `keep` from
[`kvindex.Compact(R)`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/server/storage/mvcc/kvstore_compaction.go#L35-L47),
which holds the tombstones at R and so is non-empty, while
[`hashByRev`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/server/storage/mvcc/kvstore.go#L196)
uses `kvindex.Keep(R)`, which
[drops a tombstone at R](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/server/storage/mvcc/key_index.go#L237-L256)
and so is empty when no key exists at R. The compaction hash then skips the revisions the previous
compaction kept (`foo`'s put at 2), and the follower's `HashByRev` hashes them.

## Proof

no: the corruption checker is outside the proved results, and the mvcc proof treats a hash as an
opaque value (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/kvHasher__WriteKeyValue.lean`; `HashByRev`
has no spec yet, `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`, "Still out").

## Fix

Hash the compaction with the keep set `HashByRev` uses: compute `kvindex.Keep(R)` before
`kvindex.Compact(R)` in `scheduleCompaction` and pass it to the hasher (the deletion keeps using
`Compact`'s set). When `Keep(R)` is non-empty the two sets differ only in tombstones at R, above
the previous compact revision, so the stored hashes of other histories stay as they are. Tried at
the same commit: the test passes, and so does the rest of `./storage/mvcc` (`TestHashByRevValue`'s
fixed hashes, `TestCompactionHash`) except `TestScheduleCompaction` and `TestStoreCompact`, which
hang because their fake index answers `Keep` and `Compact` from one queued response; with #22515
applied as well, this test, #22517's and #22515's own pass. Making `WriteKeyValue` filter with an
empty `keep` too would instead change `HashByRev` after a finished compaction, which mixed-version
clusters compare (the reason #22515 gives for not doing it).

## Notes

Found by the cross-member hash check of this repository's randomized mvcc tester
(`examples/mvccfull`). The same `len(h.keep) > 0` rule makes `HashByRev` depend on how far a
running compaction has gone ([`etcd-mvcc-hashkv-during-compaction-empty-keyspace`](etcd-mvcc-hashkv-during-compaction-empty-keyspace.md),
etcd-io/etcd#22517); its fix, #22515, filters an empty `Keep(R)` with `Keep(compactRev)`, which keeps
the revisions the previous compaction kept, so this test fails with it applied too.
