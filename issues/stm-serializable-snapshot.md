---
upstream: none
checked: 2026-10-16
links:
blocks-proof: no
---

# concurrency: a retried Serializable STM attempt reads keys from two revisions

With the `Serializable` and `SerializableSnapshot` isolation levels of `client/v3/concurrency`'s
STM, an attempt that follows a failed commit can read some keys at the failed commit's revision and
others at a later one, so the STM function sees a combination of values that never existed in
etcd. The attempt's commit then fails and the STM retries, so nothing inconsistent is committed;
but the function runs, and acts, on that view.

**Expected:** every read of one attempt should return data from one revision, as the
[Go doc of `Serializable`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/concurrency/stm.go#L45-L50)
says: "reads within the same transaction attempt return data from the revision of the first read"
(`SerializableSnapshot` is documented as serializable plus write-conflict checks).

**Impact:** users of `concurrency.NewSTM` with the default isolation (`SerializableSnapshot`) or
`Serializable`, under contention (an attempt must fail and the read keys change again before the
retry). An STM function that assumes an invariant between keys (written together) can see it
broken: a division by zero, a panic, or a side effect outside etcd based on the impossible state.
Committed results stay serializable.

**Reproduction:** `TestSTMSerializableSnapshotAfterConflict` in
[`issues/stm-serializable-snapshot/stm_snapshot_test.go`](stm-serializable-snapshot/stm_snapshot_test.go),
copied into `tests/integration/clientv3/concurrency` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3 (`x` and `y` are only
ever written together with equal values; the first attempt's commit is made to fail, and both keys
change before the second attempt's first read):

```
$ go test ./integration/clientv3/concurrency -run '^TestSTMSerializableSnapshotAfterConflict$' -count=1
--- FAIL: TestSTMSerializableSnapshotAfterConflict (0.16s)
    --- FAIL: TestSTMSerializableSnapshotAfterConflict/SerializableSnapshot (0.15s)
        stm_snapshot_test.go:87: isolation 0, attempt 2 read x=2 y=1
            	Messages:   	isolation 0: an attempt read x=2 and y=1, written together only with equal values
    --- FAIL: TestSTMSerializableSnapshotAfterConflict/Serializable (0.01s)
        stm_snapshot_test.go:87: isolation 1, attempt 2 read x=2 y=1
            	Messages:   	isolation 1: an attempt read x=2 and y=1, written together only with equal values
FAIL
```

**Cause:** after a failed commit,
[`stmSerializable.commit`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/concurrency/stm.go#L347-L363)
keeps the `Else` branch's reads, at the commit's revision `r`, as the next attempt's prefetch and
clears the base revision. In the next attempt
([`stmSerializable.Get`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/concurrency/stm.go#L306-L330)),
a prefetched key is returned at `r`, while the first read of any other key goes to etcd at the
latest revision and sets the base revision there.

## Proof

no: the proved results are about the committed attempt (`stm_atomicity`: it ran atomically at its
commit's revision, `Proof/go_etcd_io/etcd/client/v3/concurrency/`), which holds; the specs claim no
single-revision view for an attempt that fails.

## Fix

**Branch**: `stm-serializable-snapshot` (upamanyus/etcd, pushed): 928618847 test and fix (one commit)
**Base**: etcd-io/etcd@f061acd0902d489041448cdd19d71a345d27b9f5

**PR draft**:

Title: clientv3/concurrency: read a retried serializable STM attempt at one revision

The serializable isolation levels promise that "reads within the same transaction attempt return
data from the revision of the first read". After a failed commit, `stmSerializable.commit` loads
the read set's keys, as read by the commit's `Else` branch at the commit's revision `r`, into
`s.prefetch`, and clears `s.getOpts`. In the next attempt, a first read of a key that is not
prefetched is a fresh read at the latest revision `r2` and sets the attempt's base revision to `r2`;
a later read of a prefetched key returns the value at `r`. If a transaction changed both keys in
`(r, r2]`, the attempt sees a state that never existed. The commit's comparisons then fail, so
serializability holds, but the closure ran on an inconsistent view.

This PR reads the next attempt at the revision of the prefetched reads (`WithRev` of the commit's
revision, serializable), and lets the first read set the base revision only when none is set. The
test makes two keys that are only written together, fails the first attempt's commit, changes both
keys before the second attempt's first read, and checks that the attempt read them from one
revision.

## Notes

Earlier parked as a documentation request (the 2026-10-23 review: "Skip for now"); promoted because
the test fails through the public API against the documented guarantee. The alternative fix is
documentation: the single-revision guarantee covers reads not served from a failed commit's
prefetch.
