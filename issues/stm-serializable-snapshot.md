# concurrency: the STM's "revision of the first read" doc comment does not hold for retried attempts

## Summary

The `Serializable` isolation level of `client/v3/concurrency`'s STM is documented as "reads within the same transaction attempt return data from the revision of the first read", and `SerializableSnapshot` as that plus write-conflict checks. This holds for an attempt that follows a failed commit only for the keys that attempt reads for the first time: keys prefetched by the failed commit are returned from the failed commit's revision, so a retried attempt can see two revisions at once. The attempt's commit then fails because a prefetched key's mod revision changed, so nothing inconsistent is committed and serializability of the committed result holds. What the closure observes within such an attempt is not what the comment says. This is a request to adjust the documentation, found while formally verifying the concurrency package.

## What happens

References are to `client/v3/concurrency/stm.go` at f061acd0902d489041448cdd19d71a345d27b9f5.

1. Under a serializable level, the first read of an attempt sets its base revision, `s.getOpts = {WithRev(resp.Header.Revision), WithSerializable()}` (`stmSerializable.Get`, lines 321-328), and later reads of keys not yet in the read set use it.
2. When a commit fails, `stmSerializable.commit` (lines 347-362) stores the `Else` branch's reads of the read set's keys, taken at the commit's revision `r`, as the prefetch set (line 360) and clears the base revision (line 361).
3. In the next attempt, a prefetched key is returned from the prefetch set, at `r` (lines 307-320); the first read of any other key goes to etcd at the latest revision `r2 > r` and sets the base revision there.
4. If some transaction changed both a prefetched key and a non-prefetched key in `(r, r2]`, the attempt sees one before that transaction and the other after it.

The attempt's commit compares the prefetched keys' mod revisions with those read (`readSet.cmps`), finds the change, fails, and the STM retries. The committed result is still serializable. Only the view the closure gets during that attempt differs from the comment.

`RepeatableReads` and `ReadCommitted` promise no single revision and are not affected.

## How to reproduce

`TestSTMSerializableSnapshotAfterConflict` in `tests/integration/clientv3/concurrency/stm_snapshot_test.go` (attached), for both serializable levels. Keys `x` and `y` are only ever written together, first to `1`/`1` then to `2`/`2`. The first attempt reads `y` and writes `z`; `y` is changed behind its back so the commit fails and `y` is prefetched. Before the second attempt's first read, `x` and `y` are set to `2`. The second attempt reads `x` first (not prefetched: `2`, at the latest revision) then `y` (prefetched: `1`), and records `x = 2, y = 1`, a pair that was never stored.

## Suggested documentation

Say that the single-revision guarantee applies to an attempt's reads that are not served from the prefetch of a failed commit, or, equivalently, that after a failed commit the retried attempt reads the previously read keys at the failed commit's revision and other keys at the revision of its first fresh read; and that serializability of the committed result is what the level guarantees in all cases.

A code change that reads a retried attempt at the prefetched revision is possible (12 lines; it passes the existing STM tests) if the maintainers would rather keep the comment as it is; it is not proposed here.
