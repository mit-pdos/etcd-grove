---
upstream: none
checked: 2026-11-16
links:
  - etcd-io/etcd#17119 pr merged: related, not this behavior (the commit at `Unlock` when a delete is pending, which leaves the window below)
blocks-proof: no
---

# mvcc: a read transaction can see a compaction finished while the revisions it deleted are still there

A backend read transaction that starts while the compaction's last batch ends sees
`finishedCompactRev` at the new compaction revision `c` and, in the `key` bucket, revisions below `c`
that the compaction deleted: a state no step recorded.

**Why not an issue:** no etcd reader depends on both in one read: mvcc's readers pick revisions
through the in-memory index (compacted first) and never read a compacted revision; `HashByRev` skips
the revisions below its compaction revision that are not kept; `restore` and
`checkPrevCompactionCompleted` read `finishedCompactRev` (the latter beside `scheduledCompactRev`,
both puts) at boot or under the store's lock, not the deleted revisions. The test
(`etcd-mvcc-compaction-readtx-delete-window-mixed-state/`, copied into `server/storage/mvcc` at the
fork pin 6e8f0c004, go1.27.1) reads both, which etcd does not do:

```
$ go test ./storage/mvcc/ -run TestCompactionReadWindowMixedState -count=1 -v
    zz_compaction_window_test.go:77: reads 1983, reads of an unrecorded state 4 (first at finishedCompactRev 3)
--- FAIL: TestCompactionReadWindowMixedState (0.02s)
```

**How:** the last batch of `store.scheduleCompaction` (`server/storage/mvcc/kvstore_compaction.go:55-71`)
deletes the batch's compacted revisions (`UnsafeDelete(Key, ...)`) and puts `finishedCompactRev`
(`UnsafeSetFinishedCompact`) under one batch lock; `batchTxBuffered.Unlock`
(`server/storage/backend/batch_tx.go:328-357`) writes the put back into the read buffer, releases
`readTx`'s lock, then commits the deletes. Same window as
[`etcd-membership-readtx-delete-window-mixed-state`](etcd-membership-readtx-delete-window-mixed-state.md).

## Proof

no: the backend's read side is proved with the window (the readers' view is the read buffer over
bbolt's committed data, `RdSt`'s window flag, the safe-range buckets' deleted entries `dls`), mvcc's
reads are proved over it, and the trusted `backend.Snapshot` observes bbolt's committed data, where
the batch is atomic (`notes/backend-delete-window-audit.md`).
