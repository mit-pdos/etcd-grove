# Requirements on `go.etcd.io/etcd/server/v3/storage` (2e: the WAL storage, the hooks, the snapshot backend)

## from 2d

What the raft node driver and the apply thread need of `serverstorage` (2e):

1. **`Storage.Save(hs, ents)`** (`raftNode.start`): **fires the batch's `readyEnter`** (R1) at its
   synced write: the WAL's durable invariant holds `raftState γ.raft id D` (with the WAL's records
   replaying to `D`: 2e's `walHolds`), and `Save` takes the update and moves it to `D.next b`. No
   error under 2e's disk premise (carried by the storage handle; `lg.Fatal` unreachable).
   ```go
   if err := r.storage.Save(rd.HardState, rd.Entries); err != nil { r.lg.Fatal(...) } // raft.go:271
   ```
2. **`SaveSnap(snap)`**: the snapshot file and the WAL's snapshot record (before `Save`: a restart
   finds the snapshot it needs); **`Sync()`**; **`Release(snap)`**: keeps the records at and above
   `snap` (which replay to the durable state), releasing the `.snap.db` files below it; **`Close()`**:
   returns the WAL's durable half (`raftState` in the files: 2e's `memberDisk`). No errors.
3. **`OpenSnapshotBackend(cfg, ss, snap, hooks)`** (`applySnapshot`): opens the `.snap.db` of
   `snap.index`, saved by the snapshotter from a merged snapshot (2f's `dbSaved`), to a backend whose
   image is the state machine at `histAt γ k`, `k ≥ snap.index`, its stored index `k`
   (`Cindex.beStoredCI newbe k`); no error.
4. **`BackendHooks.SetConfState(cs)`** (`applyConfChange`): saved with the next commit (with the
   consistent index of the same entry); `OnPreCommitUnsafe` calls `consistIndex.UnsafeSave`.
5. **`Storage.Save`'s position**: a follower's acknowledgements are sent after it (2d's driver), so
   every entry committed is on a quorum's WAL (K5).
Used by: `raftNode.start.spec`, `raftNode.onStop.spec`, `snapshot.spec`, `applySnapshot.spec`.

## from 2d (round 1)

6. (correction, provability S7) item 4's "saved with the consistent index of the same entry" is
   false (a periodic commit between `SetConfState` and the membership's write saves the new
   `ConfState` with the previous index); it is harmless (the restart rebuilds the configuration
   from the members bucket), so no requirement remains on it.
7. `OpenSnapshotBackend`'s image is `imgAt γ sn.index` (2d's: the state machine at the snapshot's
   point `a`, stored index `a`): the member's invariant over `snapDbs` gives it (`srvNet`'s `dbIn`).


## from 3a

1. **`BackendQuota.Cost(req)`** (the capped applier's `a.q.Cost(r) > 0` on a zero `BackendQuota`):
   positive iff the transaction puts somewhere (either branch, any nesting: `costTxn`), so that the
   capped applier's refusal is a function of the request (3a's `IrrOp.cappedRefused`). Today's spec
   answers any `int`. Also `Cost` on a `*BackendQuota` that `NewBackendQuota` did not build (the
   capped applier's zero field): `isQuota` of it, or a spec of `Cost` without `isQuota` (it reads no
   field).
2. `Available`: any answer (as now): its `false` is 3a's `resMatch` margin.
Used by: `applierV3Capped.Txn.spec`, `quotaApplierV3.*.spec`.
```go
if a.q.Cost(r) > 0 { return nil, nil, errors.ErrNoSpace }                   // capped.go:38
```
