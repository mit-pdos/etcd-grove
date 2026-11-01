---
upstream: unchecked
checked: 2026-10-30
links: []
---

# mvcc: `store.Restore` drops a queued compaction without closing its channel; a `Physical` compaction RPC then hangs

- **Status**: a liveness bug (a hang and a goroutine leak), reproduced (2026-10-30, below). Not a
  safety issue: the store restored from the snapshot is right, only the waiter of the dropped
  compaction is never released.
- **Where**: etcd at `etc/goose.py`'s pin (the fork `upamanyus/etcd`, `249d76bea7` in
  `.lake/go-src/etcd`). `server/storage/mvcc/kvstore.go:292-314` (`store.Restore`: `close(s.stopc)`,
  then `s.fifoSched.Stop()`), `kvstore.go:234-260` (`store.compact`: the job's first lines,
  `if ctx.Err() != nil { s.compactBarrier(ctx, ch); return }`), `kvstore.go:137-154`
  (`compactBarrier`: with a cancelled context and `s.stopc` closed it returns without `close(ch)`),
  `pkg/schedule/schedule.go:150-184` (`fifo.Stop` cancels the context; the worker then runs every
  pending job with it), `server/etcdserver/v3_server.go:402-403` (`EtcdServer.Compact` with
  `Physical: true` waits `<-result.Physc`, no other case), `server/etcdserver/apply/uber_applier.go:145`
  (`Physc` is the channel `store.Compact` returned).
- **What happens**: `store.Compact` schedules its job and returns its channel `ch`. If another job
  is running (an earlier compaction: each runs in batches separated by
  `CompactionSleepInterval`, minutes for a large store), the new job waits in the scheduler's queue.
  If a snapshot is installed meanwhile (`applySnapshot` -> `s.kv.Restore(newbe)`: a lagging follower,
  while compaction runs, e.g. Kubernetes' API server compacting every five minutes), `Restore`
  closes `stopc` and stops the scheduler; the running job sees `stopc` and returns through
  `compactBarrier(context.TODO(), ch)`, which closes its channel, but the queued job runs with the
  cancelled context, calls `compactBarrier(ctx, ch)`, finds `stopc` closed and returns: its `ch` is
  never closed. The `Compact` RPC that asked for `Physical: true` on that member waits on it
  forever (its handler goroutine leaks; the client sees its own deadline, or hangs without one).
  The comment in `compactBarrier` ("compaction and apply snapshot requests are serialized by raft,
  and do not happen at the same time") holds of the requests, not of the compaction's job.
- **Reproduction** (2026-10-30): `etcd-restore-pending-compaction-unclosed/repro_test.go`, a test of
  `server/storage/mvcc` (copy it there; `go test ./storage/mvcc/ -run TestCompactPending -v` from
  `server/`): a blocking job occupies the scheduler, `Compact(…, 2)` queues behind it (two jobs
  pending), then `Restore` (the blocker returns when `Stop` cancels the context). Without `Restore`
  the channel closes at once (`TestCompactPendingNoRestoreCloses`); with it, it is never closed
  (`TestCompactPendingDuringRestoreNeverCloses` fails after 2s; same with `-race -count=5`).
- **Expected**: `Compact`'s channel is closed once the compaction is done or abandoned (as for the
  running job, which `Restore` interrupts and whose channel it closes), so a `Physical` request
  returns (with the compaction not done, as after an interruption).
- **How the proof handles it**: the store's specs are partial correctness (no liveness), and today
  no compacting store is restored (`store.Restore.spec`'s `d.cm = false` premises, Q5-3/Q5-4). The
  model of the compaction's channel already says a receive may return with the job's context
  cancelled (`compactDone`'s third disjunct, `InvCompact.lean`), so nothing claims the channel is
  closed. Found drafting restore in compaction mode (M2's storage side, step 2,
  `notes/m2-storage-plan.md`): the drafted restorable compaction right takes the jobs' share of the
  store's fields back when `Stop` returns.
- **Possible fixes**: in `compactBarrier`, close `ch` when `s.stopc` is closed instead of returning
  (`case <-s.stopc: close(ch)`: nothing waits for a later barrier once the store is stopped or
  restored); or in `EtcdServer.Compact`, wait on `Physc` with `ctx.Done()` and `s.stopping` too.
- **Found**: 2026-10-30, reading `store.Restore` against the compaction's jobs for M2's step 2
  (restore in compaction mode); reproduced by a Go test the same day.
