---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#13527 issue closed: same bug (closed by the stale bot, not fixed), the report this was triaged from
  - etcd-io/etcd#16847 pr closed: separate raft tick and ready (not merged)
  - etcd-io/etcd#15440 pr closed: watchdog for stalled writes (not merged)
  - etcd-io/etcd#15247 issue closed: related (a disk-stuck old leader revoked leases; fixed by #16822 at the lease level, not the tick)
  - etcd-io/etcd#14338 issue closed: related (removed member fails to stop on a stuck disk)
---

# A stalled WAL write stops raft's ticks, so a partitioned leader never steps down

- **Status**: a bug (liveness). The server's raft loop delivers ticks and persists `Ready`s in the
  same goroutine. While a WAL write stalls, raft gets no tick, so `CheckQuorum` never makes a
  leader cut off from its followers step down. The member keeps reporting itself leader
  (`etcd_server_is_leader`, `endpoint status`) while the rest of the cluster elects a new leader
  at a higher term. This does not break raft safety: the stale leader cannot commit.
- **Where**: at the etcd pin of `etc/goose.py` (`107edf7e4`; same on upstream `main` and since
  v3.4): `raftNode.start` (`server/etcdserver/raft.go:174`). Its `select` has the tick case
  (`:183`, `r.tick()`) and the `Ready` case, which calls `r.storage.Save` (`:256`) and, for
  snapshots, `SaveSnap`/`Sync` inline.
- **What happens**: reproduced at the pin by
  `issues/etcd-stalled-wal-no-tick/stalled_wal_no_tick_test.go` (package `etcdserver`; passes at
  the pin). It uses a WAL whose `Save` blocks and a 5 ms heartbeat. Ticks arrive while the loop is
  idle (20 in 100 ms). After a leader `Ready` with an entry, the loop enters `Save`, and no `Tick`
  reaches the node in the next 200 ms (40 heartbeat intervals). End to end, as in #13527: the
  failpoint `raftAfterSave` set to `sleep(600000)` on the leader, then the leader isolated with
  `iptables`. The old leader reports itself leader for the whole sleep.
- **Expected**: raft's ticks keep arriving whatever the disk does, so that `CheckQuorum` steps a
  leader down within an election timeout of losing its quorum, or the member otherwise stops
  claiming leadership.
- **How the proof handles it**: admitted. `raftNode.start.spec`
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__start.lean`) is partial correctness, and
  the WAL contract `isRNWal` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRaftNode.lean:566`)
  is a Hoare triple that a non-returning `Save` meets. Time is not modeled (ticks are an unbounded
  resource). Separately, the server's raft is proved with `CheckQuorum` off
  (`Spec/.../etcdserver/bootstrappedRaft__newRaftNode.lean:76`), so step-down is outside the
  proved configuration.
- **Possible fixes**: tick raft from its own goroutine (`raftNode.tick` already takes `tickMu`, and
  `node.Tick` only sends on `tickc`, which `node.run` drains while a `Ready` is outstanding), as
  #16847 proposed. Or detect the stall (#15440) and stop serving as leader.
- **Found**: 2026-10-16, by the bug triage of etcd-io/etcd#13527 (`notes/bug-triage/etcd-13527.md`).
