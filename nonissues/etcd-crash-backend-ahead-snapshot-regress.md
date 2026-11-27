---
upstream: known
checked: 2026-11-24
links:
  - etcd-io/etcd#22028 issue open: the state itself (Antithesis, "backend.ConsistentIndex (1049) must be <= WAL.HardState.commit (1047)")
  - etcd-io/etcd#22514 pr open: drops the verifier's upper bound on the consistent index, treating the state as valid
  - etcd-io/etcd#22646 issue closed: related, not this: `--force-new-cluster` on a member in the state bricks it
blocks-proof: no
---
# etcdserver: after a crash a follower's backend can be ahead of its WAL, and a later leader snapshot can move it back

A follower applies committed entries before its raft loop saves them to the WAL, so a kill -9 or
power loss can leave its backend's consistent index `i` above the WAL's last index. Restarted, its
apply progress starts at its raft snapshot's index, not `i`. A leader snapshot at an index `k`
between the WAL's last index and `i` is then accepted by raft and by `applySnapshot`, which moves
the backend back from `i` to `k` until the entries after `k` are applied again.

**Why not an issue:** no client sees the backward move: the member serves clients only after it
has applied its own publish entry, which is above `i`. The first half (backend ahead of the WAL
after a kill -9) is shown by a test; the snapshot at `k < i` is found by code reading and needs only
a live leader whose apply loop lags its commit index.

## Evidence (etcd fork pin `6b942d23f4`, raft v3.7.0)

1. **Backend ahead of the WAL.** Without async storage writes, raft hands out committed entries
   from the unstable log (`raft/v3@v3.7.0/rawnode.go:440-445`, `applyUnstableEntries`). A follower
   that gets entries and their commit index in one `Ready` (it lagged: partition, slow disk) has them
   in both `Entries` and `CommittedEntries`. `raftNode.start` sends the batch to the apply loop
   (`server/etcdserver/raft.go:251-253`) before `storage.Save` (`:275-276`). `applyAll` applies the
   entries first and waits on `notifyc` only after that (`server.go:984-995`), and the backend
   commits on its batch timer.
   `TestBackendAheadOfWALAfterKill`
   ([`etcd-crash-backend-ahead-snapshot-regress/backend_ahead_of_wal_test.go`](etcd-crash-backend-ahead-snapshot-regress/backend_ahead_of_wal_test.go))
   was run in `tests/integration` at the pin, with `gofail enable server/etcdserver/` and
   go1.27.3. The setup is three members, with one follower partitioned while 5 puts commit. Every raft
   loop is held at `raftBeforeSave`, and the follower's partition is healed. The follower's data
   directory is copied while its loop is held. That copy is the state a kill -9 leaves:
   ```
   zz_backend_ahead_of_wal_test.go:79: committed and applied by A and B up to index 14 (revision 7); F applied 9
   zz_backend_ahead_of_wal_test.go:104: kill -9 image of F: backend consistent index 14, WAL last index 9, WAL HardState commit 8
   zz_backend_ahead_of_wal_test.go:127: F restarted from the image, ready, serves revision 7 (applied 15)
   --- PASS: TestBackendAheadOfWALAfterKill (23.24s)
   ```
   The test cuts the follower off before its loop leaves the failpoint, so no acknowledgement of the
   unsaved entries reaches the leader. When it did not, the leader's heartbeat carried commit 14 to
   the restarted follower (last index 9), which panicked in `tocommit(14) is out of range`. That
   panic came from the test, not from a kill -9.
2. **A snapshot below the backend is accepted after the restart.** `run` sets
   `ep.appliedi` from the raft snapshot (`server.go:807-814`). raft's `restore` rejects only a
   snapshot at or below its commit index, or one whose entry it holds
   (`raft/v3@v3.7.0/raft.go:1861-1862`, `:1911-1918`). `applySnapshot` panics only on
   `Index <= ep.appliedi` (`server.go:1049`). After that check it opens the snapshot's backend and restores lease, mvcc,
   alarm, auth and membership from it (`:1060-1180`), whatever the old backend's consistent index.
3. **Reachability of `k < i`: a live leader whose apply loop lags (inference; the lag observed).**
   With the fork's sender repair, the merged snapshot's index is `max(applied, backend consistent
   index)` of the leader (`snapshot_merge.go:38-40`). So `k < i` needs a leader whose applied state is
   below the follower's backend, and a live leader suffices: its raft loop hands a `Ready` to the apply
   loop (`raft.go:251-253`) and sends its messages, which carry the commit index, right after
   (`:259-263`), without waiting for the apply. The follower can so learn of commit `i` and apply it
   while the leader's apply loop is still below `i`; etcd lets the applied index lag the commit index
   by up to 5000 entries (`maxGapBetweenApplyAndCommitIndex`, `v3_server.go:51`) before refusing
   proposals. coordinator-E (T10s3b, 2026-11-27) observed a live leader at applied 11 while a follower
   had applied 31. If the follower then crashes and restarts while the leader still lags, and the
   leader's raft log is compacted above the follower's WAL, the leader sends a snapshot at its applied
   index `k < i`. (An earlier version of this note said `k < i` needs the leader to crash too, with its
   durable commit below `i`; that is one way, not the only one.)
4. **Not client-visible.** Client listeners serve only after `ReadyNotify`
   (`server/embed/serve.go:133-136`). `readych` closes when `publishV3`'s request returns
   (`server.go:1854-1856`), that is, after this member has applied the publish entry. That entry is
   proposed after the restart, so its index is above every committed index, `i` included, and the
   member has applied `i` again before it serves. Watches and leases are per process, so there are none to
   see the move. Once `ep.appliedi` passes `i`, every accepted snapshot is above the backend's
   index. Only the member's metrics (`etcd_mvcc_*revision`) may show the drop.

## Fix (fork, 2026-11-24)

The fork's `goose-lean-slicessort-on-fmtattrs-snapguard` (8aa40fd5c, on the pin `6b942d23f4`; the pin of
`etc/goose.py` since etcd-dist D6 T4) makes `applySnapshot` keep the backend when the snapshot's index
is at or below the backend's consistent index: it moves `appliedi`, `appliedt`, the disk and memory
snapshot indices and the conf state to the snapshot's and returns, without opening the snapshot's
database or recovering the stores. The backend already holds every entry up to its consistent index,
and the entries between the snapshot and it are skipped by the apply loop as in any restart replay, so
the backend never moves back. `TestApplySnapshotBelowBackend` (`server/etcdserver/
snapshot_below_backend_test.go`) calls `applySnapshot` with snapshots at 5 and 7 below or at a backend
at 7: the backend is kept and the applied state moves; without the guard it panics opening the
snapshot's database. Upstream-ready as a hardening (the regression is not client-visible, above).

The keep branch first left the cluster configuration and the transport's peers as the restart replay
set them: that replay (entries at or below the consistent index) sets member attributes, peer URLs, the
cluster version, the downgrade info and the transport's peers in memory only, from entries older than
the backend, and the entries that would set them back are covered by the snapshot. The fork's
`goose-lean-discardfix-ttlkeys-keepfix` (a453b08a1, on 30df685e4) also recovers the cluster from the
kept backend (`s.cluster.Recover`), rebuilds the transport's peers from it and releases the older
WAL and snapshot files, as the replacing path does (`TestApplySnapshotBelowBackendRecoversCluster`).

## Proof

no: not a client-visible bug, and the graceful results are unaffected. With the fork's guard the
crash-form restart (`NewServer.wp_proofC`'s `σ.commit < i` case, `notes/etcd-dist-d6.md`) keeps the
apply side's monotone ghost state: a snapshot at or below the backend's index is a skip
(`applySnapshot`'s new branch), and `applySnapshot.specSnapM` (a snapshot above the consistent index)
is unchanged in meaning.

## Notes

The same receiver state, reached by a restarted leader's in-window merge instead of a crash, is
[`etcd-backward-snapshot-install-panics-watcher`](etcd-backward-snapshot-install-panics-watcher.md).
There the receiver may be serving, so its watchers can panic. After a crash the receiver serves
nothing until it has caught up.
