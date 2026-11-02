---
upstream: none
checked: 2026-11-01
links: []
blocks-proof: no
---

# v3rpc: `NewWatchServer` writes the running server's `Cfg` while other goroutines read it

With `--watch-progress-notify-interval` set below 100ms, `NewWatchServer` raises
`s.Cfg.WatchProgressNotifyInterval` to 100ms in place, after the server has started, while another
client listener's `NewWatchServer` reads the same field and `applySnapshot` copies the whole `Cfg`:
a data race under the Go memory model and `-race`.

**Why not an issue:** no test; found by code reading, and benign in effect (an aligned `int64`
write on 64-bit platforms; `OpenSnapshotBackend`'s copy does not read the field). A test could
promote it: an embedded server with two client listeners and a 50ms interval, under `-race`.

## Proof

no: before the fork's fix the proof went through with the serving path owning that field and the
snapshot path a read-only view of only the fields `applySnapshot`'s callees read (`srvSnapRO`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/SnapRO.lean`; `notes/decisions.md`, "D22 J1a"). Since
2026-11-01 the verified fork carries the fix (`goose-lean-watchcfg` `7cf3644ec`, `etc/goose.py`:
`NewWatchServer` keeps the adjusted interval local), so the whole configuration is read-only from
`EtcdServer.start` on (`srvServeCfg`; `notes/decisions.md`, "J8a-3"); a simplification, not a fix
the proof needed.

## Notes

`server/etcdserver/api/v3rpc/watch.go`, `NewWatchServer`. A fix: keep the adjusted interval in the
watch server (or `progressReportInterval`, under its lock) or adjust it before the server starts;
the fork's `7cf3644ec` reads the field into a local, raises the local to `minWatchProgressInterval`
(with the same warning) and passes it to `SetProgressReportInterval`. `EtcdServer.start`'s own writes
of `s.Cfg` (`SnapshotCount`, `SnapshotCatchUpEntries` set to their defaults when zero) are not a
race: they happen before `run` and the listeners start.
Upstream search 2026-11-01 (`WatchProgressNotifyInterval`): nothing about this race.
