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

no: the proof gives the serving path that field and the snapshot path a read-only view of only
the fields `applySnapshot`'s callees read (`srvSnapRO`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/SnapRO.lean`; `notes/decisions.md`, "D22 J1a").

## Notes

`server/etcdserver/api/v3rpc/watch.go`, `NewWatchServer`. A fix: keep the adjusted interval in the
watch server (or `progressReportInterval`, under its lock) or adjust it before the server starts.
Upstream search 2026-11-01 (`WatchProgressNotifyInterval`): nothing about this race.
