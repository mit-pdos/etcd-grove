---
upstream: unchecked
checked: 2026-10-26
links: []
---

# `NewWatchServer` writes `s.Cfg` while other goroutines read it

**Status**: a data race (benign in effect on 64-bit platforms, but a race under the Go memory
model and `-race`), with a non-default configuration only: `--watch-progress-notify-interval` set
below 100ms (and above 0).

**Where** (etcd at the pin `bc9c3868c`):
- `server/etcdserver/api/v3rpc/watch.go:77-86`, `NewWatchServer`: when
  `0 < s.Cfg.WatchProgressNotifyInterval < minWatchProgressInterval` it assigns
  `s.Cfg.WatchProgressNotifyInterval = minWatchProgressInterval`, a write to the running server's
  configuration struct, with no lock.
- `NewWatchServer` runs from `v3rpc.Server`, which `embed`'s `serveCtx.serve` calls for each client
  listener (`server/embed/serve.go:184`, `:244`) in its own goroutine, after
  `s.ReadyNotify()`: the server is started (`e.Server.Start()`, `server/embed/etcd.go:282`), its
  apply loop running.
- The same struct is read concurrently: `applySnapshot` copies the whole of `s.Cfg`
  (`serverstorage.OpenSnapshotBackend(s.Cfg, ...)`, `server/etcdserver/server.go:1061`) when the
  member installs a snapshot from the leader; and a second client listener's `NewWatchServer`
  reads the same field (`s.Cfg.WatchProgressNotifyInterval > 0`) while the first writes it.

**What happens**: with two client listeners (or a snapshot installed while the listeners start),
and the interval configured below 100ms, the write races the reads. The values involved are the
user's and `100ms`; a torn read is not possible for an aligned `int64` on 64-bit platforms, so the
effect is at most a stale interval in `OpenSnapshotBackend`'s copy (which does not read it). No
reproduction written (it needs an embedded server with two listeners under `-race`).

**Expected**: the server's configuration is read-only once the server is started (nothing
documents that it may change).

**How the proof handles it**: until J8a-3 (2026-11-01) the proof gave the serving path the field
`WatchProgressNotifyInterval` owned (`srvServeBuilt`, `InvServe.lean`), so the whole configuration
could not be read-only for the snapshot path: `srvSnapRO` (`SnapRO.lean`, D22 J1a) held only the
fields `applySnapshot`'s callees read, and `applySnapshot.specSnap`'s premise `srvCfgAddr s ↦□ cfg`
(the whole struct) was not dischargeable; `notes/decisions.md`, "D22 J1a". Since the fork's fix
(below), the field is read-only (`srvServeCfg`), `NewWatchServer.spec` takes it `↦□`, and
`srvSnapRO` holds the configuration's rebuild (`notes/decisions.md`, "J8a-3"). `EtcdServer.start`'s
two writes of `s.Cfg` (`SnapshotCount`, `SnapshotCatchUpEntries` set to their defaults when zero,
`server/etcdserver/server.go:554-570`) are not a race, since they happen before `run` and the
listeners start, but they are why the configuration is read-only only from `start` on: the rebuild
takes those two fields read-only, which `start` persists (`isServerRun`'s `"#Hsncfg"`).

**Possible fixes**: keep the adjusted interval in the watch server (or in the package variable
`progressReportInterval`, which `SetProgressReportInterval` already sets under its lock) without
writing `s.Cfg`; or adjust the configuration in `NewServer`/`embed` before the server starts.

- **Fixed in the fork** (2026-11-01, the user's decision; `upamanyus/etcd` branch
  `goose-lean-watchcfg` `7cf3644ec`, the pin of `etc/goose.py`): `NewWatchServer` reads
  `s.Cfg.WatchProgressNotifyInterval` into a local `interval`, raises the local to
  `minWatchProgressInterval` if below (with the same warning), and passes it to
  `SetProgressReportInterval`; it no longer writes `s.Cfg`. The first of the possible fixes above.

**Found**: 2026-10-26, by D22 stage J1a (threading the snapshot path's configuration from
`NewServer` to the apply thread).
