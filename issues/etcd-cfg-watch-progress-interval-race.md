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

**How the proof handles it**: the proof gives the serving path the field
`WatchProgressNotifyInterval` owned (`srvServeBuilt`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvServe.lean:106`), so the whole configuration
cannot be read-only for the snapshot path: `srvSnapRO` (`SnapRO.lean`, D22 J1a) holds only the
fields `applySnapshot`'s callees read. `applySnapshot.specSnap`'s premise `srvCfgAddr s ↦□ cfg`
(the whole struct) is therefore not dischargeable as stated; `notes/decisions.md`, "D22 J1a".

**Possible fixes**: keep the adjusted interval in the watch server (or in the package variable
`progressReportInterval`, which `SetProgressReportInterval` already sets under its lock) without
writing `s.Cfg`; or adjust the configuration in `NewServer`/`embed` before the server starts.

**Found**: 2026-10-26, by D22 stage J1a (threading the snapshot path's configuration from
`NewServer` to the apply thread).
