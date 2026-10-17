---
upstream: unchecked
checked: 2026-10-17
links: []
---

# server/etcdserver: the auto-compactor runs before `Start` and is leaked on `NewServer`'s error paths

- **Status**: a bug (a possible panic and a goroutine leak), not reproduced.
- **Where**: the fork `upamanyus/etcd` at `107edf7e4` (`etc/goose.py`'s etcd pin).
  `NewServer` starts the compactor (`server/etcdserver/server.go:383-388`: `v3compactor.New`,
  `srv.compactor.Run()`) before `restoreAlarms` (line 391) and the transport's `Start` (line
  428), either of which can still fail and make `NewServer` return an error; its deferred
  closures then close the backend and the KV (lines 307-311, 377-382) but never stop the
  compactor. The compactor's goroutine (`v3compactor/periodic.go:100-…`, `revision.go:65-…`)
  calls `srv.Compact` (`v3_server.go:382`) once its period has elapsed (periodic mode: as soon as
  the store's revision of a period ago differs from `0`, i.e. also on a fresh store) or every five
  minutes (revision mode), which goes through `processInternalRaftRequestOnce` to
  `s.w.Register(id)` (`v3_server.go:1107`); `s.w` is set only by `start()` (`server.go:570`).
- **What happens** (from reading the code): on `NewServer`'s error paths after `Run`, the leaked
  compactor later calls `Compact` on the half-built server: `s.w` is a nil interface, so the
  process panics, an embedder that handled `NewServer`'s error included. On the success path, if
  the period elapses before `Start` (a short periodic retention such as `1s` and a slow
  `embed.StartEtcd` between the two, e.g. the initial corruption check contacting peers), the same
  call races with `start()`'s write of `s.w` or panics on its nil value.
- **Expected**: `NewServer` either starts the compactor in `start()` (with the server's other
  goroutines), or stops it on its error paths.
- **How the proof handles it**: not yet: `v3compactor.New` and `Run` are names-only and their
  contracts are pending (`?` in `etc/link-lean-first-server.txt`); N0's `compactorRunOk` (`{True}
  Run() {True}`) hides the goroutine's proposals and is not a true contract
  (`notes/STATUS.md`, "Server construction, unit N1"). A true one makes `Run` require
  `Compact`'s contract, which the server only meets after `start()`; `NewServer`'s spec would
  take `cfg.AutoCompactionRetention = 0` meanwhile.
- **Possible fixes**: move `srv.compactor.Run()` to `start()` (or `Start`), or add
  `if err != nil && srv.compactor != nil { srv.compactor.Stop() }` to the deferred closure.
- **Found**: 2026-10-17, auditing the contract of `v3compactor.New` for `NewServer`'s proof.
