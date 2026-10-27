---
upstream: none
checked: 2026-10-20
links: []
---

# server/etcdserver: the auto-compactor runs before `Start` and is leaked on `NewServer`'s error paths

- **Status**: a bug (a panic and a goroutine leak); the panic reproduced (2026-10-27, below), fixed in
  the fork.
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
- **Reproduction** (2026-10-27): `etcd-compactor-started-before-start/repro_test.go`, a test of etcd's
  `tests/integration` package (copy it there): `NewServer` with a 1s periodic retention, then 2s
  without `Start`. At the fork's `c00a2dc06` (the compactor run by `NewServer`) it panics after about
  a second (`runtime error: invalid memory address or nil pointer dereference`: `Compact` on the nil
  `s.w`); with the fix (`964dccdb4`) it passes. It is also the fix's regression test.
- **Expected**: `NewServer` either starts the compactor in `start()` (with the server's other
  goroutines), or stops it on its error paths.
- **How the proof handles it**: fixed in the fork (2026-10-27, branch `goose-lean-compactorstart`,
  `964dccdb4`: `NewServer` only creates the compactor, `start()` runs it after `s.w` and the request
  path's fields are set), the spec-first pilot's choice (`notes/compactor-pilot-plan.md`): with the
  compactor running from `NewServer`, no contract for its `Compact` calls can be sound (the third
  review of the pilot's specs: `Compact` needs `isServerReq`, which only `start()` makes true). The
  compactor's `Run` takes the environment's contracts (`v3compactor.runPre`), which `start()` can
  give. Until the pilot's glue, `NewServer`'s spec keeps `cfg.AutoCompactionRetention = 0`.
- **Possible fixes**: move `srv.compactor.Run()` to `start()` (or `Start`; the fork's fix, which passes
  `tests/integration/embed`'s `TestEmbedEtcdAutoCompactionRetentionRetained`), or add
  `if err != nil && srv.compactor != nil { srv.compactor.Stop() }` to the deferred closure.
- **Found**: 2026-10-17, auditing the contract of `v3compactor.New` for `NewServer`'s proof.
