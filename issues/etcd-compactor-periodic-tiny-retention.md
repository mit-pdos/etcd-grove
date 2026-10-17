---
upstream: unchecked
checked: 2026-10-17
links: []
---

# server/etcdserver/api/v3compactor: a periodic retention below 10ns panics in `New` (divide by zero)

- **Status**: a bug (a reachable panic at startup on an accepted configuration).
- **Where**: the fork `upamanyus/etcd` at `107edf7e4` (`etc/goose.py`'s etcd pin).
  `v3compactor.New` (`server/etcdserver/api/v3compactor/compactor.go:66-67`) calls
  `newPeriodic`, which sizes `pc.revs` with `pc.getRetentions()` (`periodic.go:60`):
  `int(pc.period/pc.getRetryInterval()) + 1` (`periodic.go:177-179`), where
  `getRetryInterval()` is `min(period, 1h) / 10` (`periodic.go:183-189`), `0` for any period
  strictly between `-10ns` and `10ns`. `NewServer` calls `New` whenever the retention is not
  zero (`server/etcdserver/server.go:383-384`), and `embed`'s `parseCompactionRetention`
  (`server/embed/etcd.go:928-947`) accepts any duration string for the periodic mode
  (`time.ParseDuration`), e.g. `--auto-compaction-mode=periodic --auto-compaction-retention=5ns`.
- **What happens**: `runtime error: integer divide by zero` in `New`, so `NewServer` (and the
  member) panics instead of rejecting the configuration. Reproduction (a test in
  `server/etcdserver/api/v3compactor`, `go test -run TestPeriodicTinyRetentionPanics .`; it passes,
  i.e. confirms the panic, at the pin):

  ```go
  func TestPeriodicTinyRetentionPanics(t *testing.T) {
  	defer func() {
  		r := recover()
  		if r == nil {
  			t.Fatal("expected a panic")
  		}
  		t.Logf("New(periodic, 5ns) panicked: %v", r)
  	}()
  	New(zaptest.NewLogger(t), ModePeriodic, 5*time.Nanosecond, nil, nil)
  }
  ```
- **Expected**: an error from the configuration's validation (or from `New`), as for an unknown
  mode.
- **How the proof handles it**: `NewServer`'s proof (unit N1 of the server-construction unit,
  `notes/STATUS.md`) does not yet state `v3compactor.New`'s contract (pending, `?` in
  `etc/link-lean-first-server.txt`); its true statement needs the premise
  `mode = "periodic" → retention ≤ -10ns ∨ 10ns ≤ retention` (the analysis in `notes/STATUS.md`,
  "Server construction, unit N1").
- **Possible fixes**: reject a periodic retention below some minimum (at least `10ns`; a sensible
  bound is a second) in `parseCompactionRetention` or the server config's validation, or compute
  the retry interval with a floor of `1` in `getRetryInterval`.
- **Found**: 2026-10-17, auditing the contract of `v3compactor.New` for `NewServer`'s proof.
