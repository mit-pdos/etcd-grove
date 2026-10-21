---
upstream: unchecked
checked: 2026-10-21
links: []
---

# tests/framework/integration: a second `Blackhole` of a bridge panics

- **Status**: a bug in a test helper: the integration tests' bridge (the TCP proxy between a
  client and a member, `ClusterConfig.UseBridge`) is not idempotent under `Blackhole`. A second
  call without an `Unblackhole` in between panics with "close of closed channel", while holding
  the bridge's mutex. After the panic is recovered, every later call that takes the mutex
  (`Unblackhole`, `DropConnections`, `Close`, a new connection's registration) blocks forever.
  `Bridge`'s interface describes `Blackhole`/`Unblackhole` as states, not one-shot operations, and
  its other pairs are guarded: `Close` and `UnpauseConnections` close their channels only if they
  are open (a `select` with a `default`).
- **Where**: the fork `upamanyus/etcd` at `8a24be2a3` (`etc/goose.py`'s etcd pin; the file is
  upstream's). `tests/framework/integration/bridge.go:187-191`: `Blackhole` is
  `b.mu.Lock(); close(b.blackholec); b.mu.Unlock()`. `Unblackhole` (`:193-201`) makes a new
  channel. The copy this repository verifies is `third_party/bridge/bridge.go` (the same lines).
  Upstream's own tests (`tests/integration/clientv3/connectivity/black_hole_test.go`) blackhole a
  member once and unblackhole it before the next blackhole, so they never reach it.
- **What happens**: the second `Blackhole` panics. Reproduction:
  `third_party/bridge/bridge_test.go`, `TestBlackholeTwicePanics` (`go test -run
  TestBlackholeTwicePanics ./third_party/bridge/`; it passes, i.e. confirms the panic). Without
  the test's `recover`, the program dies.
- **Expected**: `Blackhole` of a blackholed bridge leaves it blackholed, as `UnpauseConnections`
  of an unpaused bridge leaves it unpaused. The fix is the same guard:

  ```go
  func (b *bridge) Blackhole() {
  	b.mu.Lock()
  	select {
  	case <-b.blackholec:
  	default:
  		close(b.blackholec)
  	}
  	b.mu.Unlock()
  }
  ```
- **How the proof handles it**: `third_party/bridge` stays upstream's file. `examples/linkv3p`'s
  `partitioner` (a schedule may blackhole a bridge any number of times: its theorem is "for
  every schedule") records which bridges are blackholed and skips a second `Blackhole`
  (`clientStep`'s `holed`). The bridge's spec of `Blackhole` (stage K2 of
  `notes/client-cut-plan.md`) will take the bridge unblackholed as its premise.
