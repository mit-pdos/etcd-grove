---
upstream: none
checked: 2026-10-23
links: []
---

> Moved to `issues/nonissues/` on 2026-10-23 (review of `issues/INDEX-reviewed.md`): not an issue: a precondition of a test helper (`Blackhole` on a bridge not already blackholed); no etcd test calls it twice (checked at upstream `3aaab3479b`, 2026-10-23).

# tests/framework/integration: a second `Blackhole` of a bridge panics

- **Status**: an undocumented precondition of a test helper, not a bug any test reaches: the
  integration tests' bridge (the TCP proxy between a client and a member,
  `ClusterConfig.UseBridge`) requires `Blackhole` to be called on a bridge that is not
  blackholed. A second call without an `Unblackhole` in between panics with "close of closed
  channel", while holding the bridge's mutex; after the panic is recovered, every later call that
  takes the mutex (`Unblackhole`, `DropConnections`, `Close`, a new connection's registration)
  blocks forever. Nothing states the precondition (`Bridge`'s interface has no doc comments), and
  the sibling operations are idempotent: `Close` and `UnpauseConnections` close their channels only
  if they are open, and the e2e proxy's `BlackholeTx`/`BlackholeRx` (`pkg/proxy`) are idempotent.
  No upstream caller calls it twice (2026-10-23 check below).
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
  (`clientStep`'s `holed`). The bridge's trust-boundary spec of `Blackhole`
  (`Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/bridge__Blackhole.lean`; the bridge's
  code is not verified, `notes/decisions.md` D26) takes the bridge unblackholed
  (`bridgeAt b addr false`) as its premise, and `clientStep`'s proof meets it from `holed[a]`.
- **Upstream check (2026-10-23)**: at etcd `upstream/main` `3aaab3479b`, unchanged:
  `tests/framework/integration/bridge.go:187-191` (`Blackhole`, the unguarded `close`),
  `:193-201` (`Unblackhole`), `:28-35` (the `Bridge` interface, no doc comments), `:68-78` and
  `:95-103` (`Close`, `UnpauseConnections`, guarded). `Blackhole` dates from 741d7e9dc
  (2017-08-25, "integration: add Blackhole to bridgeConn"), which gave no rationale; the guarded
  pattern came with fe1ce3a2f (2017-04-21, pause/unpause). The only callers are
  `tests/integration/clientv3/connectivity/black_hole_test.go:77,87,92` (member 0 blackholed then
  unblackholed, then member 1 blackholed once) and `:189` (once). There is no `Member`-level
  wrapper (`tests/framework/integration/cluster.go:845` `Member.Bridge` returns the bridge
  itself) and no other helper reaches it; the robustness tests' blackholes go through
  `pkg/proxy`, not this bridge. So a double call is unreachable in existing tests. GitHub search
  (`bridge Blackhole`, `"close of closed channel" bridge`, `blackholec`): nothing related (one hit,
  etcd-io/etcd#8258, unrelated keepalive PR). Worth at most a one-line cleanup PR (the guard above);
  the value to etcd is low.

