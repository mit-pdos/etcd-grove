---
upstream: none
checked: 2026-10-23
links: []
blocks-proof: no
---

# tests/framework/integration: a second `Blackhole` of a bridge panics and leaves its mutex held

The integration tests' bridge (the TCP proxy between a client and a member, `UseBridge`) panics
with "close of closed channel" on a second `Blackhole` without an `Unblackhole` in between, while
holding its mutex, so after a recovered panic every later call that takes it hangs. Its sibling
operations (`Close`, `UnpauseConnections`, the e2e proxy's blackholes) are idempotent.

**Why not an issue:** a precondition of a test helper: the only callers
(`tests/integration/clientv3/connectivity/black_hole_test.go`) blackhole a bridge once and
unblackhole it before the next; no test calls it twice (checked at `3aaab3479b`, 2026-10-23).

## Proof

no: the bridge's trust-boundary spec of `Blackhole`
(`Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/bridge__Blackhole.lean`) takes the bridge
unblackholed, and `examples/linkv3p`'s partitioner skips a second `Blackhole`.

## Notes

Test: this repository's `third_party/bridge/bridge_test.go`, `TestBlackholeTwicePanics` (passes
when the panic happens). The 2026-10-23 review's plan asked whether this is a bug or the helper's
contract; the 2026-10-23 review answered the contract. The guard `select { case
<-b.blackholec: default: close(b.blackholec) }` would be a one-line cleanup.
