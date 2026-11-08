---
upstream: none
checked: 2026-11-08
links: []
blocks-proof: yes
---

# The API server's etcd3 watcher can deliver events after a watch.Error event

When the etcd watch behind an etcd3 storage watch fails (a compacted revision, a member that lost
its leader cancelling a require-leader stream) while earlier events are still being decoded, the
`watch.Error` event can reach the consumer before some of those earlier events: the error is sent by
the goroutine reading etcd's watch (`startWatching` → `sendError`) while the processing goroutine is
still sending decoded events (`sendEvent`) on the same result channel, and `sendError`'s cancel only
stops them after its own send (and `sendEvent`'s `select` on the result channel and the cancelled
context may still pick the send). `watch.Interface` says a producer that errors "should instead send
an error event and close the result channel"; the watcher's own comment says "sendError doesn't
guarantee that no more items will be put into resultChan" (TODO(wojtek-t)). Kubernetes' storage
correctness test rejects such a stream (`WatchValidator.validateMaybeLastEventError`, and
`runWatch`'s "watch channel was not closed after watch.Error").

**Why not an issue:** reproduced only through a fake `clientv3.Watcher` (not through a real etcd);
upstream knows (the TODO); the API server's consumers (the reflector) stop at the first `Error`
event, so the extra events are dropped; it would surface as a false failure of the correctness test
under faults. GitHub not searched (no `gh` in this environment).

## Proof

yes: the 7f driver's watch check drops error events wherever they occur instead of requiring one
last (`notes/k8s-7f-scope.md`, §2.4 and §5); with upstream's validator the closed theorem would be
false under partitions.

## Notes

Test: [`k8s-etcd3-watcher-events-after-error/errorder_test.go`](k8s-etcd3-watcher-events-after-error/errorder_test.go),
package `etcd3` of this repository's `examples/k8s/etcd3` (branch `k8s-7e`, `76cb57f0b7`, with the
7f prototype's codec change: `Decode` with no object to decode into), `k8s.io/apiserver`
`9c4ec15b8038`, go1.27: a fake watcher sends 150 creates then a compacted response; a consumer that
starts reading after 100 ms saw the `Error` event before other events in 8 of 50 trials
(`watch.Error at index 50 of 52 events`). Found 2026-11-08 writing the 7f Scope.
