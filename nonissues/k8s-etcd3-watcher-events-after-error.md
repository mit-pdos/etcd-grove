---
upstream: none
checked: 2026-11-08
links:
  - kubernetes/kubernetes#23694 pr merged: the etcd3 watcher's first implementation (sendError's race dates from it; not a report of it)
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
under faults. Upstream searched 2026-11-08 (kubernetes/kubernetes issues and PRs, by keyword
through the web: "sendError doesn't guarantee", "watch channel was not closed after watch.Error",
etcd3 watcher after error): nothing but the watcher's original PR; keyword search does not rule out
a differently worded report.

## Proof

yes: the 7f driver's watch check drops error events wherever they occur instead of requiring one
last (`notes/k8s-7f-scope.md`, §2.4 and §5); with upstream's validator the closed theorem would be
false under partitions.

## Notes

Test: [`k8s-etcd3-watcher-events-after-error/errorder_test.go`](k8s-etcd3-watcher-events-after-error/errorder_test.go),
package `etcd3` of this repository's `examples/k8s/etcd3` at branch `k8s-7e` `7f2ad6c9b5` (whose
codec decodes with no target, as `runtime.Decode` asks), `k8s.io/apiserver` `9c4ec15b8038`, go1.27,
under a 32G memory cap: a fake watcher sends 150 creates then a compacted response; a consumer that
starts reading after 100 ms saw the `Error` event before other events in 1 to 12 of 50 trials over
several runs (8, 3, 1, 8, 2, 12; e.g. `watch.Error at index 50 of 52 events`). Found 2026-11-08
writing the 7f Scope.
