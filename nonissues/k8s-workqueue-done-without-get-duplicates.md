---
upstream: none
checked: 2026-11-01
links: []
blocks-proof: no
---

# client-go's work queue hands one item to two workers after a `Done` without a matching `Get`

`Typed[T].Done(item)` for an item that is queued but not being processed (a second `Done` for one
`Get` while the item was re-added, or a `Done` for an item never handed out) pushes a second copy
into the FIFO, and two `Get`s then return the item to two workers at once, against the package's
"a single item will not be processed multiple times concurrently".

**Why not an issue:** a precondition Kubernetes' controllers meet: `Get`'s doc says "You must call
Done with item when you have finished processing it", and controllers call it once per `Get`, in
the standard `defer queue.Done(key)` pattern; a second `Done` is a caller bug. The fix (return from
`Done` when the item is not being processed) or a sentence on `Done` would be cheap hardening.

## Proof

no: `Typed.Done.spec` (`Spec/k8s_io/client_go/util/workqueue/Typed__Done.lean`) takes the item's
token, which only the `Get` that returned it gives and `Done` consumes, so a second `Done` is outside
the spec; the DaemonSet controller calls `Done` once per `Get`.

## Notes

Tests: [`k8s-workqueue-done-without-get-duplicates/done_test.go`](k8s-workqueue-done-without-get-duplicates/done_test.go)
(package `workqueue_test`), both fail in `util/workqueue` of `k8s.io/client-go@v0.37.2` (go1.27.3,
2026-11-01): `two concurrent Gets both returned "a"`, `after a double Done, two Gets both returned
"a"`. Only the deferred-`Done` pattern was checked across Kubernetes: a grep of `pkg/` finds about
ten non-deferred work-queue `Done` calls (taint eviction, pod GC, node lifecycle, PVC protection,
the leader-election controller) not audited for a double `Done`; finding one that can run twice for one
`Get` would make this an issue.
