---
upstream: none
checked: 2026-11-14
links: []
blocks-proof: no
---

# The API server's etcd3 watcher can skip events once the watch is stopped or its context is done

After a storage watch's `Stop()`, or once the caller's context is done, the etcd3 watcher may drop
an event and still deliver a later one: the goroutine reading etcd's watch puts each event on the
processing queue with a `select` that gives up when the watch's context is done (`queueEvent`), and
goes on with the next events of the same etcd response or list page; the processing goroutine
chooses at random between the next queued event and the done context (`serialProcessEvents`,
`sendEvent`), so it can still take and send an event queued after the dropped one. In a test, 13 of
400 watches stopped mid-stream received e.g. revisions 6..44 and then 47.

**Why not an issue:** expected behaviour of a stopped watch: `watch.Interface` says `Stop` tells
the producer "to stop sending events and close the result channel", and promises nothing about the
events sent after it (the consumer only drains the channel until it closes); a done request context
ends the watch the same way. The API server's consumers stop using a watch's events once they stop
it or their context is done. Reproduced through a fake `clientv3.Watcher`, not a real etcd. Not
searched upstream (no GitHub access from the session that recorded it).

## Proof

no: the store watch's spec (k8s 7f-5a, `Proof/k8s_io/apiserver/pkg/storage/etcd3/Draft7f5a.lean`,
`kResElem`) claims the no-gap prefix only while the watch is live (not stopped by the consumer, its
context not done: `kCancelled`), and after that only that the events are a subsequence of the ideal
stream (in order, none invented, none repeated); the 7f driver checks the events it received before
it stopped the watch.

## Notes

Test: [`k8s-etcd3-watcher-gap-after-cancel/gap_test.go`](k8s-etcd3-watcher-gap-after-cancel/gap_test.go),
copied into this repository's `examples/premisefix/watcherctx` (branch `k8s-7f5`), `k8s.io/apiserver`
`9c4ec15b8038`, go1.27.3, GOWORK=off, under a 32G memory cap: a real `etcd3.New` store
(`ConcurrentWatchObjectDecode=false`, RV 5, recursive, `Everything`) over a fake watcher that streams
one create per response, paced by the consumer, and once the context is done sends one buffered
5-event response; `Stop()` at a varying time. Runs: 11, 16 (the review's), 13 (2026-11-14) of 400
trials with a gap. The test passes when it observes a gap.
