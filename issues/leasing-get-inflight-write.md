---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#20704 issue closed: same bug, its bugs 2 (a failed Put closes the waiter, the Get serves the evicted entry) and 4 (a second write replaces the waiter channel); closed by the stale bot, unfixed. Its bugs 1 and 3 are issues/leasing-update-stale.md
---

# clientv3/leasing: a cached Get does not wait for every write of the key in flight

## Status

A bug (a stale read, against the package's "linearizable reads" documentation). A cached `Get`
through the leasing KV waits on the key's waiter channel before it answers from the cache. In two
cases the channel closes while one of this client's writes of the key may already be committed at
etcd and not yet reflected in the cache. The `Get` then returns the value from before that write,
after another client may already have read the written value.

## Where

At the etcd pin `107edf7e4`, the same on upstream `main` (`b25719d10`):

- `leaseCache.Lock` (`client/v3/leasing/cache.go:53-61`) gives each write a fresh waiter channel
  and *replaces* the entry's `waitc` with it.
- `leaseCache.Get` (`cache.go:191-210`) reads the entry pointer `li` and its `waitc` once
  (`notify`, `cache.go:231-238`), waits for that channel, then answers from `*li`
  (`cache.go:206`) without checking that `li` is still the key's entry.
- `leasingKV.tryModifyOp` (`kv.go:218-234` on `main`; `kv.go:224-244` at the pin, with Goose's
  copy of the `fallthrough`): when the write's transaction returns an error, it calls
  `Evict(key)` and then `close(wc)`. The write's outcome is unknown at that point. `put` and
  `delete` then retry through `revoke`.

## What happens

1. **A failed write releases the waiter but not the entry the Get holds** (#20704's bug 2). A
   `Put(k, v2)` locks `k` (channel `wc`) and its transaction commits at etcd, but the response is
   lost (a partition or timeout), so `Commit` returns an error. Another client reads `v2`. A
   `Get(k)` on this leasing KV, started after that read, finds the entry `li` and waits on `wc`.
   `tryModifyOp` evicts `k` and closes `wc`. The `Get` wakes and answers from the evicted `*li`:
   `v1`. The integration test `TestLeasingConcurrentPutGet` on the fork (`upamanyus/etcd`
   `e11ce2ae7`, `tests/integration/clientv3/lease/leasing_test.go:36-121`) exercises this with a
   bridge partition, but not deterministically.
2. **A second write replaces the waiter** (#20704's bug 4). `Put1(k, v1)` locks `k` (`wc1`), then
   `Put2(k, v2)` locks it (`wc2` replaces `wc1` in the entry). `Put2` commits at `r2`, updates the
   cache to `v2` and closes `wc2`. `Put1` then commits at `r1 > r2`, and another client reads `v1`.
   A `Get(k)` started after that read sees `wc2`, which is closed, and returns `v2` while `Put1`'s
   response is still in flight.

Both are reproduced at the cache level, deterministically, by unit tests in package `leasing` at
the pin, `issues/leasing-get-inflight-write/get_inflight_write_test.go`:

```go
// 1: lc.Add(k, …v…); wc := lc.Lock(k); go lc.Get(ctx, OpGet(k)) (it waits on wc);
//    lc.Evict(k); close(wc)  →  the Get returns the evicted entry's v
// 2: lc.Add(k, …v…); wc1 := lc.Lock(k); wc2 := lc.Lock(k);
//    lc.Update(k, v2, rev 3); close(wc2)  →  lc.Get returns v2 at once, wc1 still open
```

(`TestTriageGetServesEvictedEntry` and `TestTriageGetIgnoresFirstWriter` both fail at the pin.)
The end-to-end staleness also needs the network timing above.

## Expected

`doc.go:15`: "Package leasing serves linearizable reads from a local cache". A cached `Get` should
not complete with a value older than one another client has already read.

## How the proof handles it

The specs state both behaviors, and the cached-read theorem is scoped so that it does not claim
linearizability against this client's own writes:

- `leaseCache.Get.spec` (`Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__Get.lean:27-42`)
  returns an entry that is the key's entry *or frozen* ("evicted after it was found",
  `(o.key, e) ∈ st.frozen`), which is case 1.
- `leaseCache.Lock.spec` (`leaseCache__Lock.lean:36-38`) hands each writer its own `waitcClose wc`,
  and nothing relates a `Get`'s wakeup to the other writers' channels, which is case 2.
- `getCached` (`Proof/go_etcd_io/etcd/client/v3/leasing/InvLeasingKV.lean:414-417`) says only that
  the answer is the entry's cached record, whose facts are etcd's record at the acquisition. The
  freshness corollary `leasing_cached_get_stable` (`Results.lean:180-187`) holds only while "the
  holder commits nothing" (`h.writer z ≠ e.lease` on `(e.rev, b]`). In both cases the holder's own
  write has committed.

## Possible fixes

- `Get`: after waking, under the read lock, serve only if `lc.entries[key] == li` and `li.waitc`
  is closed. Otherwise loop, or fall back to the server (returning `nil, true`). That handles
  case 1, and case 2 too if the re-check finds the newer channel still open. It still misses
  `Put1`, though, once `wc2` has closed.
- Count the writes in flight per entry (`li.pending++` in `Lock`, and `--` before each close),
  with a channel closed only when the count is zero. A cached `Get` then waits for every write of
  the key. Alternatively, `Lock` waits for the previous channel before installing its own, which
  serializes the writes of a key.
- On an unknown outcome (`Commit` error), leave the waiter open until the entry is evicted and
  every `Get` holding `li` falls back to the server. The first fix does this when it re-checks
  that the entry is still current.

## Found

Reported upstream by upamanyus as etcd-io/etcd#20704 (2025-09-23). Recorded here on 2026-10-16 by
the bug triage of #20704 against the leasing specs (`notes/bug-triage/etcd-20704.md`), with the
cache-level reproductions.
