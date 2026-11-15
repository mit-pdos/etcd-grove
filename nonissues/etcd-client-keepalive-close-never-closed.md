---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# clientv3: a `KeepAlive` racing the lessor's `Close` can return a channel that is never closed

`lessor.KeepAlive` registers the lease's entry (checking `donec` under `l.mu` first) and only then
starts the receive and deadline loops through `firstKeepAliveOnce`. `lessor.Close` runs
`firstKeepAliveOnce.Do(func() { close(l.donec) })`. If `Close` runs between the two, its `Once`
wins: `donec` is closed, the loops never start, and nothing ever closes the entry's channels (the
receive loop's cleanup is what closes them). The context closer `KeepAlive` starts returns at once
on the closed `donec`, so even cancelling `ctx` does not close the channel, contrary to the
interface's documentation ("The returned channel closes if ... the given context is canceled",
`client/v3/lease.go`). A `concurrency.Session` built then never sees its `Done()` channel close.

**Why not an issue:** found by code reading (batch 1c's provability review, 2026-11-09); a liveness
bug (a goroutine blocks forever), no test. It needs `Close` (usually `Client.Close`) concurrent with
the first `KeepAlive` of the lessor. A test could promote it with a hook between the registration
and the `Once` (or many concurrent `KeepAlive`/`Close` pairs and a timeout on the channel's close).

## Proof

no: liveness only; the specs (`lessor.KeepAlive.spec`, `kaChan_recv.spec`) are partial correctness
and promise no closing.
