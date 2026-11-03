---
upstream: none
checked: 2026-10-26
links: []
blocks-proof: yes
---

# clientv3: a reconnect with 2^31 or more watches on one stream panics in its wait group

On a reconnect, `waitCancelSubstreams` adds every resuming watch to a `sync.WaitGroup` in one
`wg.Add(len(w.resuming))`
([L976](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/watch.go#L976));
the counter is an `int32`, so with 2^31 or more watches on one stream `Add` panics ("negative
WaitGroup counter"), and with 2^32 + m it is m and `Done` panics later.

**Why not an issue:** no test, out of reach: it needs 2^31 watches on one gRPC stream, each with its
own goroutine (terabytes of stacks). The user's 2026-10 review: skip.

## Proof

yes: the verified fork carries the fix (`2aed163b1`, from `b3c29bc17` on branch `watch-resume-fixes`:
`wg.Add(1)` before each `go`); `sync.WaitGroup.Add`'s spec needs a counter below 2^31, which the
thread bound gives per goroutine started but not for `len(w.resuming)` at once
(`Proof/go_etcd_io/etcd/client/v3/InvWcJoin.lean`).

## Notes

The user noted (2026-10) that thread tokens do not rule it out, since the resumed goroutines may exit
before `resuming` is filled; that is why the proof needed the fix.
