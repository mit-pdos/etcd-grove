---
upstream: none
checked: 2026-11-22
links:
blocks-proof: no
---

# etcdserver: one stalled request plus 2^48 later ids makes the server panic with "dup id"

A member's request ids are its 16-bit member prefix and the low 48 bits of an atomically incremented
counter (`idutil.Generator.Next`: `prefix | lowbit(suffix, 48)`), so the ids repeat after `2^48`
calls. `processInternalRaftRequestOnce` registers each request's id in the wait registry
(`s.w.Register(id)`), and `wait.Register` panics (`log.Panicf("dup id %x", id)`,
`pkg/wait/wait.go:63-74`) on an id that is still registered. A request's id stays registered from
`Register` until the apply thread or the request itself (on a failed proposal or its context's
timeout) calls `Trigger`. So if one request goroutine is not scheduled between its `Register` and its
`Trigger` while `2^48` further ids are issued (by requests, `LeaseGrant`, the read-index loop), the
next request with that id panics the server. The read-index loop's ids (`read.requestCurrentIndex`)
are not registered, but they use up the same counter.

**Why not an issue:** no test, found by code reading during the step-bound work (claim issue
mit-pdos/etcd-grove#30); it needs `2^48` (about 2.8·10^14) ids within one process lifetime while
one request stays registered: at a million requests a second, about nine years with one request
stalled throughout, which `ReqTimeout` (its context's deadline, then `Trigger(id, nil)`) prevents in
practice. Same generator as [`etcd-request-id-member-prefix`](etcd-request-id-member-prefix.md) and
[`etcd-request-id-restart-reuse`](etcd-request-id-restart-reuse.md).

## Proof

no: the top-level adequacy proofs bound the execution's length. The generator's invariant holds one
time receipt per id issued (`Proof/go_etcd_io/etcd/pkg/v3/idutil/Defs.lean`, D19b), so under
`receiptBound GF ≤ 2 ^ 48` a process issues fewer than `2^48` ids and they are distinct. That premise
is why the etcd examples' `Robust` statements cannot have a step bound above about `K · 2^48`, `K` the
fewest Go instructions a caller takes per id (about `2^6`, claim issue #30): the semantics has no
fairness or time, so it cannot exclude the stalled request, and an unbounded statement would be
false.
