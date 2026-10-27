# Plan: the spec-first pilot, etcd's auto-compactor

Status: phase 0 done (2026-10-27, branch `compactor-pilot`): this note is phase 0's output, the
scope and the top-level statements. Scope **(A)**, the compactor and the server's compaction path
(the user, 2026-10-27). Next: phase 1.
Step 3 of `notes/spec-first-plan.md` ("Testing the plan").

## What the pilot is

Verify `server/etcdserver/api/v3compactor` (the auto-compactor: `compactor.go`, `periodic.go`,
`revision.go`; 14 functions, about 340 Go lines, 0% verified) spec-first, in the plan's phases (0
scope, 1 the spec skeleton and the glue proofs, 2 testing the specs against Go, 3 one full proof,
freeze, 4 the remaining proofs), and measure it against the read-index loop
(`server/etcdserver/read`, 10 functions, 178 lines), done the current way. Main metric: spec
revisions after the freeze, classified with step 1's rubric (success: at most 2 that are not INFRA,
none FALSE-BEH).

## What the proofs assume today

- `NewServer`'s premises have the compactor off: `AutoCompactionRetention = 0`
  (`examples/common/common.go:68`, every example's configuration). etcd's default is also off
  (`embed/config.go:71-72`: mode `periodic`, retention `"0"`).
- `v3compactor.New` is a trust-boundary axiom whose post is `True`
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/New.lean`, with the premise
  `ret ≤ -10 ∨ 10 ≤ ret` from `issues/etcd-compactor-periodic-tiny-retention.md`); the server's
  `run` sees the compactor only through `compactorOk` (`InvRun.lean`: nil, or `Pause`/`Resume`
  return), a names-only contract.
- **Compaction requests are outside the server's model**: `apply.dispatchOk` requires
  `dispatchKind rq ≠ .compaction` (`apply/InvUber.lean`; `notes/decisions.md`, "The server's apply:
  ... compaction out of the model", 2026-10-12), and `plainReq` admits no compaction
  (`KVModelDefs.lean`, `putgetKind`). mvcc's compaction itself is specified and proved
  (`store.Compact` and below, collection `mvcc-compaction`), under the premise `NoDelPutAt`; the
  client-facing `KVState` has a `compacted` revision already.

So turning the compactor on is not a 14-function change: its `Compact` calls go to
`EtcdServer.Compact` (`v3_server.go:382`), which proposes `InternalRaftRequest{Compaction}`
through raft, and every member applies it (`applierV3backend.Compaction`, `apply/backend.go:66`,
over mvcc's `store.Compact`). That is the first thing phase 0 found.

## The configuration (fixed now)

- Both modes, as etcd accepts them (`embed/etcd.go:928`, `parseCompactionRetention`): `periodic`
  with a retention duration (an integer means hours, e.g. `1`, the documented example; or a
  duration, `10m`), and `revision` with a revision count (`1000`, the documented example).
- Premise for `periodic`: a retention of at least 10ns (below, `getRetryInterval` is 0 and `New`
  divides by zero: `issues/etcd-compactor-periodic-tiny-retention.md`; etcd accepts it).
- The compactor runs on every member; `run` pauses it on a follower and resumes it on the leader
  (`server.go:762-785`). It starts in `NewServer`, before `Start`
  (`issues/etcd-compactor-started-before-start.md`): `Compact`'s contract must hold from then on.
- Other compactions (a client's `Compact`) stay out of the pilot's workload; the examples issue none.

## The top-level statements (drafts)

**C1, the compactor's guarantee** (the property operators configure it for: history is kept for the
retention). Every `CompactionRequest` the compactor sends has a revision `r` with `0 < r`, and:
- `revision` mode: `r + retention ≤ σ.rev` at the call (`r = Rev() - retention`, read before the
  call; the store's revision only grows);
- `periodic` mode: `r` is a revision the store had at a clock time at least
  `⌊period / retry⌋ · retry` before the call (`retry = min(period, 1h) / 10`; `revs[0]` was
  sampled `retentions - 1` iterations ago, each iteration waiting `retry` on the clock), so
  `r ≤ rev(now - ⌊period/retry⌋·retry)`;
- its requests' revisions never decrease (`Rev()` is monotone, and the periodic window only slides).

Not in C1: "no request after `Stop`". `Stop` only cancels the context, so a call in flight still
completes (with the context canceled). Phase 2 checks what `Stop` does guarantee.

The clock is a trust boundary (`clockwork.Clock`: `Now` monotone in the real clock's monotonic
reading, `After(d)` fires no earlier than `d`); phase 1 states it, phase 2 tests it.

**C2, the server with auto-compaction on** (option A only). The examples' closed theorems hold
when the server runs with auto-compaction on, in either mode, for any accepted retention: starting
with `putget_safe` (`examples/putget`), whose workload (puts and latest reads) never reads a
compacted revision; then the others. With compaction in the model, `KVState.compacted` advances at
a compaction's apply, reads below it answer `ErrCompacted` (the model has the field already).
Premise: the workload meets `NoDelPutAt` (no transaction deletes a key from-key and puts it again:
`issues/etcd-compaction-delete-then-put.md`, now reachable through auto-compaction alone; putget's
workload meets it trivially), until the fix (etcd-io/etcd#22377) is in the fork.

**C3, C1 in the KV model** (option A only): `σ.compacted ≤` the revision `C1` allows, for every
state the server reaches, given that only the compactor compacts. This is what a client relying on
the retention (a watch resuming within it) needs.

## The scope decision (the user's: (A), 2026-10-27)

- **(A) The compactor and the server's compaction path** (recommended): the 14 compactor functions;
  `EtcdServer.Compact`; `applierV3backend.Compaction` and the dispatch's compaction arm (the
  `dispatchOk` premise lifted for compactions); the KV model's compaction step and the server's
  invariants with compactions applied; `NewServer`'s `AutoCompactionRetention = 0` premise and the
  `New` axiom and `compactorOk` replaced; C1, C2 (putget first), C3. About 20 Go functions plus the
  model work. It is the plan's phase 0 doing its job: decided now, not found as a scope extension
  in phase 4 (step 1: 20 of 64 spec revisions were scope extensions).
- **(B) The compactor alone**: the 14 functions against a trust-boundary contract for its
  `Compactable` (an axiom on `EtcdServer.Compact`); C1 only; the server keeps auto-compaction off.
  Comparable in size to the read-index loop, so the cleaner experiment; but it narrows the scope the
  plan says to fix up front, and the axiom is exactly what a later widening would have to replace
  (with a re-proof of C1's callers).

Under (A) the pilot is larger than the baseline; the comparison then normalizes by functions and
Go lines, and counts the server-side spec revisions separately from the compactor's.

## Phase 1, once the scope is chosen

Write every spec of the chosen scope (the compactor's 14; the clock's; under (A) `Compact`'s,
`Compaction`'s, the dispatch arm's, the model step), proofs `sorry`; generate the links; prove the
glue: `New`'s dispatch, `NewServer` and `run` over `New.spec` (the compactor's goroutine's
proposals with `Compact`'s contract before `Start`), and under (A) `EtcdServer.Compact` over
`processInternalRaftRequestOnce`. Record the freeze candidates' state for phase 2.
