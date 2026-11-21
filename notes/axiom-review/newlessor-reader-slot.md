# `lease.NewLessor`: one reader slot too many (axiom review, 2026-11-21)

**Reviewed** (lean at `e258f61bfa`, prove-ps2-newlessor, issue #18): the trust-boundary axiom
`lease.NewLessor.wp_proof` (`Proof/go_etcd_io/etcd/server/v3/lease/NewLessor.lean`, triple in
`Spec/go_etcd_io/etcd/server/v3/lease/NewLessor.lean`), against `newLessor` and `runLoop`
(`server/lease/lessor.go:212-249, 617-662`, the etcd pin).

## Verdict

**False of the model** (over-grants one reader). The post gave the caller
`[∗list] _ ∈ List.replicate (Int.toNat actualMaxReaders) (), lessorRdOf γl`: every reader slot of
the lessor's `le.mu`. Perennial's `sync.init_RWMutex` makes exactly `Int.toNat actualMaxReaders`
slots (`RWMutexGuard.lean`; its fixed authority `ownTokAuthDfrac γmax discard actualMaxReaders`
bounds the readers by them), and `RWMutex.RLock` takes one (`RWMutex.wp_RLock_of`). But
`newLessor` forks `go l.runLoop()` (`:245`), and `runLoop` calls `revokeExpiredLeases`, which does
`le.mu.RLock()` (`:640`) on every iteration, concurrently with the caller's readers. So the program
holds up to `actualMaxReaders + 1` readers while the axiom lets the caller use all
`actualMaxReaders` slots: no proof of the real code can give them (the count is fixed by the mutex's
ghost state, and a pool built by the caller from the post's slots cannot reach the forked loop).

In Go the excess is not reachable in practice (`2^30` concurrent readers of the lessor), and the Go
`RWMutex` misbehaves beyond `rwmutexMaxReaders` readers: the model's bound is what the axiom
violated, so the statement was unprovable rather than refuted by a run.

## Repaired

The post gives `Int.toNat actualMaxReaders - 1` slots; `runLoop` keeps one for its lifetime (the
user's approval, 2026-11-21, on the condition that every caller proves on top of it). Callers
adjusted (slot arithmetic only): `etcdserver/NewServer.lean`, `NewServerR.lean`,
`examples/mvccfull/runner__open.lean`, `examples/mvccrand/runChecks.lean`. Ledger:
`notes/specs-only/ledger.md`, 2026-11-21, "`lease.NewLessor`'s reader slots".

## What a proof over the real code still needs (open, 2026-11-21)

Not the slot any more. Two statement questions, for the user:

1. **`expiredC`'s payload.** The post's `lessorExpiredC lp GA` says every slice sent on `expiredC`
   carries `⌜¬ leasesNoExpiry⌝`, an `opaque Prop` (`LessorBackend.lean`) that the top-level lease
   theorems take as a premise about the run. Perennial's `time.Now` returns arbitrary readings, so
   `l.expired()` returning true in `findExpiredLeases` proves nothing about it: this axiom is the
   only link between the premise and the code. A proof needs either a narrow trust-boundary fact
   that is the premise's meaning (under `leasesNoExpiry`, the expiry loop's `l.expired()` returns
   false), replacing this axiom, or a premise defined over the loop's observations.
2. **A thread bound.** `l.expired()` read-locks the lease's `expiryMu`, whose only reader slots are
   in `isLeaseObj`'s pool, which exists under `⌜threadBound GF ≤ 2 ^ 30 - 1⌝` only. The pre has no
   thread bound (every caller has `threadBound GF ≤ 2 ^ 29`; `Promote` and `Renew` take the same
   premise).

And one design (no decision): `expireExists` writes the expiry notifier under the read lock only
(sound in Go: `runLoop` is its only caller), so the notifier must leave `lessorMu`'s fractional
`lessorExtra` for a cell the writers (whole lock) and `runLoop` (its read share and an exclusive
token) take in turn.
