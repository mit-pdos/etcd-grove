---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22123 issue open: this bug (Resign forgets its leader state when its delete fails)
  - etcd-io/etcd#22211 pr open: the fix (clear the state only after a successful transaction); verified, notes/pr-verify/etcd-22211.md on branch pr-verify/etcd-22211
  - etcd-io/etcd#22124 pr open: the same code change (only a code comment differs), with its own test; verified, notes/pr-verify/etcd-22124.md on branch pr-verify/etcd-22124
---

# Election.Resign forgets the leader key when its delete fails

## Status

A bug: a failed `Resign` leaves the leader key in etcd but makes the `Election` forget it, so a
retried `Resign` is a no-op that returns nil, and the key stays (blocking every other candidate)
until the session's lease ends.

## Where

`client/v3/concurrency/election.go` at the pinned fork revision `09669450f`, lines 132-146
(`Election.Resign`): the guarded delete's error is returned, but lines 142-143 clear
`e.leaderKey` and `e.leaderSession` whatever the outcome. `Resign`'s documentation ("lets a
leader start a new election") says nothing about the error case.

The same happens inside `Campaign`'s cleanup calls (lines 87 and 98): if the cleanup `Resign`
fails, the campaign's key stays in etcd and the `Election` can no longer delete it.

## What happens

1. Campaign and win (`e.Key()` is the leader key).
2. `e.Resign(ctx)` with an already-canceled `ctx`: the transaction is never sent, `Resign`
   returns `context.Canceled`, the key is still in etcd.
3. `e.Key()` is now `""`; `e.Resign(goodCtx)` returns nil without sending anything (the
   `leaderSession == nil` shortcut), and the key is still there.

Reproduction: `notes/pr-verify/etcd-22211/election_resign_retry_test.go` on branch
`pr-verify/etcd-22211` (the regression test of etcd-io/etcd#22211, renamed); copied into
`tests/integration/clientv3/concurrency/` of the fork at `09669450f` it fails with `expected:
"/resign-retry//<lease>", actual: ""` (`notes/pr-verify/etcd-22211/pinned-09669450f.log`).

## Expected

A failed `Resign` keeps the election's state, so that the caller can retry; only a successful
transaction (the key deleted, or the guard `CreateRevision(key) = rev` failed because it was
already gone) clears it. The guard makes a retry safe when the first attempt was applied but
reported as an error.

## How the proof handles it

No premise: the spec on `lean` states the behavior as it is
(`Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Resign.lean`, the error case's
postcondition `electionState e s ⟨[], st.rev, null, st.hdr⟩`: key and session cleared). On branch
`pr-verify/etcd-22211` the spec's error case is `electionState e s st` (unchanged), proved of the
fixed code.

## Possible fixes

etcd-io/etcd#22211 (or the identical #22124): return the error before clearing the state. Alone,
that interacts badly with `Proclaim`, which on `ErrElectionNotLeader` clears `leaderKey` but not
`leaderSession` (line 123): every later `Resign` then sends a delete of the empty key, etcd rejects
it ("key is not provided"), and the state is kept, so `Resign` fails until the next successful
`Campaign` (`notes/pr-verify/etcd-22211/election_resign_lost_proclaim_test.go`). A complete fix also
has `Proclaim`'s not-leader branch clear `leaderSession`, or `Resign` treat `leaderKey == ""` as
nothing to delete.

## Found

2026-10-17, while verifying etcd-io/etcd#22211 (the bug had been reported upstream as #22123; the
`lean` spec recorded the behavior without flagging it).
