# mvccfull Probe: the stamp (`stream.recvOne`) and `stream.complete`

Stage F1, Probe (`notes/mvccfull-proof-plan.md`). 2026-11-09.

## Result

- `stream.recvOne.wp_proof` proved, no `sorry`
  (`Proof/github_com/mit_pdos/etcd_grove/examples/mvccfull/stream__recvOne.lean`).
- `stream.complete.wp_proof` proved, no `sorry` (`stream__complete.lean`; callee `expect`).

## Strength of the invariants

`smuInv`/`smuBody`, `watcherOwn'`/`watcherOk` and mvcc's `wsChan_recv.law` (second form) and
`wsSentLb_zero.law` were strong enough as drafted: no change to a spec, to `Streams.lean` or to
mvcc's API.

- The stamp: `regs_sentLb` gives the poll's bound `n` (at least every registration's `k`, with
  `wsSentLb ws n`); the default arm of the non-blocking receive gives `n ≤ |rs0|`, so `stamp_ok`
  and `watcherOk_stamp` keep each watcher's `watcherOwn'` when it is stamped. The loop over
  `s.order` needs no record of which watchers are stamped: its invariant is the lock's
  `[∗map]` unchanged (each id of `s.order` is in the registry, `smuBody`'s order fact).
- The blocking receive after the lock is released: on relocking, the lock's received list agrees
  with the receiver's half of `σs.rcv` (`ghostVar_agree`), so `receive` applies at `rs0 ++ [r]`.
- `complete`: `expect` is called at the spec's own history bound `Hlb` (no need to compare it with
  the lock's `Hl`); `0 ≤ rev`, `0 ≤ index` come from `wPosOk'`.

## Changes (all additive, in files this probe owns)

- `StreamLemmas.lean`: `streamCtx_persistent` (given mvcc's `persistent.law`), so `recvOne` keeps
  `streamCtx` to pass to `receive` (whose spec consumes it) after destructuring it. It unfolds
  only mvccfull's own definitions (`streamCtx`, `epCtx`, `rnCtx`, `isInc`, `ctrInv`,
  `runnerKeys`, `runnerH`). Suggestion (not done, shared files): `Persistent` instances for
  `isInc` (needs `persistent.law`), `ctrInv`, `runnerKeys`, `runnerH` in `Members`/`Readers`.

## Unfolds of other packages' definitions

None (the mvcc laws were used as stated).

## Leftovers

- `Streams.lean`'s `maxK_attained` is still `sorry`; `StreamLemmas.lean`'s `maxK_attained'` proves
  it. Delete the former (or prove it by the latter's argument) when `Streams.lean` is next edited
  (an edit rebuilds its importers).
