# mvccfull Probe: the writer's restart and restore chains (2026-11-09)

The Probe of stage F1 (`notes/mvccfull-proof-plan.md`) on the writer's riskiest bodies: `runner.restart`
(the incarnation swap) and `runner.restore` (the builder to `Restore` handoff). What was proved, what
changed and why, what is left.

## Proved

- `runner.restart` (both members, `runner__restart.lean`), over the specs of `stopReaders`,
  `endEpoch`, `shut`, `open`, `startEpoch`, `startReaders` and the laws below. The shares lent to the
  readers and streams are gathered back (`WriterShares.lean`: `shares_join`, from `lentOk`), the
  incarnation retired (`inc_retire`), its contents split (`memberState_split`), the writer's halves
  agreeing with the invariant's (so the closed state is `σOf ks ops v.ops` and the bounds `v.b`), and
  after `open` the same shares lent again at the new incarnation (`shares_split`), so `writerOwn`'s
  `q`, `qs` are unchanged and the other member's parts untouched.
- `Writer.lean`'s laws: `memberState_split`, `inc_retire`, `inc_census`, `inc_stop_image`, `inc_alloc`.
- `RestoreLemmas.lean`: `restore_au`, `Restore`'s update at the follower's incarnation invariant
  (the follower's readers and streams run throughout: the writer's live share opens the invariant,
  its halves pin the state and the bounds, the counters grow along the log prefix).
- `WriterShares.lean` (pure): `runM_hs_len`, `runM_hs_prefix`, `revAfter_mono` (so the restart needs
  none of the `sorry`'d `runM_mono`/`logOk_hist`).

## Changes (what, why, which statements)

1. **`Writer.lean` prefers `History.lean`'s `Pos.Countable` instances of `MvccState` and `Change`**
   (`attribute [local instance high]`). `Writer.lean` imports mvccrand's writer stack, which declares
   its own (equal bodies, distinct constants); `incW`/`memberCarry`'s ghost variables were elaborated
   with mvccrand's, `memberState`'s (Members.lean) with History's, so `ghostVar_agree`/`icombine` of
   the writer's half against the invariant's failed (they only matched up to unfolding). No statement's
   meaning changes; `incW`, `memberCarry`, `lessorW`, ... are re-elaborated (importers rebuilt; all of
   `runner__*` built). Better still: mvccrand's duplicates should go (a shared module of the two
   testers' instances).
2. **`lessorW` holds `lessorApplyOk lp`** (NewLessor's contract of the lessor on *any* backend), besides
   the contract on its current backend. `lessor.Recover` (in `restore`) moves the lessor to the
   snapshot's backend and gives no contract for it; `lessorW` for the follower after the restore needs
   `lessorBackend` at the new backend, which only `lessorApplyOk` (in `NewLessor.specR`'s post, so
   `open` has it) provides. Statements changed: `lessorW` (so `memCore`, `memW`, `writerOwn`), additive.
3. **`runner.restore.spec` needs `ops.length ≤ Ops`** (to come, with the restore proof): the builder's
   file `buildPath (nb + 1)` is in `writerOwn`'s unused-file list only if `nb + 1 ≤ Ops`, and the
   builder's grants need write-back tokens (`Ops ≤ k + b.ops`) only while `b.ops < ops.length ≤ Ops`.
   `write`'s spec has the premise; `restore`'s did not.
