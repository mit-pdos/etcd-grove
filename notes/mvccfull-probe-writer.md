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
3. **`runner.restore.spec` takes `ops.length ≤ Ops` and `Ops < 2 ^ 38`** (both `write`'s premises,
   which calls it): the builder's file `buildPath (nb + 1)` is among `writerOwn`'s unused files only
   if `nb + 1 ≤ Ops`, the builder's grants have write-back tokens (`Ops ≤ k + b.ops`) only while
   `b.ops < ops.length ≤ Ops`, and the snapshot's backend's kept tokens (`Ops + 1`, for the follower's
   later grants and `SetTxPostLockInsideApplyHook`) fit in `wbInit` only for a bounded `Ops`.
4. **`[ReceiptBoundLe GF (2 ^ 38)]`, not `2 ^ 48`, in `open`, `newMember`, `restart`, `restore`,
   `write`.** `inc_open_backend`'s premise `receiptBound GF + k + 4 ≤ backend.wbInit` (`wbInit =
   2 ^ 40 - 1`, `k ≥ Ops`) cannot be met from `receiptBound ≤ 2 ^ 48`: `open` and `restore` were
   unprovable. `Run` has `2 ^ 38` (as mvccrand's); `New.specR`'s `2 ^ 48` follows
   (`ReceiptBoundLe.pow_succ`).
5. `etc/link-lean-first-mvccfull.txt`: `runner__restore` takes `mvccClosed_rest.law` (for
   `inc_open_backend`); `Link.lean` regenerated.

## `runner.restore`: where the proof is (`runner__restore.lean`, one `sorry` left)

Proved, in Go's order: `builds++`; `buildPath`; `newMember(2, …)` on the first unused builder file
(the history's lower bound `hist0`); the loop `for b.ops < l.ops { apply(b, log[b.ops], false) }`
(the log's slice and its persistent `opIs`, `leadPre false` from the leader's lower bound, the
builder's write-back tokens from `Ops ≤ k + b.ops`); the builder retired (`inc_retire`, its whole
token: no reader or stream ever had a share) and `shut`, its file the image of `σOf ks ops l.ops`
(`inc_stop_image` inside `shut`) with the live leases' records; the follower's `revHi`, `cmpHi`
raised to the builder's inside its incarnation (`bnd_acc`: the bounds hold at the follower's state,
`revAfter_mono`, `cmpAfter_mono`); `openBackend` on the builder's file at a fresh registration;
`inc_open_backend` at the image.

Left (the `sorry`), with what each step needs, all checked against the statements:

- `kv := f.kv`; `f.le.Recover(newbe, func…)`. `Recover`'s premises: the records are the builder's
  (`leaseRecsOk (rbData P D) (leasesAfter l.ops)`, through `rbPart` of the new backend); `mono = false`
  (`lessorRevocable`); `id ∈ U → id ∈ L` from `logOk_recover` (`v1.U ⊆ grantedAfter v1.ops`, in
  `memCore`); `reqOf := 3600`; the `leaseReqIs`-or-fresh list from `lessorW`'s `□ [∗list] U`
  (a list-membership split); `leaseGranted γl id` from the guard `True` (**unfolds `lease.leaseGranted`:
  a missing law of lease, `leaseGranted_of_guard`**); the new backend's `isBackend` (`bkKeep`), an open
  share (`bkKeep`'s half, lent), two write-back tokens (`inc_open_backend`'s). With `Lr := L`
  (`leaseRecsOk`'s `recs.map (·.1) = L`), `leaseOwn γl L ∅` comes back, which `Restore` takes.
  The closure's `mvccDeleter` (the `kv` cell persisted; `KV.Write`'s contract; the
  `TxnWrite → TxnDelete` conversion) is a lemma to write.
- `f.kv.Restore(newbe)`: `KV.Restore.contract` (through `shapes.law`), at `σ' := σOf ks ops l.ops`
  (`MvccReachable` from `logOk_hist`, pure, `sorry`'d; items from `logOk_leases`, pure, `sorry`'d), the
  storage from `inc_open_backend`, the hook share `plHook γB nil` (`f = nil`), the update
  **`restore_au` (proved)**. Post: the new backend's share, the old storage's rest, the leases'
  items.
- `SetTxPostLockInsideApplyHook(f.hook)`: `plHook γB nil` to `f.hook`, then `plHook_persist` gives
  `hookIs` (**unfolds `backend.plHook`/`plHookRO` against `storageHook`'s `etcdStorage_hookIs`, a
  definitional equation of mvcc's API: fine**); a write-back token from the new `bkKeep`'s `k`.
- the old backend's census (`bkCensus` of the old `bkKeep` with `Restore`'s `storageRest`) and
  `backend.Close`; the fields; `revLo`/`cmpLo` stores (`bnd_acc` again: `revLo := σ'.rev`,
  `cmpLo := σ'.crev`, which hold after `Restore`); the checks (`KV.Rev`, `KV.Read`, `FirstRev`,
  `End`); `checkLeases`; the counter; `writerOwn` at `nb + 1` (the follower's `lessorW` on the new
  backend from `lessorApplyOk`, change 2, with `plHookRO γB f`).

No step found a false statement beyond changes 2-4; the risky ones (the builder's image, the
bounds' window, `Restore`'s update at a live incarnation) are proved.

## Laws still `sorry` (Writer.lean) and why

- `inc_open_backend`: `mvccrand.rc_open`'s proof at an image (`etcdStorage_open.law` in place of
  `mvccImage_fresh.law`) and `bkCensus` in place of `rcCensus`: mechanical, no invariant risk.
- the pure model lemmas `logOk_once`, `logOk_hist`, `runM_mono`, `logOk_leases`, `logOk_recover`
  (no invariant risk; `runM_mono`'s parts are now `revAfter_mono`, `cmpAfter_mono`,
  `runM_hs_prefix`, proved in `WriterShares.lean`).

## Unfolds of other packages' definitions (each a missing law of that package)

- `apply.bkRT` (etcdserver's apply package) in `inc_census`: its open share `bOpen rdOpen`
  (`bkRT_open : bkRT B ⊢ bOpen B.γB rdOpen ∗ …`).
- `backend.bStopView` (backend's `InvStop`) in `inc_stop_image`: its `rbOwn (rbData P D)`, against
  the writer's `rbPart` (`bStopView_rbPart_agree`).
- `backend.rbOwn` (an abbreviation of `rbPart γ ⊤`) with `backend.rbPart_agree` (a backend lemma,
  used as is).
