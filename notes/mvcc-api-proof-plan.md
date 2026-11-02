# Proving mvcc's candidate API, then the tester's adequacy (plan, 2026-11-02)

The user (2026-11-02): once the review is done, prove the new specs (`<F>.specC`, vocabulary
`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`, `notes/mvcc-api-candidate.md`), then use
them to prove the adequacy of the mvcc tester (`examples/mvccrand`, `notes/mvccrand.md`).

## Where today's proof linearizes (the survey of 2026-11-02)

- **A commit** (`storeTxnWrite.End`, `Proof/.../mvcc/storeTxnWrite__End.lean`): under `s.revMu`
  held exclusively (:120-204): `currentRev++` (:138), then the ghost commit (the token spent,
  `γ.clog`, the log's authority from `revMuBody`'s `revQ` and the caller's `logQPre`,
  `idxWriterB_commit`, :140-155).
- **The watchable commit** (`watchableStoreTxnWrite.End`): under the watchable `s.mu` (:484-534):
  the seal (:498), `γ.rel` raised (:508), `notify` (:511), the inner `End` (:522, with `s.mu`'s
  `logQ` lent), `γ.wst`/`γ.wlog` advanced (:531).
- **A read** (`store.Read`): `s.revMu` shared (:70-110), a fraction `rfrac` of `revMuBody`.
- **A registration** (`watchableStore.watch`): the watchable `s.mu` exclusively, `s.revMu` shared,
  after :715 (`C = σ.Lmu`, nothing pending).
- **A compaction**: `updateCompactRev`, both locks exclusively, `compactMainRev = rev` (:226-227).
- **A restore**: `restore_takeover` (`RestoreMoves.lean:120`) under both locks moves the log's
  ghost state to the new log; `restore_switch` (:301) rebuilds `revMuBody`.
- Every fraction of `γ.clog`, `idxLogAuth`, `crevUB` is allocated: the abstract state needs ghost
  state of its own.

## The design

A mode of the store, `StoreNames.absQ : Bool := false` (today's specs and their clients: `false`,
unchanged), and two ghost names (`abs`, `pnd`, default `0`), used only when `absQ`:

- `γ.abs : ghostVar (Log × Int)`, the committed log and the compaction revision: the client's
  half (`mvccState`), a quarter in the writer's state (`writerL`: in `writerInv`, or the open write
  transaction's), and a quarter in `s.revMu`'s resource (`revMuBody`, at `q · ¼`), at
  `(log, c)` of that resource.
- `γ.pnd : ghostVar (Option (List Change))`, the revision notified and not committed: the client's
  half, a quarter in the writer's state, a quarter in the watchers' link (`relInv`, an invariant:
  the released length `γ.rel` is the notified log's, the notified log sealed) or, without
  watchers, in an invariant at `none`.
- `mvccState γ σ := ghostVar γ.abs ½ (σ.log, σ.crev) ∗ ghostVar γ.pnd ½ σ.pending ∗
  ⌜MvccReachable σ ∧ bound⌝`.

Where each atomic update fires:

| Operation | Fires at | Gathers |
|---|---|---|
| a read (`Read`, `Rev`) | under `s.revMu` shared, the log fixed | `revMuBody`'s fraction of `γ.abs` agrees |
| the bump (`storeTxnWrite.End`) | after `currentRev++`, with the ghost commit | `γ.abs`: client, writer, `revMuBody` (whole); `γ.pnd`: client, writer, the link |
| the notification (watchable `End`) | at `γ.rel` raised (:508) | `γ.pnd`: client, writer (the transaction), the link |
| a plain store's `End` | both at the bump | as the bump |
| a compaction | `updateCompactRev` :227 | `γ.abs`: client, `revMuBody` (whole), the writer's state (in `writerInv`: `s.mu` exclusively) |
| a restore | `restore_switch` | as a compaction |
| a registration | after `watch`'s :715 | the state unchanged: agreement only; the registrar's view updated |

`mvccTxn_write_agree` is the writer's quarters (a pure entailment). The watch laws read the link
invariant (released length, sealed notified log) against the client's halves.

## Stages

1. **P1, the mode and the ghost state**: the three fields; `revMuBody`'s and `writerL`'s new
   conjuncts (gated: `True` when not `absQ`), carried through the proofs that unfold and close them
   (`storeTxnWrite.End`, `store.Read`, `updateCompactRev`, `watch` x5, `syncWatchers`,
   `moveVictims`, `RestoreMoves`, `NewStore`, the fractional instance); `NewStore` allocates them.
   Today's specs unchanged, the build green.
2. **P2, the commit**: `storeTxnWrite.End`'s spec (and `metricsTxnWrite.End`,
   `txnReadWrite.End`, the watchable `End`) takes, in the mode, the caller's commit updates
   (gated pre and post); the watchable `End` fires the notification at :508.
3. **P3, the reads**: `store.Read` fires the caller's update (gated); `Rev` through it.
4. **P4, the predicates and the laws**: `Api.lean`'s opaque predicates defined over the
   implementation (sealed, `@[no_expose]`), the laws proved.
5. **P5, the tester's specs**: `New`, `watchableStore.Write`, `metricsTxnWrite.*`, the watchable
   `End`, `store.Read`/`Rev`/`Commit`, `NewReadOnlyTxnWrite`, `txnReadWrite.*`, `NewWatchStream`,
   `watchStream.*` (`Watch`'s registration: `watch`'s callback made a fancy update), from the
   generalized internal specs.
6. **P6, the rest**: `Compact` (`updateCompactRev`'s spec takes the update; the `ErrFutureRev`
   arm handled), `Restore`, the hash functions, the views, the plain store's `Write`, `NewStore`,
   `Close`.
7. **A1-A3, the tester**: its translation (done: project `mvccrand`, `cb10f4ec56`); the lessor's
   specs over the new API (`Revoke` over `mvccDeleter`; `NewLessor` without `clusterOk`, which only
   `Checkpoint` needs: the tester passes a `nil` cluster); the backend's opening (a premise, as
   the examples' `dbOpensOk`); the closed theorem.

## P1 as built (`cad9d508e3`)

- `StoreNames.absQ/abs/pnd`; `absAt γ q log`, `pndAt γ q p` (`True` when `γ.absQ = false`,
  `absAt_off`, `pndAt_off`); `revMuBody` holds `absAt γ q.half log` (`"Habs"`, before its pure
  conjuncts: a plain `iframe` reaches it); `writerL` and `storeTxnWriteIs` hold `pndAt γ ½ none`
  (`"Hpnd"`, after `"Hlrd"`); `storeTxnWriteCore` holds `pndEndB γ pend sealed` (`none`, or once
  sealed `some pend`: `pndEnd`; `storeTxnWriteIs_join` needs the unsealed one at `none`).
- **The gate**: `writerFrag γ` (the caller's eighth of `γ.cur`, which today's `Write`, `End`,
  `Commit` and `Restore` take) carries `⌜γ.absQ = false⌝` (`writerFrag_off`); `writerFragA` is the
  fragment without it. So today's specs are of old-mode stores and their proofs collapse the new
  conjuncts (`storeTxnWrite.End`'s commit, `restore_switch`); the client of an old-mode store holds
  `writerFrag`, made by `NewStore` (`γ.absQ = false` by construction).
- The abstract share was moved out of `restoreHeld` (dropped at the takeover, `True` in the old
  mode) and rebuilt at the switch; `restoreHeld`/`restoreWriter` carry `Hpnd`.

## P2's resource plan (what today's per-call client resources become in the abstract mode)

Today's specs take, per call, resources the new specs do not: the caller's reader ticket
(`storeReaderC`), revision token (`revToken`), write-back token (`storeWT`), the writer's fragment
(`hookIs`' `writerFrag`), a compaction lower bound (`crevLb`) and tag (`Z`); the watchable
store's writer pin (`watchWriter`). In the abstract mode they come from the store's own
invariants (in `isMvcc`):

- **reader tickets**: a pool holding the tickets and the deposited thread tokens of the calls that
  hold one (`threadToks k ⊢ k < T ≤ 2 ^ 30`: enough tickets);
- **write-back tokens**: `New`'s receipt-paid supply (persistent);
- **revision tokens**: a pool; or none, the overflow bound from the receipts (`idxCert`'s
  `logCh log < receiptBound`), in the abstract mode's commit;
- **the writer's fragment**: in the abstract mode, without `Restore` (stage P6 redesigns it), the
  store's objects are fixed: the fragment can be discarded into a persistent pin, which every
  writer reads (the pin agrees with every share; only `Restore` gathers the owned fractions);
- **`crevLb`/`Z`**: `crevLb (-1)` (persistent, free) and `Z := True`.

## Log

- 2026-11-02: plan; the tester translated (`etc/goose.py` project `mvccrand`; its type `rec`
  renamed `kvRec`, Lean's recursor's name).
- 2026-11-02: P1 built and committed (`cad9d508e3`; full `lake build` green, 11331 jobs).
