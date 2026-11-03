# mvcc's API: the invariants (informal; 2026-11-03, branch `mvcc-api`)

The user's plan: specs frozen, then the invariants informally, frozen, then the proofs (the
functions' and the laws', in parallel). The specs: `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`
and `ApiState.lean` (frozen 2026-11-03, `notes/mvcc-api-candidate.md`, "The freeze"). This note
says what each opaque predicate of the API is over `lean`'s internals, where each atomic update
fires, and what the internals must gain. It is over `lean`'s mvcc (the survey of 2026-11-03: the
internals since M2), not round 9's old ones (`notes/mvcc-api-proof-plan.md`, whose abstract mode
does not exist on `lean`; its design is the template). **Status: draft.**

Paths are under `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/`.

## 1. New ghost state

Every fraction of the store's logical ghost state (`γ.clog`, `idxLogAuth`, `crevUB`) is already
allocated, so the abstract state gets names of its own (fields of `StoreNames`, `WsStreamNames`):

| Name | Type | Shares |
|---|---|---|
| `γ.abs` | ghost variable `Log × Int` (`σ.log`, `σ.crev`) | ½ the client (`mvccState`), ¼ `s.revMu`'s body (`revMuBody`), ¼ the writer's state (`writerL`, or the open write transaction) |
| `γ.pnd` | ghost variable `Option (List Change)` (`σ.pending`) | ½ the client, ¼ the writer's state, ¼ the watchable `s.mu`'s body (`watchStoreBody`, beside `γ.rel`); for a store without watchers, an invariant holding it at `none` |
| `ι.sst` | ghost variable `StreamState` | ½ the client (`wsState`), ½ the stream's mutex invariant (`watchStreamInv`) |
| `ι.rcv` | (none new) | the consumer's view is today's `watchConsumer` half of `recv` |

The ghost state is allocated by `NewStore` (and `newWatchableStore`, `NewWatchStream`); it is always
there, in every store: no mode (round 9's `absQ` gate is not needed: the old specs go when the API
replaces them).

## 2. The predicates

- **`mvccState γ σ`**: `ghostVar γ.abs ½ (σ.log, σ.crev) ∗ ghostVar γ.pnd ½ σ.pending` ∗ the
  certificate map's authority (`ghostMapAuth γ.cok 1 M`, today `NewStore`'s caller's) with every
  entry a prefix of `σ.notifiedLog` (`certMapOk`) ∗ `idxCert γ.idx σ.log` ∗
  `⌜MvccReachable σ ∧ σ.log.length + 3 ≤ 2 ^ 63⌝`. The map makes the watch laws pure entailments:
  every log the implementation certifies (a read's, a watched log `evLog`) is in it, so a prefix of
  the notified history.
- **`isMvcc kv γ`**: `kv` is `mkOk (Ptr store) s` with `isStore s γ.st`, or `mkOk (Ptr watchableStore)
  ws` with `isWatchableStore ws s γ`; and the pools: the readers' pool (a `ThreadPool` of
  `storeReaderC`, with a watchable `s.mu` reader slot `watchReader` when watched: a reader borrows one
  for its thread token and gives it back at its `End`), the revision budget from receipts (the
  index certificate's `⧖ (logCh log)` bounds the revisions: no revision tokens), the write-back
  supply (`□ (⧗ 1 ={⊤}=∗ wbTok)`, from `mvccBackendFor`), the watch tokens' pool (`watchTokPool`,
  receipt-paid); and, without watchers, the invariant holding `γ.pnd ¼` at `none`.
- **`mvccOpen γ`**: the closer (`storeCloser`, `wsCloser`), the compaction right (`compactRightR`,
  exclusive on `lean` too: the API's exclusive token matches it), and the restore's pieces
  (`fieldShare ¼`, `wsDep`, `writerOwn`/`retiredAt`).
- **`mvccBackend γ q B Pk`**: a fraction `q` of the writer's fragment (`writerFrag`/`curAt`) at the
  store's physical names (`γ.withPhys p`, `p.bucket = B.γB`, the backend `B.b`, its parameters
  `B.P`) and the batch lock's invariant `Pk`: the agreement law from the fragment's ghost variable;
  `Restore` gathers the whole and switches the physical names (`restore_switch`).
- **`mvccTxn t γ trace k`**: at `.read σ`, today's read transaction (`isTxnRead`/`isTxn` of a
  `*metricsTxnWrite` or `*txnReadWrite`) at `σ.log` and `σ.crev` (`crevLb`), with the pool's loan;
  at `.write σ pend`, today's write transaction (`isTxnWrite ilog pend`, with `ilog = σ.log`) of a
  `*metricsTxnWrite`, or the watchable wrapper over one (its struct read-only), holding the writer's
  `γ.abs ¼` at `(σ.log, σ.crev)` and `γ.pnd ¼` (at `none`, then the notification's `some pend`
  inside its `End`), the pool's loan, and the batch lock's invariant's hook resource.
- **`isMvccWatchStream ws γ ι`**: today's stream (`isWatchStream` at `storeWatchParams`: the reader
  `watchReader`, the watch token, `watcherIs`), its channel and channel invariant, and the stream's
  mutex invariant extended with `ι.sst ½`, agreeing with `closed` and `idsInv` (each id's watcher:
  its range, filters and first revision from `watcherIs`, its stamp `k` from `chanRegAt k`, live
  until its cancel's first check).
- **`wsState ι S`**: `ghostVar ι.sst ½ S`.
- **`wsRecv ι rs`**: the consumer's half of `recv` at the received `RespM`s `ms`, `rs = ms.map
  respView` (dropping the internal fields `w`, `cov`, `regs`, `idx`), and for each received response
  its persistent facts, resolved at the receive: `watchRecvOk` (the watcher's received prefix is the
  kept deliveries of `watchEvents L r lo d` of a certified log), `respCov`/`respCompl` with
  `regsAt` already resolved (it spends a later credit: the receive law, `wsChan_recv`, has one),
  `chanRegFact`, `respRev`, and the compaction response's `crevLb` (new, below).

## 3. Where each update fires

| Update | Fires at (on `lean`) | Gathers |
|---|---|---|
| a read (`Read`, `Rev`, `FirstRev`, the store's `Range`) | `store.Read` under `s.revMu` shared (`store__Read.lean:70-122`), the log fixed (:76) | `revMuBody`'s ¼·q of `γ.abs`: agreement |
| `Write`'s begin | `writerInv_checkout` (`store__Write.lean:127`), under the batch lock and `s.mu` shared | the writer's `γ.abs ¼`, `γ.pnd ¼` (at `none`): agreement |
| `End`'s notification (watchable) | `γ.rel` raised (`watchableStoreTxnWrite__End.lean:508`), under the watchable `s.mu` | `γ.pnd`: the client's ½, the transaction's ¼, `watchStoreBody`'s ¼ |
| `End`'s bump | `currentRev++` with the ghost commit (`storeTxnWrite__End.lean:141-160`), under `s.revMu` | `γ.abs`: the client's ½, `revMuBody`'s ¼, the transaction's ¼; `γ.pnd` back to `none` |
| a plain store's `End` | both at the bump | as the bump, with the `none` invariant's `γ.pnd ¼` |
| `Compact` | `compactMainRev` written (`store__updateCompactRev.lean:220`), under `s.mu` and `s.revMu` exclusively | `γ.abs`: the client's, `revMuBody`'s, the writer's (in `writerInv`: no write transaction holds `s.mu`) |
| `Restore` | between `restore_takeover` and `restore_switch` (`store__Restore.lean:154-398`), under both locks | `γ.abs` whole, `γ.pnd` (at `none`) |
| `Watch`'s registration | inside `watchableStore.watch` after the current revision's read (`watchableStore__watch.lean:716`), under the watchable `s.mu` and `s.revMu` shared; the stream holds its mutex across | the store's `γ.abs`/`γ.pnd` shares (agreement; `pending = none` from `watchStoreBody`'s), the stream's `ι.sst` (the client's ½ and the mutex invariant's ½: insert) |
| `Watch` on a closed stream | the `closed` check (`watchStream__Watch.lean:77`) | `ι.sst`: agreement |
| `Cancel` | its first check of the maps (`watchStream__Cancel.lean:38-43`) | `ι.sst`: the watcher not live |
| a stream's `Close` | `closed` written (`watchStream__Close.lean:~99`) | `ι.sst`: `closed` |

## 4. What the internals must gain

1. **The ghost state of section 1**, in `revMuBody`, `writerL`, the open transactions, `watchStoreBody`,
   `watchStreamInv`, and its allocation in `NewStore`/`newWatchableStore`/`NewWatchStream`; carried
   through every proof that opens and closes those (the survey's list: `storeTxnWrite.End`,
   `store.Read`, `updateCompactRev`, `watch`, `syncWatchers`, `moveVictims`, `RestoreMoves`,
   `NewStore`, the fractional instances). The first stage, sequential: everything else needs it.
2. **The watch guarantee per watcher under compaction**: `lean` covers compaction only under a global
   premise per registration (`watchNoDup = noCompactor ∨ noDupKeys`, `InvWatchStore.lean:544`,
   `storeWatchParams.T`). The API's condition is per watcher (`onceUpTo L lo crev`); the watcher's
   delivery invariant becomes "exact while the condition holds" (one implication, carried: the
   catch-up read after a compaction at `c` returns revision `c`'s last change per key, all of it
   under the condition). No second path.
3. **A compaction response's revision at most the compaction revision**: recorded at the send
   (`crevLb` under `s.revMu`, at `syncWatchers`' `choose`), where `respOk` says today it is not
   (`:484-486`).
4. **`Compact`'s `ErrFutureRev` arm**: `lean` excludes it by the caller's certificate premise; the
   contract has the arm (no channel, `Pre ∗ X` back).
5. **The readers' and write-backs' resources**: the readers' thread pool (Perennial's `ThreadPool`),
   the revision budget from receipts (`idxSealed_small`), the write-back supply (`kbWTSupply`,
   ungated: `kbWTSupplyM_of_stock` gives the gated one only).
6. **A store without a hook**: `bt_lockIn` over `plHookRO γ nil` from `LockInsideApply`'s `nil` arm,
   and `bkHookIs` relaxed (`≠ nil` dropped).
7. **The backend law** (`mvccBackendFor_open`) over `newPostKP`, and the boot path rewired to it
   (`bootBackend_of_newPost` today takes `newPostP`; `newPostK_pool` at `K := bFresh` gives
   `newPostKP`).

## 5. The proofs, after the freeze of this note

Sequential first: the ghost state (4.1), the predicates' definitions (section 2, sealed:
`ApiImpl.lean`), the pools (4.5), the backend law (4.7). Then in parallel, each a file of its own:
the contracts' proofs per (type, method) (the store's: `Read`, `Write`, `Rev`, `FirstRev`, `Range`,
`Put`, `DeleteRange`, `Compact`, `Commit`, `Restore`, `HashStorage`, `Close`, `NewWatchStream`, for
both store types; the transactions' seven for each of the three types; the stream's seven), the
constructors' (`New`, `NewStore`, `NewReadOnlyTxnWrite`), and the laws (`persistent`, `excl`,
`mvccBackend_agree`, `mvccState_reachable`, `shapes`, `wsChan_recv`, `wsRecv_ok`, `mvccW_alloc`,
`mvccBackendFor_open`), with 4.2/4.3 inside `wsRecv_ok`'s and the watchable store's proofs.
