# mvcc's API: the invariants (informal; 2026-11-03, branch `mvcc-api`)

The user's plan: specs frozen, then the invariants informally, frozen, then the proofs (the
functions' and the laws', in parallel). The specs: `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`
and `ApiState.lean` (frozen 2026-11-03, `notes/mvcc-api-candidate.md`, "The freeze"). This note
says what each opaque predicate of the API is over `lean`'s internals, where each atomic update
fires, and what the internals must gain. It is over `lean`'s mvcc (the survey of 2026-11-03), not
round 9's old internals (`notes/mvcc-api-proof-plan.md`, whose abstract mode `lean` does not have).

**Status: round 2**, after an independent review of round 1 (`~/mvcc-api-candidates/review-invariants.md`:
W1-W4 wrong, M1-M7 missing, U1-U3 unclear, P1-P2), every finding repaired inside the
implementation: **the frozen spec does not change** (W3's option of a `Restore` receipt premise not
taken: a relative revision budget instead).

Paths are under `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/`.

## 0. Namespaces (W2)

The API's updates run at `⊤ \ ↑mvccN`, `mvccN = nroot .@ "mvcc"`. Every invariant of mvcc moves
under it: `writerN`, `poolN`, `regN`, `mwN`, `crevFrozenN`, `watchN`, `watchTokN`, the channel's
and the stream's (today `"mvcc_writer"`, `"mvccwatch"`, `"mvcc.watchTok"`, ... outside it) become
`mvccN .@ "writer"`, `mvccN .@ "watch"`, `mvccN .@ "watchTok"`, ... A mechanical change across the
proofs that name them; the first step of stage 1.

## 1. New ghost state

| Name | Type | Shares |
|---|---|---|
| `γ.abs` | ghost variable `Log × Int` (`σ.log`, `σ.crev`) | ½ the client, ¼ `revMuBody`, ¼ the writer's state (`writerL`, or the open write transaction) |
| `γ.pnd` | ghost variable `Option (List Change)` (`σ.pending`) | watched: ½ the client, ¼ the writer's state, ¼ `watchStoreBody` (beside `γ.rel`); a plain store: ½ the client, ½ the writer's state (P1; sound because a plain store's two steps fire in one atomic step at the bump, U3) |
| `γ.crevLb` | monotone natural lower bound of `σ.crev + 1` | authority: in `mvccState` (½) and with the compaction right (½), raised at `Compact`'s and `Restore`'s updates; fragments persistent (M2) |
| `ι.sst` | ghost variable `StreamState` | ¾ the client, ¼ the stream's mutex invariant (W1: `wsState` exclusive, two copies exceed 1) |
| `ι.reg` | ghost map `id ↦ (watcher, range, filter predicates, first revision, stamp k)`, monotone | authority ½ in `wsState`, ½ in the stream's mutex invariant; elements persistent, minted at the registration (M1) |
| `ι.dead` | ghost set of cancelled ids, monotone | as `ι.reg`; an element minted at `Cancel`'s first check and at `Close` (M1) |
| `ι.rcv` | the consumer's view: `watchConsumer`'s `γc.recv`, re-split ⅔ the consumer (`wsRecv`), ⅓ the channel invariant (W1) | |

Allocated by `NewStore`, `newWatchableStore`, `NewWatchStream`: in every store, no mode.

## 2. The predicates

- **`mvccState γ σ`**: `ghostVar γ.abs ½ (σ.log, σ.crev) ∗ ghostVar γ.pnd ½ σ.pending` ∗ the
  certificate map's authority `ghostMapAuth γ.cok 1 M` with `certMapOk M σ.notifiedLog` (every entry
  a prefix of the notified log, key 0 excluded so that `certOk`'s `certFree` disjunct contradicts
  it, M7; the `length ≤ 2` disjunct: such a log is `[[], []]`'s prefix, comparable with every log) ∗
  the authority half of `γ.crevLb` ∗, watched, the sole writer's half of `γ.wlog` (the notified log's
  authority, today `watchWriter`'s, M2/M4) ∗ the relative revision budget (§4.3: the restore base
  `b` with `σ.log.length = b + n`, `⧖ n`, `b + receiptBound + 3 ≤ 2 ^ 63`) ∗
  `⌜MvccReachable σ⌝`. Exclusive by the map's full authority (W1: say so).
- **`isMvcc kv γ`**: `kv` is `mkOk (Ptr store) s` with `isStore s γ.st`, or `mkOk (Ptr watchableStore)
  ws` with `isWatchableStore ws s γ`; the readers' pool (a `ThreadPool` of `storeReaderC`, with
  `watchReader`'s slot when watched); the write-back supply (`□ (⧗ 1 ={⊤}=∗ wbTok)`, ungated); the
  watch tokens' pool (`watchTokPool`); and the store's own goroutines (the sync loops, the
  compaction's job) draw readers from the same pool, with their thread tokens: no retired readers
  under the API, so `threadBound ≤ rdStockN` suffices (U2).
- **`mvccOpen γ`**: the closer (`storeCloser`, `wsCloser`), the compaction right (`compactRightR`)
  with the other half of `γ.crevLb`, the restore's pieces (`fieldShare ¼`, `wsDep`,
  `writerOwn`/`retiredAt`).
- **`mvccBackend γ q B Pk`**: a fraction `q` of the writer's fragment (`writerFrag`/`curAt`) at the
  store's physical names (`γ.withPhys p`, `p.bucket = B.γB`, `B.b`, `B.P`) and the batch lock's
  invariant `Pk`.
- **`mvccTxn t γ trace k`**: `.read σ`: today's read transaction at `σ.log`, `σ.crev`, with the
  pool's loan. `.write σ pend`: today's write transaction (`isTxnWrite σ.log pend`), the store's or
  the watchable wrapper over one, holding the writer's state: `γ.abs ¼` at `(σ.log, σ.crev)`,
  `γ.pnd` (¼ or ½) at `none` (then the notification's `some pend` inside the watchable `End`),
  `writerPin` (M4), the pool's loan.
- **`isMvccWatchStream ws γ ι`**: today's stream at `storeWatchParams`, its registration callback a
  fancy update given the store's shares at `σ` and the recorded registration index `k`
  (`chanRegAt k`, not the current send count: `moveVictims` sends without `s.mu`) (M6); the filters
  recorded with their predicates (`watch` takes `fs`, a `WatcherNames` field; `P.F`/`IWF` carry it,
  not `∃ p, filterSpec f p`: a diverging filter satisfies every `p`) (M3); the stream's mutex
  invariant extended with `ι.sst ¼`, `ι.reg ½`, `ι.dead ½`, agreeing with `closed`, `idsInv`.
- **`wsState ι S`**: `ghostVar ι.sst ¾ S ∗ ghostMapAuth ι.reg ½ R ∗ ghostSetAuth ι.dead ½ D`, with
  `S.ws` determined by `R` and `D` (live iff not in `D`, `closed` from `ι.sst`).
- **`wsRecv ι rs`**: the consumer's ⅔ of `recv` at the received `RespM`s `ms`, `rs = ms.map respView`,
  and for each received response **pure facts and persistent ghost elements only** (W4: no
  `filtersImpl` triples, no `rsnFor`/`progFact`, no fancy updates): the watcher's `ι.reg` element
  (its range, predicates, first revision, stamp), the events of the watcher received so far as
  `filtered fs (watchEvents L rg lo hi)` for a `γ.wlog` lower bound `L` (`notifiedLb`, recorded with
  every response: events or not, M2), the ids the response covers (a `-1` response: the live ids
  registered at a stamp at most its index, resolved from `regsAt` at the receive, which spends the
  receive's later credit), `ι.dead` elements, a compaction response's `γ.crevLb` fragment. The
  receive law (`wsChan_recv`) converts the channel invariant's facts into these.

## 3. Where each update fires

| Update | Fires at (on `lean`) | Gathers |
|---|---|---|
| a read (`Read`, `Rev`, `FirstRev`, the store's `Range`) | `store.Read` under `s.revMu` shared (`store__Read.lean:70-122`) | `revMuBody`'s share of `γ.abs`: agreement |
| `Write`'s begin | after `writerInv_checkout` (`store__Write.lean:127`), mask `⊤` | the writer's `γ.abs`, `γ.pnd` (at `none`): agreement |
| `End`, `pend = []` | both updates by agreement before the check-in (the watchable `End` takes no lock then) | the transaction's shares |
| `End`'s notification (watchable) | `γ.rel` raised (`watchableStoreTxnWrite__End.lean:508`), before any event of the revision is sent | `γ.pnd`: the client's, the transaction's, `watchStoreBody`'s; the next log's certificate minted into `γ.cok` (M4); the client's `γ.wlog` half advanced with the lock's |
| `End`'s bump | `currentRev++` with the ghost commit (`storeTxnWrite__End.lean:141-160`), under `s.revMu` | `γ.abs`: the client's, `revMuBody`'s, the transaction's; `γ.pnd` back to `none`; the budget's `⧖` |
| a plain store's `End` | both at the bump, one atomic step | as the bump; the certificate minted there |
| `Compact` | `compactMainRev` written (`store__updateCompactRev.lean:220`), under `s.mu`, `s.revMu` exclusively, with `writerInv` open (under `mvccN`, §0) | `γ.abs`: the client's, `revMuBody`'s, the writer's; `γ.pnd` (`none`); `γ.crevLb` raised |
| `Compact`'s `ErrCompacted`, `ErrFutureRev` | at the checks under `s.revMu` (U1) | agreement |
| `Restore` | between `restore_takeover` and `restore_switch` (`store__Restore.lean:154-398`) | `γ.abs` whole, `γ.pnd`, `γ.crevLb` raised; the budget re-based at `σ'.log.length` |
| the store's own `Put`/`DeleteRange` | one transaction: `Write`'s begin, then `End`'s two steps; the lessor's map `I` learnt by peeking the update, pinned by the transaction's ¼ (U1) | as those |
| `Watch`'s registration | inside `watchableStore.watch` after the current revision's read (`watchableStore__watch.lean:716`), the update fired after closing `watchN` (M6); the stream holds its mutex | the store's shares (agreement; `pending = none`), `ι.sst`, `ι.reg` (insert, element minted) |
| `Watch` on a closed stream | the `closed` check (`watchStream__Watch.lean:77`) | `ι.sst`: agreement |
| `Cancel` | its first check of the maps (`watchStream__Cancel.lean:38-43`) | `ι.sst`, `ι.dead` (element minted; the stream's cancel reason `Ψ` becomes it, replacing v3rpc's) |
| a stream's `Close` | `closed` written (`watchStream__Close.lean:~99`) | `ι.sst`, `ι.dead` (all) |

## 4. What the internals must gain

1. **The namespaces under `mvccN`** (§0).
2. **The ghost state of §1**, in `revMuBody`, `writerL` (with `writerPin`, `γ.wlog`'s writer half,
   M4), the open transactions, `watchStoreBody`, `watchStreamInv`, the channel invariant; allocated
   in `NewStore`, `newWatchableStore`, `NewWatchStream`; carried through every proof that opens and
   closes those (`storeTxnWrite.End`, `store.Read`, `updateCompactRev`, `watch`, `syncWatchers`,
   `moveVictims`, `RestoreMoves`, `NewStore`, the fractional instances).
3. **The relative revision budget** (W3): `idxCert`'s `⧖ (logCh log)` bounds a log by this process's
   receipts, which a restored history did not earn; the budget becomes relative to the last
   restore's base `b` (`⧖ (logCh log - b)` and `b + receiptBound + 3 ≤ 2 ^ 63`, the latter
   `Restore`'s frozen premise), changing `idxSealed`/`idxCert` and their users; `mvccState` carries
   the budget, not `idxCert`.
4. **The watch guarantee per watcher under compaction**: the global premise per registration
   (`watchNoDup = noCompactor ∨ noDupKeys`, `InvWatchStore.lean:544`) becomes per watcher: the
   watcher's delivery invariant "exact while `onceUpTo L lo crev`" (one implication: a catch-up read
   after a compaction at `c` returns revision `c`'s last change per key, all of it under the
   condition; the transfer of a fact recorded at `c₀` uses `γ.crevLb`: `c₀ ≤ σ.crev`).
5. **A compaction response's revision at most the compaction revision** (`respOk` does not record
   it today, `:484-486`): a `γ.crevLb` fragment at the send under `s.revMu`.
6. **`Compact`'s `ErrFutureRev` arm** (`lean` excludes it by premise).
7. **Pools**: the readers' `ThreadPool` (with the store's goroutines, U2), the write-back supply
   ungated (`kbWTSupplyM_of_stock` gives the gated one only).
8. **A store without a hook**: `bt_lockIn` over `plHookRO γ nil` from `LockInsideApply`'s `nil` arm,
   `bkHookIs`'s `≠ nil` dropped.
9. **The backend law** over `newPostKP`, the boot path rewired (`newPostK_pool` at `K := bFresh`).
10. **Internal specs over both store kinds** (M5): `store.Write`, `storeTxnWrite.End` (the
    client's second update only, the first already fired by the watchable `End`), `store.Restore`,
    with the store's shares lent: internal lemmas (variants), the API's contracts at the concrete
    types their corollaries.

## 5. The proofs, after the freeze of this note

Stage 1, sequential (everything else needs it): §4.1, §4.2, §4.3, the predicates' definitions
(sealed, `ApiImpl.lean`), §4.7, §4.9, §4.10's statements. Stage 2, in parallel, a file each: the
contracts' proofs per (type, method) (the store's thirteen for both store types; the transactions'
seven for each of the three types; the stream's seven), the constructors' (`New`, `NewStore`,
`NewReadOnlyTxnWrite`), §4.4-§4.6 and §4.8 inside them, and the laws (`persistent`, `excl`,
`mvccBackend_agree`, `mvccState_reachable`, `shapes`, `wsChan_recv`, `wsRecv_ok`, `mvccW_alloc`,
`mvccBackendFor_open`).

## Clients (from the review)

The tester's proof needs §4.5 and the notified-log bound of every response (M2) though it never
compacts (it checks `CompactRevision == 0` and progress revisions below its history). etcd keeps
`mvccState` in its own invariant (fine at the mask once §0 is done) and loses `γ.cok` as its raft
link: its proof's link moves to `mvccState`'s `σ.log`.
