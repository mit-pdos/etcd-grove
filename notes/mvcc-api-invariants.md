# mvcc's API: the invariants (informal; 2026-11-03, branch `mvcc-api`)

The user's plan: specs frozen, then the invariants informally, frozen, then the proofs (the
functions' and the laws', in parallel). The specs: `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`
and `ApiState.lean` (frozen 2026-11-03, `notes/mvcc-api-candidate.md`, "The freeze"). This note
says what each opaque predicate of the API is over `lean`'s internals, where each atomic update
fires, and what the internals must gain. It is over `lean`'s mvcc (the survey of 2026-11-03), not
round 9's old internals (`notes/mvcc-api-proof-plan.md`, whose abstract mode `lean` does not have).

**Status: frozen (2026-11-03, round 3).** Round 1 reviewed (`~/mvcc-api-candidates/review-invariants.md`:
W1-W4 wrong, M1-M7 missing, U1-U3 unclear, P1-P2), every finding repaired inside the implementation
(**the frozen spec does not change**: W3's option of a `Restore` receipt premise not taken, a
relative revision budget instead); round 2 reviewed (`review-invariants-2.md`: the repairs' defects
D1-D6 and two missing items), its repairs applied as the review gave them. Frozen by the agent (the
user delegated it): every finding of both reviews repaired, and the second review found
`wsRecv_ok` a pure entailment for every conjunct with those repairs.

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
| `γ.crevLb` | monotone natural lower bound of `σ.crev + 1` | authority: ½ in `mvccState`, ¼ with the compaction right, ¼ in `revMuBody` (scaled by its fraction, so that `syncWatchers` under `s.revMu` mints fragments, D2); raised at `Compact`'s and `Restore`'s updates, which hold all; fragments persistent (M2) |
| `ι.sst` | ghost variable `StreamState` | ¾ the client, ¼ the stream's mutex invariant (W1: `wsState` exclusive, two copies exceed 1) |
| `ι.reg` | ghost map `id ↦ (watcher, range, filter predicates, first revision, stamp k)`, monotone | authority ½ in `wsState`, ½ in the stream's mutex invariant; elements persistent, minted at the registration (M1) |
| `ι.dead` | ghost set of cancelled ids, monotone | as `ι.reg`; an element minted at `Cancel`'s first check only (`Close` marks none: its update leaves `live` unchanged, and no `-1` response is sent after it, D3) (M1) |
| `ι.rcv` | the consumer's view: `watchConsumer`'s `γc.recv`, re-split ⅔ the consumer (`wsRecv`), ⅓ the channel invariant (W1) | |

Allocated by `NewStore`, `newWatchableStore`, `NewWatchStream`: in every store, no mode.

**Superseded in part (2026-11-03, stage 1):** `ι.sst` and `ι.reg` cannot hold a `StreamState` or a
`WInfo` as written: a watcher's filters (`fs : List (EvM → Bool)`) are functions, and Perennial's
ghost values are of small countable types only (`ghostVar` needs `Pos.Countable`). Saved
propositions would hold them, but agree only under a later, which `wsRecv_ok.law`'s plain
entailment cannot strip. So `ι.sst` and `ι.reg` hold the countable part (ids, ranges, `lo`, `k`,
`live`, `closed`), each watcher with the ghost name of its **saved filters** (`savedFilters γf fs`,
`Proof/.../mvcc/ApiGhost.lean`: the filters' code `fsCode fs : Pos → DiscreteO (Option Bool)`, a
discrete function, so its agreement is pure equality, `savedFilters_agree`, and the code is
injective, `fsCode_inj`); `wsState ι S` relates `S`'s `fs` to the saved filters of `ι.sst`'s names.
The frozen API is unchanged.

**Open (2026-11-03, stage 1): the carry-through and today's specs.** §4.2 has the new ghost state
carried through today's proofs, and stage 1 was to keep today's statements. The two do not fit for
the steps that change the state (`storeTxnWrite.End`, `store.updateCompactRev`, `store.Restore`,
`watchableStore.watch`, `NewStore`): each must update `γ.abs`/`γ.pnd`/`ι.reg` with the client's half,
which today's specs do not give their callers. Either (a) today's specs keep a holder of the
client's halves inside `isStore`/`isWatchableStore` (a legacy mode, thrown away at the migration);
(b) the internal specs change to the API's shapes together with their clients (M1 as one change:
the internals' statements and every client at once); or (c) the new internal lemmas are written
beside today's proofs (§4.10's variants), with today's specs as their corollaries where they can
be (a corollary needs (a)'s holder). (b) is what M1 says; it makes stage 1's ghost carry-through
part of stage 2 and of the migration. **Decided 2026-11-03 (the coordinator): (c) without the
holder**: parallel modules (`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/Api/`), copies of only
what changes (the invariants `revMuBody`, `writerL`/`writerInv`, `watchStoreBody`, the stream's
mutex invariant, and the proofs whose statements change: `storeTxnWrite.End`,
`store.updateCompactRev`, `store.Restore`, `watchableStore.watch`, `NewStore`), carrying §1's ghost
state, the share token and the frozen writer state; unchanged modules reused by import; today's
specs and proofs untouched and green until the M1 switch deletes them and moves every client at
once. *Superseded 2026-11-04 (the coordinator; `notes/decisions.md`, "the slots in place"):
today's definitions carry the slots in place, keyed on `StoreNames.api` (trivial at `none`, which
`isStore` asserts; the API's at `some a`); no parallel tree.*

## 2. The predicates

- **`mvccState γ σ`**: `ghostVar γ.abs ½ (σ.log, σ.crev) ∗ ghostVar γ.pnd ½ σ.pending` ∗ the
  certificate map's authority `ghostMapAuth γ.cok 1 M` with `certMapOk M σ.notifiedLog` (every entry
  a prefix of the notified log, key 0 excluded so that `certOk`'s `certFree` disjunct contradicts
  it, M7; the `length ≤ 2` disjunct: such a log is `[[], []]`'s prefix, comparable with every log) ∗
  the authority half of `γ.crevLb` ∗, watched, a share of `γ.rel` (the released length, bumped at the
  notification, `watchableStoreTxnWrite__End.lean:508`: the notified log's bound, D1) and the sole
  writer's half of `γ.wlog` (the committed-and-notified log, today `watchWriter`'s, M2/M4) ∗ `idxCert γ.idx σ.log` (today's, with the receipt
  `⧖ (logCh σ.log)` of the whole history: round 15, the user's (D), `Restore` taking the restored
  history's receipt, so no relative budget) ∗
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
  invariant `Pk`, **and a fraction `q` of a share token of total 1** (round 16, the review's F2: the
  writer's fragment alone excludes nothing, being one of several `dghostVar` parts), with
  `isBackend B.γB B.P (mvccW gx) Pk B.b`. Every step that changes the history (`End`, `Put`,
  `DeleteRange`, `Compact`, `Restore`, the lease delete) holds its share across the step.
- **The frozen writer state** (F2, for `mvccImage_snapshot.law`): `writerInvBody` gains a state that
  the whole share's holder enters and leaves: it deposits the whole token, and takes a half of a
  ghost value at `(σ.log, σ.crev)` paired with `W`'s half of `γ.wv` (and a `crevUB` at `σ.crev` for
  the deletable keys' `crevLb`), so that every commit inside the call finds `W`'s log `σ.log`; a
  writer that finds the frozen state contradicts its own share. A write transaction left open: the
  holder takes the deposited `writerKey`, so every commit's `W` contradicts it (the observation is
  vacuous; that transaction cannot `End` without a share). The snapshot's no-compaction case
  (`σ.crev = -1`, the law's premise) gives `fkOwn γ 0`, hence no compaction key (`fkRd_abs`).
- **`mvccImage D L c u`**: the image facts (`keyImage L D` when `c = -1`, else the restore image:
  `Api.lean`'s docstring) ∗ `⧖ (logCh L)`. **`mvccBackendFor B Pk L c u`**: the opened backend's
  store part (`mvccBackendFor_open`'s post), with the image's receipt kept for `Restore`'s
  `idxCert`. `isMvcc` records `receiptBound ≤ 2 ^ 48` (`New`'s premise), from which `Restore`
  derives the length bound it no longer takes (a committed revision is never empty, `commitLog`;
  `preceipt_lt`).
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
  (its range, predicates, first revision, stamp, with its `chanRegAt`; deposited into the channel
  invariant before `s.mu` is released at the registration, so the receive can hand it out), the
  events of the watcher received so far, **as an implication**: `onceUpTo L lo c₀ →` they are
  `filtered fs (watchEvents L rg lo hi)`, with a `γ.crevLb c₀` fragment (exactness fails when a
  compaction lost an event); a lower bound on the notified log with every response (events or not,
  M2): a `γ.rel` lower bound for the notification's responses (D1), `notifiedLb` at `syncWatchers`
  and progress, and for `moveVictims` (which sends without `s.mu`) the bound recorded when the victim
  batch was made and carried to the send; the coverage of a progress response: every watcher
  registered at a stamp at most its index is covered **or has an `ι.dead` element** (D4: the receive
  runs inside the channel invariant, with no access to `ι.reg`/`ι.dead` behind `ws.mu`; `regsAt`
  resolved from `sentAuth` inside the opening the receive already makes: no credit, D5); a compaction
  response's `γ.crevLb` fragment. The receive law (`wsChan_recv`) converts the channel invariant's
  facts into these.

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
| `Restore` | between `restore_takeover` and `restore_switch` (`store__Restore.lean:154-398`) | `γ.abs` whole, `γ.pnd`, `γ.crevLb` raised; the receipt `⧖ (logCh σ'.log)`, from `mvccBackendFor`, into `idxCert` and to the update (round 16) |
| the store's own `Put`/`DeleteRange` | one transaction: `Write`'s begin, then `End`'s two steps; the lessor's map `I` learnt by peeking the update, pinned by the transaction's ¼ (U1) | as those |
| `Watch`'s registration | inside `watchableStore.watch` after the current revision's read (`watchableStore__watch.lean:716`), the update fired after closing `watchN` (M6); the stream holds its mutex | the store's shares (agreement; `pending = none`), `ι.sst`, `ι.reg` (insert, element minted) |
| `Watch` on a closed stream | the `closed` check (`watchStream__Watch.lean:77`) | `ι.sst`: agreement |
| `Cancel` | its first check of the maps (`watchStream__Cancel.lean:38-43`) | `ι.sst`, `ι.dead` (element minted, and deposited in `respCompl` directly: not through the saved reason `rsnFor`, which would cost a second later credit at the receive, D5) |
| a stream's `Close` | `closed` written (`watchStream__Close.lean:~99`) | `ι.sst` (`closed`; `ι.dead` unchanged, D3) |

## 4. What the internals must gain

1. **The namespaces under `mvccN`** (§0).
2. **The ghost state of §1**, in `revMuBody`, `writerL` (with `writerPin`, `γ.wlog`'s writer half,
   M4), the open transactions, `watchStoreBody`, `watchStreamInv`, the channel invariant; allocated
   in `NewStore`, `newWatchableStore`, `NewWatchStream`; carried through every proof that opens and
   closes those (`storeTxnWrite.End`, `store.Read`, `updateCompactRev`, `watch`, `syncWatchers`,
   `moveVictims`, `RestoreMoves`, `NewStore`, the fractional instances).
3. **No relative revision budget** (superseded, round 15, the user's (D)): `Restore` takes the
   restored history's receipt `⧖ (logCh σ'.log)` (the server's snapshot image certificate carries
   it, `etcdserver/InvImage.lean:148`), so `idxCert` keeps today's whole-history receipt and its users
   are unchanged. The `Range` contracts' `stateOk` (every readable state at most `2 ^ 62` entries,
   non-negative revisions and version) is proved from it: a state's entries, a key's version and a
   revision number are each at most the history's changes, fewer than `receiptBound ≤ 2 ^ 48`; a write
   transaction's pending state from the writer's `⧖ (logCh ilog + pend.length)` (today's
   `idxWriter`). Round 16: the receipt reaches `Restore` inside `mvccBackendFor`, from the image
   `mvccImage` (`mvccBackendFor_open`), so `mvccImage` is defined on adoption as the image facts
   ∗ `⧖ (logCh L)`, and `mvccBackendFor` keeps the receipt for `Restore`'s `idxCert`; the
   positivity in `kvSortOk` and `wsRecvOk` is from the same receipt (`logCh` bounds every revision
   and version below `receiptBound`, so none wraps).
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
`mvccBackendFor_open`, `mvccImage_fresh`, `mvccImage_snapshot`, `reach_logWf` (pure: better a theorem
in `ApiState`), `mvccTxn_leaseDelete`, `wsSentLb_zero`, `names_nonempty`).

**From the probes** (2026-11-04): export `persistent.law`'s facts as `instance`s once `ApiImpl.lean`
defines the predicates (clients otherwise re-declare them); `wsChanNames ι` defined as the stream's
channel's names; M1's obligations (`WsRecvOkProbe.lean`'s header): a registration's stamp the exact
sent count (the channel invariant opened at the registration), a `-1` send seeing every
registration made by then, `Restore`'s `pending = none` from the writer's state, the filters'
agreement by plain equality (`savedFilters`).

**Round 16's obligations** (the review, `~/mvcc-api-candidates/review-r16.md`):
- The receipts at the notify step (`Txn.End`, `Put`, `DeleteRange`, the lease delete): from the open
  transaction's writer state, `⧖ (logCh ilog + pend.length)`; at `Restore`'s step, from
  `mvccBackendFor`.
- `wsRecvOk`'s event positivity is recorded per received response, unconditionally (not under the
  `onceUpTo →` implication: a lossy compaction's events are still positive): at the send, the
  index's version facts; for a delete, `watchableStoreTxnWrite.End`'s `ModRevision = rev` and
  `kvsToEvents`' tombstones.
- The vocabulary exports two rewrites the clients keeping `⧖ (logCh σ.notifiedLog)` need:
  `(σ.notify p).notifiedLog = σ.log ++ [p]` (`σ.pending = none`), and `logCh (L ++ [[]]) = logCh L`.
- Not done (F4, kept as today; dropping it later is a strengthening no client breaks on):
  `keySized`'s premise of `mvccBackendFor_open`, derivable from the receipts.

## Clients (from the review; the size facts superseded by round 15)

The tester's proof needs §4.5 and the notified-log bound of every response (M2) though it never
compacts (it checks `CompactRevision == 0` and progress revisions below its history). etcd keeps
`mvccState` in its own invariant (fine at the mask once §0 is done) and loses `γ.cok` as its raft
link: its proof's link moves to `mvccState`'s `σ.log`. (The second review's obligation for etcd, its
sort premise `sortSmall` after a compacted restore, is gone: round 15 states what the sort needs,
`stateOk`, at the `Range` contracts, from the whole-history receipt.)

## The migration (the user, 2026-11-03)

**M1: all at once.** The internals change, today's specs are replaced by the API's, and every
client of today's mvcc specs (etcd's `txn`, `apply`, `lease`, the server, `v3rpc`, client/v3's watch
proofs, the examples) moves onto the API in the same stage (not today's specs kept as temporary
corollaries over a legacy invariant, M2; not a mode flag, M3). **First** (the user): an informal
assessment that etcd's proofs can work over the new specs (three, by client group:
`~/mvcc-api-candidates/assess-{txn,server,watch}.md`); if it holds, the mvcc proofs, then the proofs
on top of them.

**The order (the user, 2026-11-03): every spec and invariant first, then the proofs.** To keep the
proofs from backtracking (a stronger spec found needed halfway, the proof redone), all the new specs
and invariants are designed and checked against each other before any proof: the mvcc API (frozen)
and its invariants (frozen, this note); then each client package's specs restated over the API
(`txn`, `apply`, `lease`, the server, `v3rpc`, client/v3's watch proofs, the examples' closed
theorems) and their invariants (the server's holding `mvccState`, `v3rpc`'s sharing `wsState`), each
reviewed; a gap found there that needs a stronger mvcc spec reopens the API before the proof, not
during it. Then the proofs, mvcc first.

## Hand-off: the parallel internals' invariants (2026-11-03, stage 1)

*Superseded 2026-11-04 by the next section: `Api/InvStoreX.lean` and `InvWatchX.lean` are retired;
the per-proof ghost updates below still describe what each slot step does.*

**Built** (`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/Api/`, no `sorry`, no axiom; today's
modules untouched):
- `Ghost.lean`: `AbsNames` (`abs`, `pnd`, `crevLb`, `tok`, and `frz`, the writer's frozen flag);
  `absPart`/`pndPart` (agree, update with two shares making 1), `crevAuth`/`crevAtLeast`,
  `shareTok` (`shareTok_excl`), `absNames_alloc` (all of them at a new store, the flag down).
- `InvStoreX.lean`: today's bodies with a **slot**, every lemma over them restated for any slot
  (today's proofs, carrying it): `revMuBodyLX`/`revMuBodyX` (slot `X q log c`),
  `revMuBodyLX_fractional`, `_of`, `_noLag`, `_mu`, `_wsd`; `revMuCurX`, `revMuInvX` (restoring:
  the counters only, the slot's part the restorer's), `_fractional`, `revMuInvX_open`, `_open_pin`,
  `_open_cur`, `_closeL`, `_close`, `_open_held`, `_open_share`; `writerLX` (slot `Y ilog`);
  `writerInvBodyX s γ Y F Fr fz` (in/out with the flag whole and down; **frozen**: the flag half up
  and `F` deposited; restoring: with `Fr` deposited and the flag down), `writerInvX_checkout`/
  `_checkin` (the writer holds `G`, `F ∗ G ⊢ False`), `writerInvX_freeze`/`_thaw` (the freezer
  takes `writerTaken`: the state, or the open writer's key); `isStoreX` and `_withPhys`. **The
  API's instance**: `revMuAbs a q L c` (¼q of the view and of the compaction authority),
  `writerAbs a pw L` (¼ of the view, `pw` of the pending revision at `none`; `pndW γ`: ¼ watched,
  ½ plain), `isStoreA s γ a` (`F = Fr = shareTok a 1`, flag `a.frz`), `revMuInvA_fractional`.
- `InvWatchX.lean`: `watchStoreInvX s γ Z q` (slot `Z q σ`), `_fractional` (with today's
  `ownIvt_split` hypothesis), `isWatchableStoreX`, `revMuInvX_open_ws`; **the API's instance**
  `wsAbs a q σ` (¼q of the pending revision, agreeing with `σ.Lmu`'s last revision: `pndOk`),
  `isWatchableStoreA`; `watchStreamInvX`/`isWatchStreamX` (slot `Z nextID closed WM`); the stream's
  countable ghost (`StreamAbsNames`: `sst`, `reg`, `dead`; `WInfoC`, `RegC`, `wrC`; `winfoIs`, a
  watcher's info against its countable part and saved filters) and the first-cut instance
  `streamAbs` (¼ of `ι.sst` at the mutex's closed flag, ½ of the registry's and the cancelled
  set's authorities), `isWatchStreamA`.

**Scope, corrected.** Not only the five proofs whose statements change: a lock's invariant is
fixed at its creation, so **every proof that opens `s.revMu`, the writer's invariant, the watchable
store's `s.mu` or a stream's `ws.mu`** is redone over the slotted invariants (today's proofs over
`isStore`/`isWatchableStore` do not apply to `isStoreA`/`isWatchableStoreA`). Those that open them
(today's files): `store__Read`, `store__Write`, `storeTxnWrite__End`, `metricsTxnWrite__End`,
`store__updateCompactRev`, `store__Restore`, `RestoreMoves`, `RestoreOn`, `NewStore`, `ReaderSpecs`,
`InvCompact` (lemmas), `InvWatchStore` (lemmas), `watchableStore__watch`, `__syncWatchers`,
`__moveVictims`, and those of `watchStoreInv` (`watchableStoreTxnWrite__End`, `__cancelWatcher`,
`__progressIfSync`, `__syncWatchersLoop`, `__syncVictimsLoop`, `__Restore`, `newWatchableStore`,
`NewWatchableLemmas`) and of `watchStreamInv` (the stream's methods). The other 45-odd files that
only take `isStore`/`isWatchableStore` as a premise port by renaming (`isStoreX` has `isStore`'s
named conjuncts). Most proofs carry the slot untouched: they can be proved for **any slot**
(generic `X Y F Fr fz Z`), as the lemmas here are, and only the steps below need the instance.

**Per proof: the new invariants, lemmas and ghost updates** (§3's table):
- **`storeTxnWrite.End`** (and the plain store's `End`): `writerInvX_checkin` with `G :=
  shareTok a q` (its backend share); at the bump under `s.revMu` (`revMuInvX_open_held`, the
  body `revMuBodyX` at `log`): `absPart_update` with the lock's ¼ (`revMuAbs`), the writer's ¼
  (`writerAbs`, in the transaction's hands) and the client's ½ (the update's), to `(log ++ [pend],
  c)`; `pndPart_update` back to `none` (the client's ½, the writer's `pndW`, a watched store's
  `wsAbs` ¼ under `s.mu`); the notify step (watchable `End`, `watchStoreInvX` at `σ.Lmu`):
  `pndPart_update` to `some pend` with `pndOk` from the notified log; the receipt from the writer's
  `⧖ (logCh ilog + pend.length)`.
- **`store.updateCompactRev`** (`Compact`): under `s.mu`, `s.revMu` exclusive, `writerInvX` open (the
  writer's state in: the flag down; frozen excluded by its share): `absPart_update` (lock ¼, writer
  ¼, client ½) to `(log, c')`; `crevAuth_update` with the lock's ¼, the compaction right's ¼ and the
  client's ½ (`crevAtLeast` minted).
- **`store.Restore` / `RestoreMoves`** (`restore_takeover`, `restore_switch`, `restore_finish`): the
  takeover moves the writer's invariant to its restoring state, depositing `Fr := shareTok a 1`
  (the restorer's whole share; a frozen state is excluded by it) with the flag down, and takes
  `writerAbs`'s and `revMuAbs`'s parts out (`revMuInvX` restoring holds the counters only); at the
  switch, `absPart_update` whole to `(σ'.log, σ'.crev)`, `crevAuth_update`, the pending revision at
  `none`; the finish returns `Fr`.
- **`watchableStore.watch`**: under `s.mu` (`watchStoreInvX`) and `ws.mu` (`watchStreamInvX`):
  agreement of the client's view with `revMuAbs` (the read revision), `pndOk`'s `none`; the
  registration: `ι.sst` updated (¾ client, ¼ `streamAbs`), a registry element minted
  (`ghostMapElem ι.reg id .discard e`, with `savedFilters_alloc`), the tie of `streamAbs` to `WM`
  strengthened as the proof needs (the first cut ties only `closed`).
- **`NewStore`** (and `newWatchableStore`, `NewWatchStream`): `absNames_alloc` at `mvccStart`
  (`absPart 1`, split ½ client, ¼ `revMuAbs`, ¼ `writerAbs`; `pndPart 1` split ½ client and
  `pndW`/`wsAbs`; `crevAuth 1` split ½ client, ¼ compaction right, ¼ `revMuAbs`; `shareTok 1` to the
  client's `mvccBackend`; `frz` whole in `writerInvBodyX`), the locks created at
  `revMuInvX`/`watchStoreInvX`/`watchStreamInvX` (`revMuInvA_fractional`,
  `watchStoreInvX_fractional` with `wsAbs_fractional`); the stream's `StreamAbsNames` allocated at
  `NewWatchStream`.
- **The snapshot law** (`mvccImage_snapshot.law`, stage 2): `writerInvX_freeze` with `F :=
  shareTok a 1` (`hFr`, `hFF`: `shareTok_excl`), the observation from `writerTaken`'s `writerLX`
  (its `γ.wv` half agrees with `W`'s; its `writerAbs` with the client's `σ`), `writerInvX_thaw`.

**Not done here**: `ι.rcv` (the consumer's view, re-split in the channel invariant, §1) and the
read-only proofs' ports.

## Hand-off: the slots in place (2026-11-04, stage 1)

(Superseded in part, 2026-11-04, the user: strict M1, `notes/decisions.md`, "strict M1, no
scaffold": no `none` case; the slots become the API's ghost state outright, `isStore`'s
`γ.api = none` and today's specs' corollaries go.)

**Done** (today's statements unchanged; `γ.api = none` from `isStore`):
- `InvStore`: `StoreNames.api`; `slotX`/`slotY`/`slotF`/`slotFr`/`slotFl` (`_withPhys`, `_none`,
  `slotX_change`, `slotY_change`, `slotX_fractional`); the slots in `revMuBody`, `revMuBodyL`
  (`"HX"`), `writerL` (`"HY"`), `writerInvBody` (frozen state, restorer's deposit, flag); `isStore`'s
  `"%Hapi"`; `writerInv_checkoutG`/`_checkinG` (a resource `G` with `slotF γ ∗ G ⊢ False`), today's
  `writerInv_checkout`/`_checkin` taking `γ.api = none`. `pndW` moved here; `revMuAbs`/`writerAbs`
  to `Api/Ghost.lean` (which now imports only `InvIndex`).
- The lock-openers carry the slot: `store.Read`, `store.Write`, `storeTxnWrite.End`,
  `store.updateCompactRev`, `NewStore`, `RestoreMoves` (`restore_takeover`/`_switch`/`_finish` take
  `γ.api = none`), `store.Restore`, `watchableStore.{watch, syncWatchers, moveVictims}`; the other
  mvcc proofs needed no change.
- `Api/Instance.lean`: `slot*_some`, `slotF_share_excl`, `writerTaken`, `writerInv_freeze`/`_thaw`.

**Left** (in order):
1. The watchable store's and the stream's slots (`watchStoreInv`'s `Z`, `watchStreamInv`'s), keyed
   the same way (on `γ.api` and on the stream's names); `ι.rcv`.
2. `isStoreA s γ a` (today's `isStore` body with `⌜γ.api = some a⌝`: generalize `isStore` to the
   `api` fact as a parameter, `isStore` its `none` instance), `isWatchableStoreA`, `isWatchStreamA`.
3. The generic versions of the slot-changing steps, with the slot step as a hypothesis: today's
   proofs use `γ.api = none` only at `slotX_change`/`slotY_change`/`slotF_none`/`slotFr_none`/
   `slotFl_none(_true)`; each such use is where the generic proof takes the step. Shapes:
   - End's bump: `slotX γ q L c ∗ slotY γ L ∗ Cl ={E}=∗ slotX γ q L' c ∗ slotY γ L' ∗ Cl'` (`Cl` the
     client's half, from the update);
   - Compact: `slotX γ q L c ∗ Cl ={E}=∗ slotX γ q L c' ∗ Cl'`;
   - Restore's switch: `slotX γ 1 L' c` from `slotFr γ`'s holder's parts and `Cl`;
   - checkout/checkin: `G := api.shareTok a q` (`slotF_share_excl`).
   Note: `store.Write` drops the writer's `HY` (affine; `End` rebuilds a trivial one at `none`):
   the API's transaction must carry it from `Write` to `End`.
4. `ApiImpl.lean`'s definitions, pools, the backend law, §4.10's statements.

