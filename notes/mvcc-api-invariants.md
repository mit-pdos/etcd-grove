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

## Hand-off: strict M1 (2026-11-04, stage 1)

**Done** (the mvcc library builds: `mvcc.Link`, `Results`, `Api`, `Api/Instance`, `Api/SentInv`;
beyond it the build is red, as strict M1 allows: e.g. `etcdserver/RestorePre.lean` unfolds
`watchStoreInv`):
- **No scaffold.** `StoreNames.api : api.AbsNames`; the slots (`slotX`, `slotY`, `slotF`, `slotFr`,
  `slotFl`) are the API's ghost state outright; `isStore` has no `api = none`; today's
  `writerInv_checkout`/`_checkin` wrappers gone (`…G` forms only). `NewStore` allocates the API's
  ghost state (`api.absNames_alloc_store`: the lock's and the writer's slots and the frozen flag
  kept, the client's parts dropped, today's spec returning none of them; `pndW_compl`).
- **The watchable store's slot**: `relAuth γ q Lmu` (the released length's authority and
  `wsSlot`, a quarter of `q` of the pending revision agreeing with the notified log, `pndOk`) in
  `watchStoreInv`; fractional (`InvWatchFrac`: `wsSlot_fractional`, `relAuth_fractional`);
  `relAuth_of_eq` restated; carried by every watchable-store proof.
- **The writer's slot carried from `Write` to `End`** (`storeTxnWriteIs`/`Core`'s `"HY"`).
- **`Api/SentInv.lean`**: probe M1's pure core (`SentInv`, `wsRecvOk_of_sent`, the steps), moved
  from `notes/mvcc-api-probes/WsRecvOkProbe.lean`.
- **Placeholders** (`sorry -- M1-REPLACE: <contract>`, 10): `M1Placeholders.lean`'s five lemmas,
  each false in general, used at 10 sites (`slotX_step_M1`: End's bump, `updateCompactRev` ×2;
  `slotY_step_M1`: End's bump; `slotF_excl_M1`: `Write`'s checkout, End's checkins ×2;
  `wsSlot_make_M1`: `newWatchableStore`; `wsSlot_step_M1`: the watchable End's notify, its
  `Restore`), and five local ones in `RestoreMoves` (the takeover's, switch's and finish's slot
  steps and frozen-state exclusions). Each goes when its proof is rewritten against the API's
  contract at stage 2; nothing new may use them.

**Left** (in order):
1. **The stream's slot** (§1's `ι.sst`, `ι.reg`, `ι.dead`, `ι.rcv`): `WsStreamNames.api :
   StreamAbsNames` and a conjunct of `watchStreamInv` (the retired first cut, `cc74c18040`'s
   `Api/InvWatchX.lean`: `StreamAbsNames`, `WInfoC`/`RegC`/`wrC`, `sstPart`, `winfoIs` over
   `savedFilters`, `streamAbs` tying only the closed flag). Its real ties are the watch chain's
   design (stage 2's M1, `notes/mvcc-api-risk.md`): the registry against the stream's id map
   (`idsInv`, `chanIdAssigned`) and each watcher's `watcherFixed`/`covFact`; the stamp the exact
   sent count, which today's channel invariant already records (`chanRegAt w n` with
   `n ≤ sent.length` minted at the registration, `regsOk`); `-1` responses covering the
   registrations so far (`respCompl`, `rsnW`: the cancelled set `ι.dead` is `rsnFor`'s ids); the
   channel invariant keeping `Api/SentInv.lean`'s `SentInv` of its sent list (`sentAuth`'s
   `respCov` facts are the per-response `SentFact.holds`); `ι.rcv` the consumer's `γc.recv`
   re-split (⅔ the client's `wsRecv`, ⅓ the channel invariant).
2. `ApiImpl.lean`'s sealed definitions of the opaque predicates (`mvccState` = the client's parts:
   `absPart ½`, `pndPart` its part, `crevAuth ½`, `crevAtLeast`; `mvccBackend γ q` = `shareTok q`
   with the writer's fragment, ...), `persistent.law`'s facts as instances, `wsChanNames ι`.
3. Pools and the backend law (§4.7, §4.9); §4.10's internal statements.

## Hand-off: stage 2, the watch chain (2026-11-05)

**Done** (no `sorry`, no axiom; the mvcc library builds, 389 modules; the API's interface unchanged):
- `Api/StreamLog.lean` (pure): a stream's history `SEv` (registrations, cancels, close, sends, each
  send with its fact: response, watcher's registry info with its filters by saved name, the
  notified-log and compaction lower bounds, a `-1` response's covered and cancelled ids), its
  `replay` (stream state, cancelled set, facts; a registration's stamp the number of sends before
  it, exactly), `LogWF` (each event's premises held when appended: `stepOk`), and
  `sentInv_of_log`/`wsRecvOk_of_log` (from `Api/SentInv.lean`'s step lemmas).
- `Api/Ghost.lean`: `AbsNames.nl`, the notified log's monotone authority, whole in `mvccState`
  (exclusive; the internals keep only lower bounds of it, minted at the notify update's commit,
  when the client's `mvccState` is in hand).
- `Api/StreamGhost.lean`: `WsAbs` (the stream's API names: `st` the store's, `ev` the history, `ns`
  the count of client events, `rcv`/`rx` the consumer's view and its exclusive count, `ch`/`chn`
  the channel), `logTok` (a well-formed lower bound of the history with its filters' saved names
  and the sends' lower bounds), `mvccStateI`, `wsStateI`, `wsRecvI`, `wsSentLbI`, their
  timelessness, persistence, exclusivity, and **`wsRecv_okI`: `wsRecv_ok.law`'s entailment as a
  plain entailment** (the two lower bounds comparable, `mono_list_lb_valid`; the receiver's extra
  events sends only, by the count's lower bound against the client's authority; filters by
  `savedFilters_agree`; the bounds against the client's authorities).
- `Api.lean`: `MvccName := StoreNames`, `WsName := api.WsAbs`, `mvccState`, `wsState`, `wsRecv`,
  `wsSentLb`, `wsChanOf`, `wsChanNames`, `isMvccWatchStream` sealed (`@[no_expose]`) over them
  (the internals imported non-publicly); `isMvccWatchStream` is the tie `ι.st = γ.api` and a
  private opaque placeholder for the stream's channel part (`isMvccWatchStreamRest`, M1-REPLACE).
- `Api/WatchLaws.lean`: `wsRecv_ok.law`, `wsSentLb_zero.law`, the watch conjuncts of
  `persistent.law` (instances) and `excl.law`. **No frozen statement found false**: the riskiest
  one (`wsRecv_ok.law`'s plain `⊢`, risk M1) holds over these definitions.

**Done since** (2026-11-05, `Api/StreamSteps.lean`, no `sorry`): the API part of the channel
invariant as a predicate, `chanApiAt ι l dec recv` (the history's authority at `l`, `LogWF dec l`,
the filters' saved names, the sends' bounds, the invariant's half of the consumer's view, a lower
bound of the client's count), and its steps, each what a frozen post needs: `chanApi_alloc`
(`NewWatchStream`: `wsState ι wsStart`, `wsRecv ι []`), `chanApiAt_send` (a send's event, its
`stepOk` the sender's obligation), `chanApiAt_reg` (`Watch`'s update: `wsState` at
`S.register id ⟨rg, fs, lo, k, true⟩` with `k` the exact sent count, and `wsSentLb ι k`),
`chanApiAt_cancel` (`wsState ι (S.cancel id)`), `chanApiAt_recv` (`wsRecv ι (rs ++ [r])`, the
receiver's lower bound minted), `chanApiAt_sentLb` (the empty receive's `n ≤ |sends|`). So every
frozen post of the stream's contracts is producible at the ghost level.

**Done since** (2026-11-05, the wiring; the mvcc library builds):
- `WatchModel.lean`: the watchers' log model (`evOfKv` .. `watchEvents_cmp`, the countable
  instances of `EtcdKv`, `EvM`, `WatchRange`) split out of `InvWatchStore`, so that `ApiState`
  (importing it in place of `WatchRecv`; statements unchanged) and `Api/SentInv` .. `Api/StreamSteps`
  come before the channel invariant, which `InvWatchStore` now builds over them.
- `WatchChanNames` gains the stream's API names (`aev`, `ans`, `arcv`, `arx`); `wsAbsOf γ ch γc`
  is the stream's `WsAbs` (`st := γ.st.api`, the channel and its names); `watchChanInv` gains
  `"Hapi" ∷ chanApi γ ch γc sent` (`∃ l dec rw, chanApiAt (wsAbsOf γ ch γc) l dec rw ∗
  ⌜sendsOf l = sent.map RespM.toW⌝`). **The consumer's view `rw` is not yet tied to the channel's
  received prefix `recv`**: the receives (`WatchRecv`) frame `chanApi`; item 2 ties it (`rw =
  recv.map toW`, or `γc.recv` replaced by `γc.arcv`) when it rewrites the receive lemmas.
- `watchableStore.NewWatchStream`: allocates it (`chanApi_alloc`), its spec's post now also
  `api.wsStateI (wsAbsOf γ ch γc) wsStart ∗ api.wsRecvI (wsAbsOf γ ch γc) []` (its interface file
  to regenerate once the package builds whole).
- The registration (`watch_register`), `cancel_ghost`, the channel's close (`WatchClose`) and the
  17 receive sites frame `chanApi` (no API event yet: see below).
- **The two sends** (`watcher.send`, `WatchCmpSend.cmp_send_inner`) append their response through
  **one placeholder**, `M1Placeholders.chanApi_send_M1` (`chanApi γ ch γc sent ⊢ |==> chanApi γ ch
  γc (sent ++ [x])`, `sorry -- M1-REPLACE: wsChan_recv.law, wsRecv_ok.law (a send's stepOk)`).
  Not in `etc/tcb-baseline.txt` (nor are stage 1's placeholders: the build beyond mvcc is red).

**Done since** (2026-11-05, the senders' tokens, no `sorry`): `StreamLog.replay_reg` (a registration
in a well-formed history: the replay has its registry info at its id for good), `replay_D_mono`,
`replay_cancel` (a cancel after a registration: its id in the replay's cancelled set);
`StreamSteps.regTok`/`cancelTok` (persistent history lower bounds with the event), minted from the
authority (`chanApiAt_regTok`, `chanApiAt_cancelTok`) and used at it (`chanApiAt_regAgree`: a send's
`factAgree`; `chanApiAt_dead`: a `-1` send's `deadIn`); `InvWatchStore.recvEvs_toW` and
`chan_recvEvs` (from the channel invariant's `respOk`s and `chanRegFact`s: the client's `recvEvs` at a
registered watcher's id is the watcher's sent events, today's `chanWatcher` filter by `x.w`), so (b)
and (c) below are done but for minting the tokens where the events are appended.

**Done since** (2026-11-05, item 2, no `sorry`): **`wsChan_recv.law` proved**
(`Api/WatchLaws.wsChan_recv.law_holds`, over `wsChan_recvI` at a stream's names `wsAbsOf γw ch γc`;
`#print axioms`: no `sorryAx`). `isMvccWatchStreamRest` defined (private, sealed): a watchable
store's names `γw` (`γw.st = γ`) and the channel's `γc` with `ι = wsAbsOf γw ι.ch γc`, the buffered
channel (`isChan`, `0 < chanCap`) and `inv watchN (watchChanInv γw ι.ch γc)`; item 3 adds the
stream's own invariant (`isWatchStream`). The API view is tied to the channel's received prefix:
`chanApi γ ch γc sent recv` (the history's consumer view `recv.map toW`); `watchConsumer γc ms` is
both halves (`γc.recv` at `ms`, `γc.arcv` at `ms.map toW`), and the API's `wsRecvI` holds it
(`WsAbs.crecv := γc.recv`; `rx` an exclusive token fixed at `0`, so a receive needs no update
outside the invariant); `RespM` moved to `WatchModel`, `RespM.toW` to `Api/StreamGhost`. The receive
lemmas (`watch_recv_au`, `watch_tryrecv_au_alt`) move both views at each receive (`chanApi_recv`) and
hand the receiver its lower bound (`apiRecvLb`, in `watchRecvResult`, now taking `ch`); the
non-blocking receive takes a `wsSentLbI` and its empty case gives `n ≤ received.length`
(`chanApi_sentLb`). `NewWatchStream` returns `wsRecvI` in place of `watchConsumer γc []` (v3rpc's
`sendLoop` uses the latter: red under strict M1). `chanApiAt_recv` (the abstract receive step)
removed, superseded.

**What each remaining step needs of the internals** (found wiring; none is a frozen statement's
problem: no frozen statement found false):
- *The send's `stepOk`* (replacing `chanApi_send_M1`): the sender passes its event `.send (toW x)
  fg rg lo L c0 cov dead`. (a) **Saved filters per watcher**: today a delivery's filters are
  `∃ fs, filtersImpl fcs fs` per delivery (`chanWatcher`, `covFact`), and `watcher.send` takes
  `filtersOk fcs`; the history needs one `fs` per watcher by name: `WatcherNames` gains `fg` with
  `savedFilters γw.fg fs ∗ filtersImpl fcs fs` (from `Watch`'s `filtersImpl fcs fs`, through `watch`'s
  `P.F`/`IWF`, M3), each delivery `savedFilters γw.fg fs ∗ ⌜dl.2 = filtered fs dl.1⌝`. (b) **A
  registration token per watcher** (`∃ l, monoListLbOwn ι.ev l ∗ ⌜.reg id rg fg lo ∈ l⌝`, minted at
  the registration) and the pure lemma that a well-formed history's replay has the registered info
  at `id` (ids fresh at `reg`, never removed), for `factAgree`. (c) **id-to-watcher uniqueness of
  the sent responses** (for `recvEvs` by id vs today's filter by `x.w`): from `respOk` and
  `chanRegFact` (`chanIdAssigned` agreement), both in the channel invariant. (d) **A notified-log
  lower bound at every send** (`nlLb`, minted at the notify update's commit, kept in
  `watchStoreInv`; `moveVictims` sends without `s.mu`: the bound recorded with the victim batch)
  and `crevAtLeast` for the compaction response (§4.5). (e) **Event positivity** (`respShape`'s
  last conjunct) from the log's receipt (§5, round 16). (f) **Exactness under `onceUpTo` only**
  (§4.4): today's delivery is exact under `watchNoDup`, which `Watch`'s frozen contract does not
  give; `evsWf`/`covFact`'s exactness becomes `onceUpTo L lo c₀ → ...` and the catch-up read after a
  compaction is proved under it. (g) **`-1` responses**: `stampsAt` (every watcher of the stream's
  state registered by then covered, or its id cancelled in the history: today's `rsnW`/`rsnFor`
  becomes a history lower bound with `.cancel id`, deposited at `Cancel`'s first check, D4/D5).
- *The registration* (`watch_register`, `chanApiAt_reg`): `isWatchable`'s callback (`∀ w, ⌜w ≠
  null⌝ -∗ |==> chanIdAssigned γc id w ∗ Back w`) must run with the channel invariant open and be
  handed its `chanApiAt` (to append `.reg` at `(sendsOf l).length`, the exact sent count) and the
  store's shares at the registration (`revMuBody`'s `slotX` and the watch lock's `wsSlot`, both held
  there, `watchableStore__watch.lean:787`), so that `Watch`'s update can fire with `watchLo σ
  startRev = lo` and `σ.pending = none`. **`wsSlot` must then say `pending = none` at the lock's
  release** (today `pndOk Lmu p` allows `some ps` with `Lmu` ending in `ps`; Go commits under `s.mu`,
  `watchableStoreTxnWrite.End`, so it is true). The caller's update is `watchStream.Watch`'s, i.e.
  item 3's `Watch` contract: the registration step and that contract go together.
- *Cancel* (`chanApiAt_cancel`): at `watchStream.Cancel`'s first check, opening the channel
  invariant from the stream's (`isWatchStream`'s `inv`), with the client's `wsState` from the
  contract's update: item 3 as well.

**Left** (in order):
1. **The channel invariant's API part, wired in** (*wired 2026-11-05, above; left: the sends'
   `stepOk`, the registration, the cancel*) (`watchChanInv`, `InvWatchStore.lean:820`):
   `WatchChanNames` gains the stream's API names (countable: `st : AbsNames`, `ev`, `ns`, `rcv`,
   `rx`), and `watchChanInv` the conjunct `∃ l dec, chanApiAt ι l dec (recv.map toW) ∗
   ⌜sendsOf l = sent.map toW⌝` (`toW : RespM → WResp`: id, events, revision, compaction
   revision). The sites: `watcher__send` and `WatchCmpSend` (the sends: `chanApiAt_send`),
   `WatchRecv` (the receives: `chanApiAt_recv`, `chanApiAt_sentLb`; 17 unfolds),
   `watchableStore__watch` (the registration: `chanApiAt_reg`), `watchableStore__cancelWatcher` and
   the stream's `Cancel` (`chanApiAt_cancel`), `WatchClose`, `watchableStore__NewWatchStream`
   (`chanApi_alloc`), and outside mvcc v3rpc's `InvWatch` (red under strict M1). The rest of this
   item as specified below:
   authority `monoListAuthOwn ι.ev 1 ℓ` with `LogWF dec ℓ` (the senders' facts' filters by their
   saved names: a registry element names its watcher's `savedFilters`), the sent list (`RespM`)
   projecting to `sendsOf ℓ`, the consumer's other half of `ι.rcv`, a lower bound of `ι.ns` at
   `nsCount ℓ`, and each send's `evTok` (`nlLb` from the store's lower bound, which
   `watchStoreInv` keeps, minted at each notify commit; `crevAtLeast`). Every send (`notify`,
   `syncWatchers`, `moveVictims`, `progressIfSync`, the compaction response) appends its event,
   proving `stepOk` from today's facts (`respCov`/`covFact`/`respRev`/`respCompl`: the delivery,
   the coverage, the cancelled set's `rsnFor`). A registration (`Watch`'s update) appends its event
   at the exact sent count (today's `chanRegAt w n` has `n ≤ sent.length`: make it exact, opened
   at the registration's atomic step); `Cancel`'s first check appends a cancel when the stream's
   state changes.
2. ~~**`isMvccWatchStreamRest`** ... **`wsChan_recv.law`**~~ (done 2026-11-05, above; the
   stream's `isWatchStream` to add at item 3, and the law's proof to adjust then).
3. **The `WatchStream` contracts** at `*watchStream` and `NewWatchStream` (allocating `WsAbs`),
   then the store's side of `mvccState` (its other halves in the internals: they exist, §1).


## Hand-off: stage 2, exactness per watcher (2026-11-05)

**Settled first, as asked: §4.4's per-watcher exactness is true of the code; no frozen statement
found false.** The only place the code delivers a watcher's events inexactly is `syncWatchers`'
backend read, and only at the compaction revision itself: compaction at `c` deletes only keys at
revisions `≤ c` (a deletable key is at a certified compaction revision `c' ≤ c`), and
`syncWatchers` holds `s.store.revMu` shared from reading `compactMainRev` to the end of the scan
(`defer s.store.revMu.RUnlock()`), so no compaction beyond `cQ` can run during the read; a watcher
behind `cQ` gets the compaction response instead. So a member reading above `cQ` gets its exact
events, and one reading from `cQ` loses events only when revision `cQ` changes a key twice, i.e.
exactly when `onceUpTo L lo cQ` fails for it (`lo ≤ minRev = cQ`), for good (both bounds grow).
Revision `cQ`'s single change of a key, a tombstone included, is kept (`kiAvail_unique`, the fork's
`doCompact` with #18274/#22377). Every other delivery (`notify`'s, the victims' resends of a batch
made from either) is in memory.

**Done** (no new `sorry`, no axiom; the mvcc library builds):
- `rangeEvents`' spec without the no-duplicate premise: the scan's events are of the kept entries `P`
  (`(logEnts ..).filter P`), every entry above `c` kept, every entry kept when revision `c` changes
  each key once or `c = -1` (`WatchScan.snapThin_missing_le`, `snapThin_scan_full`,
  `bucketRange_sub`).
- The internal invariant per watcher: `evsWf` is exact or the watcher is `doomed` (a persistent
  witness: the API's `nlLb N` and `crevAtLeast c` with `¬ onceUpTo N lo c`), its events then of
  revisions from `lo` on; `covFact` and `watchRecvOk` carry the same disjunct. `syncWatchers`
  per member (`SyncModel.sw_memberBatch_cases`): exact batch when revision `cQ` changes each key once
  or the member reads above `cQ` (`memberBatch_filter_above`), else a sub-list and the member doomed
  (`memberBatch_sublist`, `SyncWatchersLemmas.sw_evsWf_step`); the witness's bounds are the lock's
  `nlLb` (`wsSlot` now holds the API's `nlLb` at the notified log; produced where the notified log
  moves, today by the `wsSlot_*_M1` placeholders, by `New`/`End`'s notify contract at the
  migration) and `s.revMu`'s `crevAtLeast` (`slotX_crevLb`).
- `watchNoDup` is no longer needed: `storeWatchParams`' `T` is the watch token alone, `wsWatchFrozen`
  is vestigial (`True`; its conjunct in `watchStoreBody` is left for a cleanup), `watchNoDup_crev`
  removed. The definitions `watchNoDup`/`noDupKeys` stay for v3rpc's proofs (red under strict M1),
  which should drop them at the migration.

**Done since** (2026-11-05, (a), no new `sorry`): one saved filter set per watcher: `WatcherNames.fg`
(the predicates' saved name, `api.savedFilters`, allocated by `watch_register` from the filters'
choice, `filtersOk_of`); a registered watcher holds `watcherFilters γw fcs` (its filters implement
the saved predicates) in place of `filtersOk` (`memberRes`, `watcher.send`'s spec, `cmp_send`, the
lock's lemmas), and every delivery in `chanWatcher`/`covFact` records the saved predicates it was
filtered by, so all of a watcher's deliveries agree (`savedFilters_agree`) and the history's
send can name `γw.fg`.

**Left** (the previous hand-off's list, "What each remaining step needs of the internals", minus
(f) and (a)): (b) the registration appending `.reg` (needs the client's
`wsState`, i.e. the `Watch` contract, item 3) at the exact sent count, `wsSlot` at `pending = none`
while the lock is free; (d) a notified-log lower bound at every send (the lock has one now,
`wsSlot_nlLb`; `moveVictims` must carry it with the batch) and the compaction response's
`crevAtLeast` (§4.5); (e) event positivity (no lemma yet that a certified log's watch events have
positive revisions, creation revisions and versions: needed for the sends and for the `Range`
contracts' `stateOk`; a doomed watcher's events are a sub-list of them, so the same lemma serves);
(g) `-1` responses' cancel tokens; then each send's
`stepOk` from these facts and `chanApi_send_M1` gone. For a doomed watcher the send's fact takes
the doom witness's bounds (the longer `nlLb`, the larger `crevAtLeast`), making its delivery and
progress conjuncts vacuous.

## Hand-off: stage 2, the sends' bounds (2026-11-05)

**Done** (no new `sorry`, no axiom; the mvcc library builds: `mvcc.Link`, `Results`, `Api`,
`Api/WatchLaws`, `Api/Instance`; no frozen statement found false):
- **(e) Event positivity.** `WatchPos.lean` (pure): every event of a log whose revision `0` is empty,
  with fewer than `2 ^ 63` revisions and `2 ^ 63 - 1` changes, is positive (`evPos`: revision, and a
  put's creation revision and version; `logEvents_pos`, `watchEvents_pos`, `filtered_pos`; through
  `stateAfter_pos`, every key-value of the log's states in `[1, R]`/`[1, V]`). `evLog` records
  `logCh L < 2 ^ 48` (`evLog_of_sealed`/`evLog_of_cert` take the store's receipt bound,
  `isStore_rb`, `isWatchableStore_rb`), so `evLog_pos`; `evsWf`'s doomed branch records its events
  positive (`syncWatchers`' sub-list of a watched log's, notify's new revision's), so `evsWf_pos`
  holds for exact and doomed watchers alike.
- **(d) The bounds at every send.** `evLog` is a lower bound of the API's notified log
  (`api.nlLb γ.api L`, `evLog_nlLb`; `evLog_nil` mints `[]`'s): every delivery (`evsWf`), covered
  watcher (`covFact`) and doom witness is over the API's history. Its producers: the watchable
  `End` (the API slot's step, still `wsSlot_step_M1`, **moved to the release point**, before the
  revision's events go out, where §3 has the notify fire), `syncWatchers` (its committed log is the
  lock's notified one, `HCL`, so the lock's `wsSlot_nlLb`). Every response but a compaction
  response is sent at a revision of it: `respRev` gains `⌜x.compactRev ≠ 0⌝ ∨ revApi γ x.rev`
  (`revApi`: an `nlLb N` with `rev < |N|`), `watcher.send` takes `revApi γ wr.Revision'` (notify:
  the new log; `syncWatchers`: the committed log; `moveVictims`: the victim's delivery,
  `mv_revApi`, so nothing more is carried with the batch; `progressIfSync`: the lock's slot at
  `σ.Lmu`). A compaction response's revision is at most the API's compaction revision:
  `cmpPerm γ c = crevPermAt γ.st c ∗ api.crevAtLeast γ.st.api c` in `cmpPermOf`, the `choose`/
  `chooseAll` specs and `cmp_send_inner`, from `syncWatchers`' `s.revMu` slot (`slotX_crevLb`).
- **Delivery certificates** (`WatchSendApi.lean`): `delivCert a P`, lower bounds `(L', c')` of the
  API's notified log and compaction revision (`c' = -1`: none) with `P` at every larger pair;
  `delivCert_join` (the longer log, the larger bound), `delivCert_mono`, `delivCert_elim`. The
  certificates: `revApi_cert` (`rev < |L|`), `evsWf_cert`, `covFact_cert`, and the two a send
  needs: `chanWatcher_cert` (a registered watcher's sent events, by its saved filters, are its kept
  events of `[lo, hi)` of every larger log while `onceUpTo`, and positive) and `covFact_recv` (a
  covered watcher's events sent before the response, up to its revision `+ 1`).

**How a send's `stepOk` assembles** (at `watcher.send`, after `entries_deliver` and `sentAuth_snoc`,
the channel invariant open; the event `.send (toW x) γw.fg r γw.lo L c0 cov dead`; `dec γw.fg` the
saved filters `fs0`):
- `respShape`: events at or below the revision (`respOk`); `rev < |L|` (`revApi_cert`); a `-1`
  response's (`respCompl`); positivity (`chanWatcher_cert`: `x.evs` are among `w`'s sent events).
- the own delivery: `chanWatcher_cert` at `sent ++ [x]`, with `chan_recvEvs` (the client's
  `recvEvs` by id is `w`'s sent events); also for the compaction response (no events: its
  delivery conjunct is `w`'s events so far).
- the own progress (no events): `covFact_recv` for `w` (`w ∈ x.cov`; `rev ≥ 0` from the lent log,
  non-empty), `recvEvs (pre ++ [x]) id = recvEvs pre id`.
- a `-1` response's coverage: `covFact_recv` for each `w' ∈ x.cov`, `cov` its watchers' `(id, r,
  fg, lo)`.
- one pair: join the certificates (`delivCert_join`), `delivCert_elim`; `evTok` needs
  `crevAtLeast c0`: mint `crevAtLeast (-1)` (a `monoNatLbOwn _ 0`) at the send's update when
  `c0 = -1`.
- **what needs the registration** (blocked, as the previous hand-off said): `factAgree` (a `regTok`
  for `w` and for each covered watcher: the registration deposits it, e.g. in `chanRegFact`, which
  every registered watcher has in the channel invariant); `stampsAt` (an invariant of `chanApi` to
  add with the registration: each `.reg id ..` of the history, at stamp `k`, is a channel-registered
  watcher `wl` with `RI wl = k` and `chanIdAssigned γc id wl`; then `regsOk` puts `wl` in `x.regs`,
  `respCompl` makes it covered, its id `c.id`, or `rsnW`); `deadIn` (a `cancelTok` for each `rsnW`
  watcher in place of `rsnFor`, deposited by `Cancel`'s update).

**Left** (in order): the registration appending `.reg` at the exact sent count with `Watch`'s update
(the store's side of `mvccState` at the registration: `σ.log` the committed log under `s.revMu`'s
slot, `σ.pending = none` from `wsSlot` while the lock is free, `watchLo σ startRev = γw.lo`), and
`chanApi`'s `stampsAt` invariant; `Cancel`'s update and the cancel tokens; each send's `stepOk` as
above, then `chanApi_send_M1` deleted; the `WatchStream` contracts and `NewWatchStream`.

**Done since** (2026-11-05, no `sorry`): `WatchSendApi.holds_own`, `holds_cmp`, `holds_all` (pure): a
send's `SentFact.holds` from its parts for each kind of response (a watcher's own, a compaction
response, a stream-wide progress response), the parts being what the certificates above give at
the joined pair. **The registration's design point** (found surveying it, for the next step): the
store's registration callback is `isWatchable`'s `∀ w, ⌜w ≠ null⌝ -∗ |==> chanIdAssigned γc id w ∗
Back w` (`InvWatchStream.lean:294`), a plain update with neither the channel invariant nor the
store's slots; to append `.reg` at the exact sent count it must become a fancy update run with the
channel invariant open (its `chanApiAt` and `sentAuth`) and the store's slots in hand (`revMuBody`'s
`slotX`, the watch lock's `wsSlot`, at `watchableStore__watch.lean:787`), firing `Watch`'s atomic
update (the client's `mvccState`/`wsState`), and deposit the watcher's `regTok` where the sends find
it (`chanRegFact`). `isWatchable` is generic over `WatchParams` and v3rpc's proofs use it (red under
strict M1).

## Hand-off: stage 2, the registration and the stream's contracts (2026-11-05)

**Done** (the mvcc library builds: `mvcc.Link`, `Results`, `Api/WatchLaws`, `Api/Instance`; no new
`sorry`, no axiom; no frozen statement found false). `#print axioms` of `mvcc.watchStream.wp_Watch`,
`wp_Cancel`, `wp_Close` (the API's `WatchStream.Watch/Cancel/Close.contract` at `*watchStream`,
`Spec/.../mvcc/watchStream__{Watch,Cancel,Close}.lean` now the API's contracts): no `sorryAx`.
`watcher.wp_send` still has it (`chanApi_send_M1`).
- **The stream knows its client's state.** `WsAbs.cl` (`WatchChanNames.acl`): the history at the
  client's last event, a ghost variable, half in `wsStateI`, half in the stream's mutex invariant
  (`watchStreamInv`'s `"Hacl"`), with the pure tie `wsRel nextID closed CM CS (replay d lm).S` at
  every decoding `d` (the client's state closed exactly when the stream is; its watchers' ids in
  `[0, nextID)`; every cancel closure a watcher's; every live watcher of an open stream has its
  closure; every id of `CS` a watcher not live). `CS` (`WsStreamNames.cs`, a monotone list,
  lower bounds `idCancelled`) is what `Cancel`'s second critical section needs to drop a closure.
  The client's steps take the stream's half too (`chanApiAt_reg`, `chanApiAt_cancel`,
  `chanApiAt_close`, `wsStateI_cl`); the `wsRel` steps are pure (`wsRel_register`, `_cancel`,
  `_delete`, `_close`, `_next`; `replay_ws_isSome`: which ids are watched is decoding-free).
- **The registration callback is the store's** (`WatchParams.RegCb`, the store's `regCb`): run by
  `watch_register` with the channel invariant open (the history `l`), `s.revMu`'s part of the view
  (`revMuAbs` at the committed log `C`) and the watch lock's pending revision (`wsSlot` is now
  `pndPart … none`: the watchable `End` notifies and commits under `s.mu`; `pndOk` gone), it
  appends `.reg rg.id rg fg lo` at the exact sent count and gives the store its parts back. The
  filters are the caller's predicates (`WatchParams.FI`, `filtersImpl`; `F` gone), saved under the
  watcher's `fg`. `Api/StreamHandle.watch_regCb` builds it from `Watch`'s update (the store's
  state agreeing with the client's: `σ.log = C`, `σ.pending = none`, `watchLo σ startRev = lo`).
- **Cancel tokens** in place of `rsnFor`: `chanCancelTok γc id` (a history lower bound ending in
  `.cancel id` after the registration; `api.cancelTok` at the stream's names), minted by
  `Cancel`'s update for a watcher of the client's state (`cancel_fire`, `chanApiAt_cancel_tok`);
  `cancelledFor` and `rsnW` carry it. `rsnFor`/`progFact`'s saved predicates and the stream's
  `watchStreamOpen` token are now unused by mvcc (left for the cleanup; `NewWatchStream` still
  returns them).
- **`isMvccWatchStream`** holds the stream over the watchable store at its channel
  (`isWatchStreamAt`, split out of `isWatchStream`), the store's watch-token pool and a thread pool
  of `watchReader`s (`watchRdPoolN`): `Watch` borrows a reader with its thread token and takes a
  watch token for a time receipt. `NewWatchStream`'s contract must produce them (from `isMvcc`,
  still `True`: its pools, §4.7).
- `Api/StreamHandle.lean` (private, `import all`ed by the contracts' proofs: its statements mix
  the sealed names with the internals', which only a module seeing the sealed bodies can state):
  `isMvccWatchStream_open`, `watch_regCb`, `watch_fire_closed`, `cancel_fire`, `close_fire`,
  `watchChanInv_api`. `wsAbsOf` is an `abbrev` (so `(wsAbsOf γ ch γc).cl` is `γc.acl` to `iexact`).
- `Close`'s contract proved as well (the invariant change needed its proof redone): its update
  fires at the lock, its premise `S.closed = false` excludes a second close.

**Left** (in order):
1. **Each send's `stepOk`**, then `chanApi_send_M1` deleted (`watcher.send`, `WatchCmpSend`),
   as "Hand-off: stage 2, the sends' bounds" says, with two pieces of infrastructure first, both
   established in `watch_register` right after the callback (it knows `w`, its `chanRegAt γc w
   sent.length`, `watcherFixed w r fcs`, `γw.fg`, `γw.lo`, and the history's new last event):
   (a) a registration token per channel-registered watcher (`chanRegTok γc r.id r γw.fg γw.lo`,
   `api.regTok` at the stream's names; in `chanWatcher`, or in `covFact`, for the covered
   watchers of a `-1` response), for `factAgree`; (b) `chanApi`'s per-registration witness (each
   `.reg id rg fg lo` at position `p` of the history is a watcher `wl` with `chanRegAt γc wl
   (sendsOf (l.take p)).length`, `watcherFixed wl rg _`, `watcherMeta` with `fg`, `lo`), kept by
   the sends, cancels and closes (no registration), for `stampsAt`: with `regsOk`, every such `wl`
   is in a `-1` response's `regs`, so covered or `rsnW` (whose `chanCancelTok` is `deadIn`'s). The
   `-1` sender then names its `cov` and `dead` lists from `x.cov` and the `rsnW` watchers (a choice
   over a list of persistent existentials, as `filters_choose`).
2. ~~`Chan`, `RequestProgress`, `RequestProgressAll`~~ (done since, below); `Rev` at
   `*watchStream` (its update fires at the store's read: `isWatchable`'s `rev()` triple needs the
   same treatment as the registration, a fancy update with `s.revMu`'s view in hand; its internal
   spec is still the generic one over `WatchParams`); `NewWatchStream` at `*watchableStore`
   (needs `isMvcc`'s pools, and must give the handle's: the watch tokens, the readers, the
   channel's progress fact).
3. The cleanup: `rsnFor`, `WsStreamNames.rsn`, `progFact`'s use by `progressAll` (the `-1`
   response's API fact replaces it), `watchStreamOpen`.

**Done since** (2026-11-05, no `sorry`): `WatchStream.Chan`, `RequestProgress` and
`RequestProgressAll` at `*watchStream` (their spec files now the API's contracts; `#print axioms`:
no `sorryAx`). `isMvccWatchStream` gains the channel's progress fact (`progFact γc.prog`, what
`progressAll` is lent); the reader slot each borrows from the handle's pool with its thread token,
given back before the last step (`wp_fupd`).

## Hand-off: stage 2, the sends' stepOk, Rev and NewWatchStream (2026-11-05)

**Done** (the whole mvcc tree builds, 394 modules; no new `sorry`, no axiom; no frozen statement
found false; interfaces regenerated, the API's unchanged):
- **Each send's `stepOk`, `chanApi_send_M1` deleted.** `#print axioms mvcc.watcher.wp_send`: no
  `sorryAx` (nor `cmp_send_inner`'s users, `syncWatchers`). The two pieces of infrastructure:
  (a) **registration tokens**: `chanRegTok γc id rg fg lo` (`InvWatchStream`, a lower bound of
  `γc.aev` holding the `.reg`; `api.regTok` at the stream's names), and `chanRegW γ γc w` (the
  watcher's names, fixed range and its `chanRegTok`), kept for every registered watcher in
  `watchChanInv` (`"#Hrt"`, beside `"#Hrf"`), minted by `watch_register` right after the callback
  (`chanApiAt_regTok`); (b) **registration witnesses**: `regWit γc l` in `chanApi` (every `.reg id rg
  _ _` of the history is a watcher of the channel's registered set `γc.reg`, with fixed range `rg`,
  `id = rg.id`), kept by every non-registration step (`regWit_app`), extended by `watch_register`
  (`regWit_reg`), `regWit_nil` at `NewWatchStream`. (Not with positions/stamps: a `-1` response's
  `regs` is the channel's whole registered list `L`, so membership suffices.)
  The assembly (`WatchSendApi.lean`, "A send's premises"): `stepOk_own`/`stepOk_all` (pure: the
  replay's registry info from the `.reg` in the history, `replay_reg`; stamps from
  `replay_ws_reg`); `own_cert` (the watcher's registration in the history, its saved filters the
  decoding's, `chan_recvEvs`, `chanWatcher_cert`); `cov_certs` (each covered watcher's
  `covFact_recv`, joined); `stamps_of` (a `-1` response: every registration a watcher of `L = x.regs`,
  so covered — one of `cs`, by its fixed range's id — or `rsnW`, its id in the replay's cancelled
  set: `chanApiAt_dead`); `chanApi_finish` (the event appended, `crevAtLeast (-1)` minted when no
  compaction bound); `chanApi_send_resp` (`watcher.send`: own or `-1`; `dead` is the replay's whole
  cancelled set) and `chanApi_send_cmp` (`cmp_send_inner`, its compaction bound from `cmpPerm`).
- **`WatchStream.Rev.contract` at `*watchStream`** (`#print axioms mvcc.watchStream.wp_Rev`: no
  `sorryAx`). The read's update fires in `store.Read` under `s.revMu`: `store.Read.spec` takes a
  **read callback** `readCb γ F` (`InvStore`: run with `s.revMu`'s `slotX` at the log read, giving
  `F log` in the post; callers with nothing to fire pass `readCb_true`: `kvOver_Read`,
  `store.Read.spec_R`, `Results`' `mvcc_store_Read_after_Compact`, `progressIfSync`'s `rev`);
  `watchableStore.rev.spec`/`specR` pass it through; `WatchParams.RevCb` (the store's: `readCb γ.st`)
  and `isWatchable`'s `rev()` triple `∀ F, {{ P.R ∗ P.RevCb F }} … {{ r, P.R ∗ ∃ L, F L ∗ ⌜L ≠ [] ∧ r =
  L.length - 1⌝ }}`; `StreamHandle.rev_readCb` builds the callback from `Rev`'s update (agreement of
  the client's `absPart` with the slot's). The same callback is what `KV.Read`/`Rev`/`FirstRev`'s and
  `Range`'s contracts at the store need (§3, first row).
- **`WatchableKV.NewWatchStream.contract` at `*watchableStore`** (its spec file now the contract;
  `#print axioms mvcc.watchableStore.NewWatchStream.wp_proof`: no `sorryAx`; the linked
  `wp_NewWatchStream` has one only through `metricsTxnWrite.wp_End`, the store's `End` and its
  `M1-REPLACE` placeholders, via `watchableStore.rev`/`progress`/`progressAll`). **`isMvcc` defined**
  (`Api.lean`, `@[no_expose]`): `□ (isMvccPlain kv γ ∨ isMvccWatchable kv γ)`, a plain store's handle
  (`isStore`) or a watchable store's (`isWatchableStore s st γw` with `γw.st = γ`, `watchTokPool γw`,
  a thread pool of `watchReader`s at `watchRdPoolN`). The stream's progress fact is `True` (the
  saved proposition), its cancel reason `fun _ => True`; `watchStreamOpen` no longer returned.
  **Left of `isMvcc`** (§2): the plain store's readers' pool, the write-back supply, the store's
  own goroutines' readers from the pool (U2), and what `mvccState_reachable.law` and the shape law
  need (the receipt bound, the contracts at the type); no producer of `isMvcc` yet (`New`/`NewStore`
  give it at their contracts).

**Left** (in order):
1. The cleanup (not done: not cheap enough for the time left): `rsnFor` and `WsStreamNames.rsn`/
   `WatchChanNames.rsn` (unused by mvcc now; `client/v3`'s `WatchRun` still names `rsnFor`),
   `watchStreamOpen`/`WsStreamNames.tok` (unused by mvcc; v3rpc's `serverWatchStream.close` spec
   names it), `progFact`'s use by `progressAll` (`watchChanInv`'s `"#Hpf"`, `complW`: the `-1`
   response's API fact replaces it; `isMvccWatchStream` still carries `progFact γc.prog`, now of
   `True`).
2. The other contracts (`KV.*` at both stores with `readCb` at the reads, `Txn.*`, the
   constructors producing `isMvcc`), replacing the remaining `M1-REPLACE` placeholders.

## Hand-off: stage 2, the snapshot image (2026-11-05)

**Done** (the mvcc modules build; no axiom; one new `sorry`, the listed placeholder `snapObs_M1`; no
frozen statement found false; one frozen statement found insufficient for the clients, finding 5):
- **`Api/SnapImage.lean`** (pure, no `sorry`): probe 2's proved cores (`entsCutAt_jobs`,
  `entsCutAt_jobStep`, `jobPast_skip`, `KeyDel_down`, `KeyDel_mono`, `reach_shape`, `image_of_obs_exact`);
  the image's facts **`imageOk D L c u`** (the `Key` bucket entries `ents` cut at `c`, the compaction
  keys the records `rc` of `L` past `0`, `rc.crev = c`, `rc.resumes = u`, `restore()`'s last
  revision, `L` well formed of a reachable shape), `imageOk_keyImageM` (the restore image, both modes
  at `-1`), `imageOk_fresh`; the image from an observation over **any** logical view (`cutOk L m X c`:
  the physical bucket, `m` but the deleted `X`, is entries cut at `c`; `key_of_cut`, `imageOk_of_cut`;
  a restored store's view is thinned, so the probe's `hLv : Lv = bucketMap L` does not hold in general);
  the cut under the store's steps (`physLookup`, `cutOk_mono`, `cutAt_del`: the job's delete with its
  loop invariant and the backend's record of the delete, `hX'`).
- **`Api.lean`**: `mvccImage D L c u := ⧖ (logCh L) ∗ ⌜snap.imageOk D L c u⌝` and **`mvccBackend γ q B
  Pk`** (`shareTok γ.api q`, `curAt (γ.withPhys p) q/8 o` at the current names, `p.kb = some d`,
  `d.cm` (the API is always compacting), `B = ⟨d.γB, d.P, d.be⟩`, `□ isBackend … (mvccW d.gx) Pk d.be`),
  sealed. `mvccW`/`mvccWReg` still opaque (finding 5).
- **`Api/SnapLaws.lean`**: `mvccImage_fresh.law_holds`, `mvccBackend_agree.law_holds`,
  `mvccBackend_fractional`, `mvccImage_persistent`, `isMvcc_persistent` (no `sorryAx`);
  **`mvccImage_snapshot.law_holds`**, whose `#print axioms` has `sorryAx` only through `snapObs_M1`.
  The proof: the share's token and the current names from `mvccBackend γ 1`; the writer frozen
  (`writerInv_freezeNL`); the client's update committed at once, the frozen writer's slot `slotY`
  agreeing with `mvccState` (so the state is the writer's log and compaction revision); the
  snapshot called with `R ∗ snapFrozen` and the observation `Q d r ∧ b ∧ snapObsOk σ.log σ.crev vd
  v`; thawed (`writerInv_thawNL`); the image from `imageOk_of_snapObsOk` (`sData`'s `Key` part is
  the data's, `fkVals` the records) and the frozen writer's certificate's receipt.
- **`Api/SnapFreeze.lean`**: `writerInv_freezeNL`/`_thawNL` (no later credit), `writerL_split`,
  `snapFrozen s γ σ b` (the frozen flag's half and the writer's state at `σ`, or the open writer's
  key), `snapObsOk`, `imageOk_of_snapObsOk`, and the placeholder **`snapObs_M1`** (`M1-REPLACE`: the
  frozen store's part of the observation, `snapFrozen ∗ mvccW d.gx ∗ viewAtD ∗ dlsOwn X ∗ fkdOwn v ⊢
  ⌜b = true ∧ snapObsOk σ.log σ.crev vd v⌝`; listed in `M1Placeholders.lean`'s header).

**Findings** (what the store-side tracking must be, replacing `snapObs_M1`):
1. **No later credit.** The law's code is the `Snapshot()` call alone: no step before or after it, so
   the freeze and thaw open `writerInv` without credits, the taken state kept under the later but for
   its timeless parts (`writerL_split`). Any store-side fact the replacement needs non-later must be
   timeless or taken out at the freeze.
2. **The observation opens nothing.** `backend.Snapshot`'s observation is a plain wand to `⌜Q⌝`, so
   what it needs of the store is in `W` (`mvccW d.gx`, the batch lock's client resource: `lateW`,
   `writerRes`) or in the freezer's `R`. Hence:
   (a) **mvcc's halves of `fkdOwn` and `dlsOwn` move out of `mwInv`** (today inside the write right
   `kbMW = ∃ f, fkOwn γB f`, which the observation cannot reach) into `compactRes`, pinned: `fkdOwn γB
   (recBytes fin, recBytes sched)` of `metaCompact`'s records, `dlsOwn γB X` with `cutOk L m X
   rc.crev` (`m` the writer's view: `writerRes` must name its bucket, today hidden in `bucketViewL`),
   `recsOk L rc`, `recsPos rc`, and for the running job its cursor (`entsCutAt_jobStep`'s `hpast`, a
   ghost variable half with the job). `mwInv` keeps the flag's half; a session holder assembles
   `fkOwn` from the swap and `compactRes`, and splits it back.
   (b) **The store's backend contract hides the values.** `batchTxSpecG`'s delete and `Meta` put (and
   the backend's `UnsafeDelete`/`UnsafePut` specs, via `dlPut`/`fkPut`) take and give back `∃ f, fkOwn
   γB f`: the job cannot re-pin (a). The contract (`InvStore`, proved in `BackendBridge` from
   `batchLocked`'s exact session state, `batchLocked_fkd` and its `dlsOwn` analogue) must expose the
   delete's `X'` (`cutAt_del`'s `hX'`: the entry recorded iff present, `BSess.del`) and the put's new
   compaction-key values.
   (c) **The records' revision tied to the writer's.** `compactRes` knows `(sched, fin)`, not `σ.crev`;
   `Compact` writes `compactMainRev` (with `writerInv` open) before `SetScheduledCompact` (under the
   batch lock). A ghost `AbsNames.rcv`, half in `compactRes` at `rc.crev`, half in `writerAbs` with
   `cr = c ∨ ∃ q, shareTok a q` (`Compact` deposits part of its share between the two writes): the
   whole share then gives `rc.crev = σ.crev`.
   (d) **The pending registration.** After a `Restore` that resumes nothing, `writerReg` holds `kbRegRight
   ∗ writerRes` and the lock's `lateW` is unregistered until the first lock holder: the observation
   sees neither. Fix: the freezer takes `writerRes` out of a pending `writerReg` into its `R` (a third
   state, lent), every other opener excluded: writers and `Compact` by their share (the frozen state in
   `writerInv`), the job by a `storeRegd` in its premise (a job is scheduled only by `Compact` or a
   resuming `Restore`, both of which take the batch lock, hence register, first).
   (e) **An open write transaction** (`b = false`): its writer's key is the freezer's, so a commit's
   `W` (registered: `storeRegd`) holding `writerKey` contradicts it: provable once `mvccW := lateW`.
3. `cutOk` is the right inductive fact for the observation (not the probe's jobs list): it covers a
   restored, thinned view; the jobs' closed form `entsOfJobs` stays the cut's witness for a store
   booted fresh.
4. **`mvccBackendFor_open.law` needs** (M3): `mvccW`/`mvccWReg` defined (`lateW`/`lateReg`); from
   `mvccImage`, `imageOk_keyImageM` for `restoreImageM_of_open`, the receipt kept in `mvccBackendFor`;
   the store's tracked state at the open (a): `X = ∅` and the open's compaction-key values, which
   `fkCl`'s `fkOwn γ (fkInit D)` hides (`∃ v, fkdOwn γ v`, `∃ X, dlsOwn γ X`): the backend's open
   (`NewAlloc`, `fkCl`) must give `fkdOwn γ (fkVals D) ∗ dlsOwn γ ∅`; the cut at the open from
   `imageOk`'s `ents` (`physLookup m ∅ = bucketOfEnts ents`, `m` the restored view).
5. **Finding on a frozen statement (insufficient, not false): `mvccW_alloc.law`.** It gives `∃ gx,
   mvccWReg gx` only, but the boot (`notes/mvcc-api-clients/clients-server.md`, step 2) and the snapshot
   path open the backend at `W := mvccW gx`: `backend.New`'s pre needs the client's `∀ γ, hkOwn ∗
   bFresh ={⊤}=∗ W γ ∗ Pk γ ∗ K γ`, i.e. `mvccW gx` from the client, which no law gives; and
   `mvccBackendFor_open` consumes `mvccWReg gx` as well. With `mvccW := lateW` (the lock's unregistered
   half of `gx`) it cannot be made from nothing (a lock holder could otherwise forge it). Minimal fix:
   `mvccW_alloc.law : ⊢ |==> ∃ gx, mvccWReg gx ∗ mvccW gx`. Not changed here (frozen; M3's to decide).

**Left** (in order): (a)-(e), replacing `snapObs_M1` (then `mvccImage_snapshot.law` without `sorry`):
the contract's values (b) first, then `compactRes`'s halves (a) through the job (`cutAt_del`),
`updateCompactRev` (`cutOk_mono`, (c)), `End`'s commit (a cut lemma for a new revision, not written),
`NewStore`/`Restore`; then M3 (`mvccBackendFor`, `_open`, finding 5).

## Hand-off: stage 2, the snapshot image's store-side tracking begun (2026-11-05)

**Done** (the mvcc modules build but `store__scheduleCompaction`, `Results`, `Link`, whose imports
reach etcdserver/txn through `Spec/github_com/dustin/go_humanize/Bytes.lean` (`import
...etcdserver.InvApplier`), red mid-migration by its own agent; `store__scheduleCompaction` was
checked with `lake env lean` on a copy whose humanize spec is a verbatim stub over
`GeneratedProof...etcdserver` (`/tmp/mkscratch.py`'s approach); no axiom, no new `sorry`; no frozen
statement found false):
- **(b) the contract's values** (`2545f1ca52`): `batchTxSpecG`'s write right is indexed, `MW w X`,
  by the compaction keys' values and the deleted entries; the real backend's is `bkMW γB w X`
  (`InvStore`: the client's half of the flag at some value, `fkdOwn γB w`, `dlsOwn γB X`: `fkOwn` with
  its halves exposed; `kbMWv`, and `kbMW := ∃ w X, kbMWv …`, what `mwInv` still holds). The
  compacting range's delete of a key it read (`⌜(m'.lookup k).isSome⌝`) gives `∃ X', MW w X' ∗
  ⌜dlStep X X' k⌝` (exactly `cutAt_del`'s `hX'`); a `Meta` put gives `MW (fkPutV w k v) X`
  (`metaPutCap bt X Y`'s `Y` is now `GoString → GoString → IProp`, applied at the key and value put;
  `UnsafeSetScheduledCompact`/`UnsafeSetFinishedCompact`'s posts at `schedKeyBytes`/`finKeyBytes`
  and `revBytes ⟨value, 0⟩ false`). Proved in `BackendBridge` from the batch lock's exact state
  (`batchLocked_dls`, `batchLocked_bkMW`, `fkVals_putMeta`, `fkVals_delKey`, `dlR_key`; the range's
  token `bkLockedC … m'` keeps every key of the range's bucket present or recorded deleted,
  `keysKept`, `keysKept_del`, `keysKept_putMeta`, `dlStep_del`). The backend's specs are unchanged.
- **M3's first two items** (`f8e4c72fed`): `mvccW gx := lateW gx`, `mvccWReg gx := lateReg gx`
  (sealed), `mvccW_alloc.law_holds` (finding 5's fixed statement).
- **Item 3, pure** (the cut under `End`'s new revision): `Api/SnapImage.lean`'s `cutOk_append` (the
  physical bucket gains the revision's entries, whose keys `X` never recorded), `entsOfRev_pairs`,
  the running job's loop invariant `snap.jobPast` and `jobPast_append`.
- **`CutDefs.lean`** (importable, imported by `InvStore`): the cut's pure vocabulary moved upstream of
  the invariants, unchanged (`Bucket`, `keyName`, `KvEnt`, `entsOfRev`, `logEnts`, `bucketOfEnts`,
  `entsCutAt`, `CmpRecs` and its revisions, `recsOk`, `recsPos`, `recBytes`, `snap.cutOk`,
  `snap.physLookup`, `snap.jobPast`): `compactRes` can now state the cut.

**Findings** (for (a), in addition to the snapshot image's hand-off):
1. **The cut is not inductive without the job's cursor** (`entsCutAt`'s third conjunct needs
   `jobPast` for the running job's delete), and the cursor must survive between the job's batches,
   during which commits append (`jobPast_append`). Design: a ghost variable `γ.jc : Option (Int ×
   Rev)` (a new `StoreNames` field), half in `compactRes` with the pure fact, half in the compactor's
   token `compactTok` (which the schedule queue hands from job to job, so one job runs at a time) at
   `none` between jobs; the job sets it to `some (rev, ⟨0, 0⟩)` in its first session and back to
   `none` in its last.
2. **The pinned `compactRes`** (proposed):
   `compactRes γ L m := ∃ sched fin n, metaCompact … ∗ fin's counter ∗ mwSlot γ ∗ cmpTrack γ L m ⟨fin, sched⟩`,
   `cmpTrack` (real compacting backend) `:= fkdOwn d.γB (recBytes fin, recBytes sched) ∗ ∃ X jc,
   dlsOwn d.γB X ∗ ghostVar γ.jc ½ jc ∗ ⌜∃ ents, entsCutAt L rc.crev ents ∧ (∀ k, physLookup m X k =
   (bucketOfEnts ents).lookup k) ∧ recsOk L rc ∧ recsPos rc ∧ ∀ c₁ p, jc = some (c₁, p) → jobPast L c₁
   p ents ∧ -1 ≤ c₁ ∧ c₁ ≤ rc.crev⌝`; `writerRes` names its bucket (`∃ L m, … bucketView ¼ m ∗
   bucketLog γ L m ∗ compactRes γ L m`). `mwInv` keeps the flag's half only (`kbMW := ∃ f,
   monoNatAuthOwn d.γB.fk ½ f`); a session holder assembles `bkMW` from the swap and `cmpTrack`.
3. **The generic `SetScheduledCompact`/`SetFinishedCompact` specs' swap** (`mwSwap W (∃ w X, MW w
   X)`) hands the whole lock resource `W` and takes it back right after the put, before the caller's
   record update: with the pinned `compactRes` the swap back cannot be proved (the new value is not the
   old record's). Their specs must lend only the values: e.g. `W ∗ £ 1 ={⊤}=∗ ∃ w X, MW w X ∗ (∀ w',
   MW w' X ={⊤}=∗ Wv w')` with the caller's update `Q ∗ Wv (fkPutV w schedKeyBytes (revBytes ⟨value,
   0⟩ false)) ={⊤}=∗ P ∗ W ∗ Post`. These are internal specs (not frozen).
4. **mvcc's build reaches etcdserver/txn** through `go_humanize.Bytes`'s spec importing
   `etcdserver.InvApplier`: while a client package is mid-migration the job's proof cannot be built.
   Its spec needs only `GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver` (the `Assumptions`
   class) and `GeneratedProof.github_com.dustin.go_humanize`; the import is not mvcc's to change.
5. Interfaces not regenerated (`etc/gen-interface.py` builds `Link`, red for the reason above):
   regenerate once the build is green.

**Left** (in order): (a) with findings 1-3 (`compactRes`/`writerRes`/`StoreNames.jc`; `NewStore`,
`restore`/`Restore` establishing the cut from `imageOk`'s `ents` with `X = ∅` (needs M3's exact
`fkCl`, below); the job re-establishing it per delete with `cutAt_del` and `jobPast`; `End` with
`cutOk_append`/`jobPast_append`; `updateCompactRev` with `cutOk_mono`), then (c), (d), (e) as in the
snapshot image's hand-off, then `snapObs_M1` replaced. M3: `mvccBackendFor` (keeping the image's
receipt), `mvccBackendFor_open.law`, and the backend's open giving the exact `fkdOwn γ (fkVals D) ∗
dlsOwn γ ∅` (`fkCl` redefined with exact values; `NewAlloc` already allocates them so: `fkVals D`,
`dlR P ∅`).

**Obligations added by the coordinator (txn's migration, 2026-11-05; `notes/mvcc-api-candidate.md`):**
`KV.Range`'s and `Txn.Range`'s proofs must give the read log's `LogWf'` and its revisions' size bound
(`MvccReachable`'s `LogWf` and the receipt; for a write transaction, the pending revision's deletes
of present keys), `Txn.Changes`'s `0 ≤ sint.Z chs.len` (the pending length, bounded by the writer's
receipt). (F) `Txn.DeleteRange`'s proof must give `LogWf' (σ.log ++ [pend ++ ds])` and its revisions'
size bound (the transaction's pending revision well formed: `ds` deletes only keys present after
`pend`, `delKeys`; its length bounded by the writer's receipt `⧖ (logCh ilog + pend.length)`).

## Hand-off: stage 2, the snapshot image's tracking in place (2026-11-05)

**Done** (`snapObs_M1` deleted; `#print axioms mvccImage_snapshot.law_holds` has no `sorryAx`; no
axiom; four new listed `M1-REPLACE` placeholders in the maintenance, below; no frozen statement
found false or too weak):
- **The pinned tracking (a)** (`InvStore`): `compactRes γ L` (the batch lock's log `L`) holds an
  eighth of the bucket's view at the logical view `m` and `cmpTrack γ L m rc` (`rc` the meta keys'
  record): for a compacting real backend mvcc's halves of `fkdOwn` (at `recBytes` of the record) and
  `dlsOwn X`, half of the records' compaction revision (`StoreNames.rcv`, physical: (c)), and
  `snap.cmpOk L m X rc jc` (`CutDefs`: the physical bucket the entries cut at `rc.crev`, with the
  witness; `recsOk`, `recsPos`; every recorded delete `KeyDel L rc.crev`; the last job's
  `jobPast` with `finRev ≤ jc.1 ≤ rc.crev`); nothing for any other backend. `writerRes` keeps an
  eighth of the view (`writerRes`'s quarter split with the compaction's part); a write
  transaction's part is `txQ` (the pin's quarter and `writerRes`'s eighth). `mwInv` keeps only the
  write right's flag (`kbMWf`); a session holder assembles `kbMWv w X` from it and the tracked
  values (`kbMWv_split`, `cmpTrack_split`, `cmpRest`).
- **(c)**: `slotY` carries the writer's half of `rcv` at its view's compaction revision (`rcvW`),
  so the frozen writer's slot gives `rc.crev = σ.crev`.
- **(d)**: `writerReg`'s third state, lent (`regLent`: a quarter of the right to register and a
  quarter of the frozen flag); `mvccBackend` records the registration's invariant (`∃ s,
  writerReg s γp`, its body only: no statement changes); `Api/SnapFreeze.lean`'s
  `writerInv_freezeR` (the registration opened with the writer's invariant: a pending one's
  writer's resource taken, the invariant left lent; lent already excluded by the unfrozen flag) and
  `reg_unlend`. `storeW_open` takes an excluder of the lent state (`LE`): a writer's the unfrozen
  flag (`writerReg_get`).
- **(e)**: `snapFrozen`'s open-transaction case holds the writer's key, stripped of the later; a
  registered lock resource's `writerRes` contradicts it.
- **The observation** (`snapObs`, `snapObs_writerRes`, `vd_of_cut`): the lock's resource is the
  registered store's writer's resource or (unregistered) the freezer's lent one; its tracked
  values, deleted entries and `rcv` agree with the lock's halves and the freezer's slot; the
  bucket's eighth with `viewAtD`'s quarter (`keyView`); so `snapObsOk`.
- **Maintenance proved**: `storeTxnWrite.End`'s commit re-pins the tracking at the new log and view
  (`Api/CmpTrack.lean`'s `cmpOk_append`, with `cutAt_append`, the explicit-witness form of
  `cutOk_append`; `cmpTrack_append`); `updateCompactRev`'s record update moved into
  `SetScheduledCompact`'s loan (`mwLend`, the spec's new form: the right lent at its values and
  taken back at the put's, `fkPutV`), re-pinning at the new record (`cmpOk_sched`,
  `compactLend_sched`); `cmpOk_fin` (the job's finished record keeps the compaction revision) and
  `cmpOk_crev` proved, not yet used.
- `mvccBackend_isBackend.law_holds` (the coordinator's law, `c1f1565c78`).

**Placeholders added** (`M1Placeholders.lean`, listed in its header):
- `regLent_excl_M1`: the compaction's openers of the registration (`updateCompactRev`'s loan, the
  job) exclude the lent state without the means. Fix: the job's premise `storeRegd` (from
  `updateCompactRev`, which registers), `updateCompactRev` with the compactor's share
  (`KV.Compact.contract`), the restore path by the restoring state.
- `rcvSched_M1`: the records' compaction revision moved to `rev` without the writer's half, with
  `1 ≤ rev`, `c ≤ rev`, `rev < |L|`. Fix: `KV.Compact.contract`'s update fired at the record write
  (inside `SetScheduledCompact`'s loan: `s.revMu` and `s.mu` held, the writer's state checked in,
  frozen excluded by the share), moving the client's, `s.revMu`'s and the writer's view with the
  writer's `rcv` half.
- `cmpTrack_new_M1`: `NewStore`'s and `store.Restore`'s new tracking from the `rcv` half only. Fix
  (M3): the backend's open giving `fkdOwn γ (fkVals D) ∗ dlsOwn γ ∅` (`fkCl`, `NewAlloc`), taken
  before `restore()` (whose `kbRecs` needs only the flag), the record allocated at the image's
  `rc` (today `(none, none)`, a latent mismatch with the backend's values), the cut from `imageOk`'s
  `ents` (`physLookup m ∅ = bucketOfEnts ents`).
- `cmpTrack_job_M1`: the job's session keeps the tracking (its deletes `X` to `X'`, its finished
  record). Fix, in this order: the compacting range's post exact on the physical view (`m'.lookup k
  = physLookup m X k` on the range, from `MW w X`; `BackendBridge`); the job's cursor ghost
  (`StoreNames.jc`, half in `cmpTrack`, half in `compactTok` with `jc.1 ≤ c`, so the next job knows
  `finRev ≤ c₁`); a persistent lower bound of `rc.crev` minted by `updateCompactRev` for the job
  (`c₁ ≤ rc.crev`); then per entry `cutAt_del`/`jobPast_skip`, and `cmpOk_fin` at the last batch.

**Left**: the four placeholders above (the job's first, then `NewStore`/`Restore` with M3); M3
(`mvccBackendFor`, `mvccBackendFor_open.law`, `fkCl` exact).

## Hand-off: stage 2, the job's tracking (2026-11-06)

**Done** (no axiom; `cmpTrack_job_M1` deleted; no frozen statement found false or too weak):
- **The compacting range exact on the physical bucket** (`batchTxSpecG`'s limited range, lent the
  right `MW w0 X0`, gives it back with `⌜∀ k, snap.physLookup m X0 k ≠ none → (m'.lookup k).isSome⌝`:
  every entry of the physical bucket is in the range's bucket). Proved in `BackendBridge`
  (`bt_rangeC`, from `batchLocked_bkMW`, the new `batchLocked_dlsW` and `key_phys_sub`: the session's
  `Key` bucket is the logical view but the recorded deletes, `dlsOk`). Stated one way only (the
  range's bucket holds the physical one, not equals it), so mvcc's assumed backend, whose `MW`
  ignores `X0`, can still meet it (a backend that never deletes physically).
- **The job's cursor** (`StoreNames.jc`/`PhysNames.jc`, `ghostVar (Int × Rev)`): half in `cmpTrack`
  (with `snap.cmpOk`'s `jc`), half the compactor's (`jobCur γ jc`, in `compactTok` with `jc.1 ≤ c`;
  the job's spec gives it back at its revision). **The records' compaction revision's lower bounds**
  (`StoreNames.rcl`, `monoNatAuthOwn` of `crevN` in `cmpTrack`/`cmpRest`): `updateCompactRev` mints
  `cmpLb γ rev` (with `1 ≤ rev`) at the record's write, out of `SetScheduledCompact`'s loan
  (`mwLend W MW f Q`: the loan's new output `Q`, returned by `SetScheduledCompact`'s spec), into
  `compactJobPre`. `NewStore` and `store.Restore` allocate both (the cursor at `(-1, ⟨0, 0⟩)`).
- **`Api/CmpJob.lean`**: pure, the cursor's order on keys (`rb_lt`, `rb_le`, `zeros_le`,
  `revSucc_lt`), `job_gap` (no physical entry between the cursor and the batch's `i`th entry, from the
  range's exactness and key order), `cmpOk_step` (one entry deleted, `cutAt_del`, or kept,
  `not_KeyDel_of_keep`), `cmpOk_start` (a job's first batch at cursor `⟨0, 0⟩`, from `cmpLb`);
  Iris, the session's tracking `sessTrk` (the cursor's ghost whole): `sess_open`, `sess_mono`,
  `sess_fin` (`cmpOk_fin`), `sess_close`.
- **`store.scheduleCompaction`** keeps the tracked compaction through every batch: per entry the
  cut and cursor move (`cmpOk_step`), the last batch's finished record (`sess_fin`), the cursor's
  halves split back at each `Unlock`.

- **The job's registration** (`regLent_excl_M1`'s first use gone): `compactJobPre` holds
  `storeRegd s γ`, minted with `cmpLb` in `updateCompactRev`'s loan (whose `storeW_open` registers);
  the job's `storeW_open` excludes a snapshot's loan with it (`storeRegd_regLent`).

**Placeholders left** (`M1Placeholders.lean`, three of the snapshot tracking's four):
- `regLent_excl_M1`: now only `compactLend_sched` (`updateCompactRev`'s loan). Fix (unchanged): the
  compactor's backend share in `updateCompactRev`'s premise (`KV.Compact.contract`), `storeW_open`'s
  exclusion generalized to an update opening `writerInv` (the freezer's frozen state holds the whole
  share, `shareTok 1`, so a share in hand and the lent flag's quarter contradict every state:
  `▷ False` is timeless), the restore's resumed compaction by its restoring state.
- `rcvSched_M1`: unchanged. Finding: it cannot be fixed apart from `slotX_step_M1`. The writer's slot
  `slotY` ties its `rcv` half to its view's compaction revision (`absPart γ.api ¼ L c ∗ … ∗ rcvW ½ c`),
  so moving `rcv` to `rev` at the record's write moves the writer's part of the API's compaction
  authority too: `KV.Compact.contract`'s update (the client's atomic update) must fire there, inside
  `SetScheduledCompact`'s loan, with `s.revMu`'s part (today `slotX_step_M1`, earlier, under
  `s.revMu`). `updateCompactRev`'s spec then carries the contract's update into the loan, and its
  compactor's share keeps a freeze out of the window between `s.revMu`'s section and the batch
  lock's (`snapObs` needs `rc.crev = σ.crev` at a freeze): the share is the key of both this and
  `regLent_excl_M1`'s fix.
- `cmpTrack_new_M1` (restated: from the halves of `rcv` and `jc` and the `rcl` authority; still the
  values' halves and the cut missing): M3, unchanged.

**Left**: the three placeholders above; M3 (`mvccBackendFor`, `mvccBackendFor_open.law`, `fkCl`
exact, `NewStore`/`Restore` from the image).

## Hand-off: stage 2, `KV.Compact.contract` (2026-11-06)

**Done** (no axiom; `rcvSched_M1` and `regLent_excl_M1` deleted, `slotX_step_M1`'s Compact uses gone;
one new listed placeholder, `hookNilRO_M1`; no frozen statement found false or too weak):
- **The compaction's ghost step** (`LockArm.lean`'s `cmpCb γ c cp rev Fok Fce Ffr`): what
  `updateCompactRev` fires at its three outcomes: success (inside `SetScheduledCompact`'s loan, mask
  `⊤ ∖ writerN`): `s.revMu`'s slot and the writer's quarter of the view with its part of the pending
  revision, at the committed log, moved to `rev`; `ErrCompacted`/`ErrFutureRev` (under `s.revMu`):
  the lock's slot read. Its excluder `S` (lent, given back) with `slotF γ ∗ S ⊢ False` and
  `ghostVar γ.wr 1 () ∗ slotFr γ ∗ S ⊢ False` (the frozen and restoring states).
- **`mwLend` one-shot** (no `□`): `compactLend_sched` (`Api/CmpSteps.lean`) opens the writer's
  invariant inside the loan, finds the writer's state checked in (the open writer by the lock's key,
  the frozen/restoring states by `S`), so the frozen flag down (`slotFl γ 1 false`) is `storeW_open`'s
  `LE` (`slotFl_regLent`: that is how the hand-off's "share in hand and the lent flag's quarter
  contradict" landed, no change to `storeW_open`); the writer's slot agrees with `s.revMu`'s (`wv`,
  `absPart`) and its `rcv` half with the records' (`cmpRest_sched`, now with the writer's half: no
  placeholder); `cmpCb` fired there; the writer's state put back at the moved view.
- **`updateCompactRev.spec`**: `S`, `cmpCb`, `1 ≤ rev`, the commit request `X ∗ storeReq γ X Y`
  (`ForceCommit`'s; the success gives `Y`, the errors `X`), an `ErrFutureRev` arm (no certificate
  premise; the success's `crevSafe` from the committed log's). `lockCtxM`/`lockBackM` over `hookOk`
  (no writer's fragment), the unset arm's update `P ∗ Pre ={⊤}=∗ P ∗ Post` (`lockArmS` likewise,
  `SetScheduledCompact`'s proof adapted); `hookP_agree_lc2`.
- **`compactLockfree.spec`**: `restore()`'s resume only, at `c = rev` (`cmpCb_refl`), excluder `s.mu`'s
  deposit ghost (`wr_restoring_excl`; the frozen state by `slotF_excl_M1`, `wr_frozen_excl`, whose
  M1-REPLACE now also names `KV.Restore.contract`); success only. `store.Restore` passes `Hwr` and
  the records' `recsPos` (`1 ≤ rev`).
- **`Api/CmpCb.lean`**: `store.Compact.core` (the internal statement), `compact_cmpCb` (the client's AU
  is the ghost step: three quarters of the view and of the compaction authority, `MvccReachable.compact`
  from the writer's `pndPart` at `none`), `compactChan_ok`, `store.Compact.wp_api` (the contract from the
  core), `watchableStore.Compact.wp_proof` (the promoted method, the inner store's contract).
- **`mvcc.store.Compact.spec` is `KV.Compact.contract` at `*store`** (`store__Compact.lean` proves the
  core as a `have`, then `wp_api`); `mvcc.watchableStore.Compact.wp_proof` gives the canonical
  `api.watchableStore.Compact.spec` from it (not linked: no Go function of its own).
- **The API's bodies** (`Spec/.../Api.lean`, statements unchanged): `mvccOpen` defined (`@[no_expose]`:
  the store's location `locIs`, the restorable compaction right at the current names, the right's
  quarter of the compaction authority, the compactor's reader token and supply); `isMvccPlain`/
  `isMvccWatchable` record the (inner) store's location and the permit `True`; `mvccBackend` records
  `hookP` of `Pk` at the current names. `Api/Ghost.lean`: `AbsNames.loc`, `locIs`, `locIs_agree`,
  `absNames_alloc(_store)` allocate it (`NewStore` at its store).

**Placeholder added** (`M1Placeholders.lean`): `hookNilRO_M1` (`plHookRO γB nil ⊢ plHook γB nil`):
`KV.Compact.contract`'s nil-hook arm, until §4.8 (`lockNilSpec` at any share of the hook at `nil`).

**Left**:
- `cmpTrack_new_M1` and M3 (the backend's exact open, `mvccBackendFor`, `mvccBackendFor_open.law`,
  `NewStore`/`Restore` from the image), unchanged since the last hand-off; `New.spec`/`NewStore.spec`
  must now produce `mvccOpen` (with the compaction right, the reader token and supply from
  `mvccBackendFor`), `isMvcc`'s `locIs` and permit `True` (`NewStore`'s `Perm := True`).
- `excl.law`'s `mvccOpen` conjunct: two open tokens have one location and names, so two
  `compactRightR`s at them (their scheduler's stop token is exclusive).
- `KV.Restore.contract`/`KV.Close.contract`: `mvccOpen`'s body has only the compaction's pieces (§2's
  closer and restore pieces to add); the restore's resume needs the restorer's share for
  `slotF_excl_M1`.
- §4.8: `hookNilRO_M1`.
- The TCB baseline (`etc/tcb-baseline.txt`, not mine): two `sorry`s fewer (`rcvSched_M1`,
  `regLent_excl_M1`), one more (`hookNilRO_M1`).

## Hand-off: stage 2, §4.8 and M3 (2026-11-06)

**§4.8, a store without a hook** (`hookNilRO_M1` deleted; no axiom; no frozen statement changed):
`batchTxSpecG`'s nil-hook clause is now at **any share** of the hook at `nil`: its `HN` is a family
`DFrac → IProp` (default `fun _ => False`) and the clause `□ ∀ dq, lockNilSpec … (HN dq) …`;
the store's is `kbHookNilAt γ.kb` (`InvStore`: the real backend's `plHookAt d.γB dq nil`,
`kbHookNilAt_half : kbHookNilAt kb ½ = kbHookNil kb`), proved by `bt_lockInNil` at any `dq` (the
backend's `LockInsideApply` spec already takes any share). `lockCtxM`/`lockBackM` take the share
(`dq`, default ½; their `_some`/`_none`/`_pre` lemmas take it explicitly); `updateCompactRev.spec`
and `store.Compact.core` quantify it; `KV.Compact.contract`'s nil arm lends the hook frozen at `nil`
(`DFrac.discard`, the API's `hookIs B nil`). `bkHookIs`'s `≠ nil` is kept (not needed: the nil arm
goes through `lockNilSpec`, not the hook arm; dropping it would break the server's
`SnapApplyOptsLemmas.snap_hookOk`). `KV.Write.contract`'s nil arm (when it is proved) uses the
same clause.

**Layout**: `WatchParams.mk.congr_simp` realized once in `InvWatchStream`
(`WatchParams.mk_congr_simp_realized`; `#check` does not keep it): `--check --layout` reports 0 new
(and 5 fixed, for the coordinator to drop from the baseline).

**Internal definitions changed that modules outside mvcc import**: `batchTxSpecG`, `isBatchTxG`,
`isKeyBackendG`, `isKeyBackendGR` (the `HN` parameter's type), `lockCtxM`, `lockBackM` (a trailing
`dq`), `store.updateCompactRev.spec`, `store.Compact.core` (`dq`). No module outside mvcc names
them (checked with `etc/importers.py --uses`).

## Hand-off: stage 2, M3 begun and a finding on `mvccBackendFor_open.law` (2026-11-06)

**Done** (no axiom, no new placeholder):
- **`excl.law` proved** (`Api/WatchLaws.lean`: `mvccOpen_excl`, `excl.law_holds`): two open tokens'
  restorable compaction rights each hold an eighth of the fields at the current objects and names
  (`fieldShareAt_cur`, `curAt_agree`), so their physical names agree, and with them the scheduler,
  whose stop token is exclusive (`mono_list_idx_agree` on `schedStopName`, then `dghostVar` at 1+1).
- **`NewStore`'s tracked compaction from the open** (`cmpTrack_new_M1`'s `NewStore` use gone):
  `mvcc.NewStore.spec`, `mvcc.newWatchableStore.spec` and `mvcc.New.spec` take
  `kbVals kb (none, none) ∅` (the open's halves of the compaction keys' values and of the deleted
  entries, `fkCl`'s over fresh data: `fkVals D = (none, none)` when `D` has no compaction key);
  `NewStore.lean`'s `cmpOk_fresh` (the cut at `[[], []]`, nothing anywhere) and `cmpTrack_fresh`.
  `StoreBackend.NewStore_backend` and `Results.lean`'s two linked forms take
  `fkdOwn d.γB (none, none) ∗ dlsOwn d.γB ∅`. Interfaces regenerated.

**Breaks outside mvcc** (not fixed, the server's track): the callers of `mvcc.New.spec`
(`etcdserver.BuildLemmas`, `etcdserver.M2StorageDraft`, `etcdserver.NewServer`: pass `fkCl`'s
`fkdOwn`/`dlsOwn` at the fresh data's values) and of `mvcc_NewStore_backend` (`etcdserver.Results`).
These are to move onto the API's `New.spec` anyway.

**Finding: `mvccBackendFor_open.law` is too weak (stopped M3 there).** It quantifies over every
`P : backend.BParams`, but the store over a real backend needs `P` to be a real instance's
parameters (`KBReal.P d`: `Key` the one safe-range bucket, the hook's buckets and keys, the rest
buckets tracked, `FV := metaRevVal`) with `Key` and `Meta` in its table (`bridgeParams`): the
bridge (`storeBackend_of_backendC`) takes `bridgeParams d.P`, and `mvccBackend`'s body pins
`B = ⟨d.γB, d.P, d.be⟩` for a `d : KBReal`. Nothing among the law's premises (`newPostKP`,
`isBackend`'s `P.Wf`, `keySized`, `mvccImage`) says anything of `P`'s shape, so `mvccBackendFor`
cannot carry it, and `New.spec`/`NewStore.spec`/`KV.Restore.contract` (which take only
`mvccBackendFor B Pk …`) cannot produce `mvccBackend γ 1 B Pk` at a `B` whose `P` is not of that form.
**Minimal fix**: a premise `⌜mvccParams P⌝` on `mvccBackendFor_open.law`, with the vocabulary
`mvccParams P := ∃ d : KBReal, d.P = P ∧ bridgeParams P` (or its unfolded form over `BT`, `hookMax`,
`limit`); the server's mirrors (`KVStoreApi`'s `dbImageA_open.law`, `bootBackend.law`) take it too,
and the server has it (`InvBoot`'s and `SnapRO`'s `p.kb = some d ∧ bridgeParams d.P`).

**Left** (in order, after the fix above is decided):
- `mvccBackendFor`'s body (then the law: mostly `newPostKP`'s split into the store's part and
  `backendRest`): `isBackend` at `lateW gx`, `keySized`, `⌜mvccParams P⌝`, the image (`mvccImage D L c
  u`), `bViewC`, `dlInit`, `fkCl`, `srSlot`, `rdStock` with the `rdStockN` open shares (`bkRTx`),
  `lateReg gx`, the two write-back tokens and the supply. At `mvccStart` it gives `NewStore_backend`'s
  premises (the `Key` bucket empty and no compaction key from `imageOk D [] (-1) false`).
- `New.spec`/`NewStore.spec` over it: `NewStore` must return the API's client parts it drops today
  (`absNames_alloc_store`'s `-`: `mvccStateI`, `shareTok 1`, the compaction authority's quarter),
  `Perm := fun _ => True`, `mvccLeases` defined (`opaque` today: `@[no_expose] def … := γ.leases`),
  `mvccOpen` from `compactRightR_of_closer` with a reader token kept back (`storeRT`) and the supply
  (`kbWTSupplyM`); `wsSlot_make_M1` (`New`'s).
- `cmpTrack_new_M1`: only `store.Restore`'s use left; it also tracks `⟨none, none⟩` records though the
  image may hold records (the restore's records from the image's `rc`, and the cut from `imageOk`'s
  `ents`). Its docstring in `M1Placeholders.lean` still names `NewStore` (not edited: 314 importers).
- `KV.Restore.contract`/`KV.Close.contract` (unchanged since the last hand-off).
- The TCB baseline: no axiom or `sorry` added or removed (`cmpTrack_new_M1` still used).

## Design: mvcc's API over its storage abstraction (2026-11-06; approved by the user, 2026-11-06)

The decision (`notes/decisions.md`, "mvcc's API over its storage abstraction, not etcd's backend"):
`Api.lean`/`ApiState.lean` stop naming etcd's backend; mvcc's storage contract is the API's
abstraction of storage, and etcd's backend is one implementation of it, adapted by the bridge.

**Survey: what the API names of the concrete backend** (`Api.lean`, `ApiState.lean`):
1. `BkRef` (`ApiState`): `backend.BNames`, `backend.BParams`, the location; every contract's `B`.
2. The Go value passed to `New`, `NewStore`, `Restore`: `interface.mkOk (*backend.backend) #B.b`.
3. `mvccBackend`'s body (sealed, fine) and `mvccBackend_isBackend.law` (`backend.isBackend … (mvccW gx)`).
4. `mvccW`, `mvccWReg`, `mvccW_alloc.law`: the `W` of etcd's backend constructor.
5. `mvccBackendFor` (sealed) and `mvccBackendFor_open.law` (`backend.newPostKP`, `wbTok`, `bOpen`,
   `rdOpen`, `rdStockN`, `keySized`).
6. `backendRest`, `backendRest_open.law` (`isStopChans`, `plHook`, `rbOwn`, `rdPool`).
7. `hookIs B f := backend.plHookRO B.γB f`; `KV.Restore.contract`'s `backend.plHookAt B'.γB dq f`.
8. `backend.commitReq B.γB B.P Pk B.b X Y` in `KV.Compact`, `KV.Commit`, `KV.Restore`.
9. `KV.Restore.contract`'s give-back `[∗list] rdStockN, backend.bOpen B.γB rdOpen`.
10. `threadBound GF ≤ backend.rdStockN` (`New.spec`, `NewStore.spec`).
11. `mvccImage (D : backend.Data)`, `mvccImage_fresh.law` (`backend.dget`), `mvccImage_snapshot.law`
    (`backend.backend.Snapshot.spec`, `snapOpen`, `hkOwn`, `rbOwn`, `hkData`, `rbData`, `wbTok`).
12. `mvccTxn_leaseDelete.law` (`backend.bF "batchTx"`, `rbPart`, `batchTxBuffered.UnsafeDelete`).
13. Imports: `backend.RdPool`, `backend__Snapshot`.

**The restated API** (`Api.lean`, no `backend.` name left):
- `MvccStorage : Type` (opaque, replaces `BkRef`): a storage implementation; `storageVal S :
  GoInterface` the Go value the constructors and `Restore` take (item 2).
- `mvccBackend γ q S Pk` (as today, over `S`); `mvccBackend_agree.law` over `S`.
- `storageHook S dq f` (fractional in `dq`, sealed): the storage's post-lock hook; `hookIs S f :=
  storageHook S DFrac.discard f` (item 7). `storageReq S Pk X Y` (sealed): a commit request on it,
  `X` to `Y` (item 8, the contract's `Req`). `storageRest S` (sealed): what `Restore` gives back of
  the old storage (item 9).
- `mvccReaderN : Nat` (an API constant, today's value of `rdStockN`): `threadBound GF ≤ mvccReaderN`
  (item 10).
- `mvccStorageFor S Pk L c u` (sealed, replaces `mvccBackendFor`): `S` meets mvcc's storage contract
  at batch-lock invariant `Pk` (what `storeBackendT_of_backendC` and `keyCleanRead_of_backend` give:
  `isKeyBackendG` with the compaction's clauses and the clean read, at every store's names over `S`)
  and holds the history `L` compacted at `c` (unfinished iff `u`), with the receipt `⧖ (logCh L)`,
  the store's write tokens and supply, `mvccReaderN` reader tokens, the registration of the store's
  write resource. `New`/`NewStore` take it at `mvccStart`, `Restore` at `σ'`.
- Gone from `Api.lean`: items 3 (`isBackend` half), 4, 5, 6, 11, 12, the two imports. The
  open law has no counterpart in the API: making a storage is the implementation's business.

**The bridge module** (new, importable, inside mvcc's tree because it unfolds the sealed
predicates: `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/EtcdBackend.lean`, over `BackendBridge`;
"mvcc over etcd's backend", what the server imports, never `Api.lean`'s clients that do not choose
etcd's backend):
- `etcdStorage (d : KBReal) : MvccStorage` with `storageVal (etcdStorage d) = interface.mkOk
  (*backend.backend) #d.be`, and laws: `storageHook (etcdStorage d) dq f ⊣⊢ plHookAt d.γB dq f`,
  `storageReq … ⊣⊢ backend.commitReq …`, `storageRest (etcdStorage d) ⊣⊢ [∗list] rdStockN, bOpen d.γB
  rdOpen`, `mvccReaderN = backend.rdStockN`, `mvccBackend γ q (etcdStorage d) Pk ⊢ □ isBackend …` (item 3).
- `mvccW`/`mvccWReg`/`mvccW_alloc.law` (item 4), `backendRest`/`backendRest_open.law` (item 6),
  `mvccImage`/`mvccImage_fresh.law` (item 11), `mvccTxn_leaseDelete.law` (item 12) move here
  unchanged but for `B := etcdStorage d`.
- **The open law** (item 5), with the premise the store needs: `⌜bridgeParams P⌝` and `P = d.P` for a
  real instance `d` in compaction mode (`d.cm`), at `W := mvccW d.gx`: `mvccImage D L c u ∗ newPostKP …
  ∗ … ={⊤}=∗ mvccStorageFor (etcdStorage d) (Pk d.γB) L c u ∗ backendRest …`. Proved by the bridge
  (`storeBackendT_of_backendC`, `keyCleanRead_of_backend`, `fkCl`'s exact values for the tracked
  compaction). The server discharges `bridgeParams d.P` from what it holds (`InvBoot`, `SnapRO`).

**The snapshot** (`mvccImage_snapshot.law`): it stays a fact of etcd's backend, in the bridge
module, not an operation of the storage contract. Why: mvcc's code never takes a snapshot (the
server calls `s.be.Snapshot()` on its concrete backend, `createMergedSnapshotMessage`); a contract
operation would make every storage provide one that mvcc does not use and put the backend's data
type (`backend.Data`, the image's carrier) into mvcc's API. The law needs mvcc's internals (the
frozen store, the tracked compaction), which the bridge module may unfold, being in mvcc's package;
its statement is over `mvccState`, `mvccBackend γ 1 (etcdStorage d) Pk` and `backend.Snapshot`, the
server's terms. Likewise the image `mvccImage` is a relation between bbolt's data and a history: a
fact of etcd's storage format, so the bridge's.

**The internals** (two phases): (A) `MvccStorage := KBReal` (sealed; `etcdStorage := id`), the
store's names keeping `kb : Option KBReal`: the API is stated over the abstraction now, and the
bridge's premise `bridgeParams` is where it belongs; mvcc works over etcd's backend only, but no
statement changes when (B) the store's instance becomes a record of the contract's predicates
(`View`, `RT`, `WT`, `Del`, `Req`, `HF`, the compaction's, today `storeBackend`'s arguments through
`kb`), `MvccStorage` that record with its Go value, and `mvccStorageFor` gets an introduction law
in the contract's own terms (for an implementation other than etcd's). (B) touches every module
reading `γ.kb` (`InvStore`'s 3986 importers): later, not on the M3 path.

**Clients affected** (statements, when the API is restated): every client naming `BkRef`'s fields
or the moved laws: the server (`KVStoreApi`'s `dbImageA_open.law`, `bootBackend.law`, the
snapshot's send and receive, `lessor.Revoke`'s lease delete, the boot) imports the bridge module;
`examples/mvccrand` (its backend boot: `backendRest_open`, `mvccW_alloc`). `B.γB`/`B.b` uses become
`d.γB`/`d.be` at `B := etcdStorage d`.

## Hand-off: stage 2, the API over its storage abstraction (phase A) and M3's open (2026-11-06)

**Done** (no axiom; no placeholder added or removed):
- **Phase A of the design above** (approved by the user, 2026-11-06): `Api.lean`/`ApiState.lean` name
  no backend. `BkRef` is gone; the vocabulary is `MvccStorage` (sealed, `:= KBReal`), `storageVal`,
  `storageHook` (fractional), `hookIs := storageHook · DFrac.discard`, `storageReq`, `storageRest`,
  `mvccReaderN`, `mvccStorageFor` (in place of `mvccBackendFor`); `persistent.law`'s image conjunct is
  replaced by `hookIs`'s and `storageReq`'s persistence (instances in `Api.lean`). The bridge module
  `Spec/.../mvcc/EtcdBackend.lean` (listed importable in `etc/api/mvcc.txt`): `etcdStorage bk`, its
  equations (`etcdStorage_val/_hook/_hookIs/_req/_rest`, `mvccReaderN_eq`, `etcdStorage_inj`),
  `mvccW`, `mvccWReg`, `mvccImage` (+ `mvccImage_persistent`), `backendRest`, and the laws
  `mvccW_alloc`, `mvccBackend_isBackend` (now at `etcdStorage bk`, `mvccW bk.gx`),
  `backendRest_open`, `etcdStorage_open` (in place of `mvccBackendFor_open`: at a real instance `bk`
  with `bridgeParams bk.P` and `bk.cm`), `mvccImage_fresh`, `mvccTxn_leaseDelete`,
  `mvccImage_snapshot` (all at `etcdStorage bk`). Proofs adapted (`SnapLaws`, `SnapFreeze`, `CmpCb`).
- **`mvccStorageFor` defined** (phase A body: the store's part of `newPostKP` at the image's data, the
  image's receipt and facts, `bridgeParams`, compaction mode, `keySized`, the registration, the payment
  rights) and **`etcdStorage_open.law` proved** (`Api/StorageOpen.lean`).
- `excl.law` (earlier this day).

**Reverted** (`2e310b1b99`): the `kbVals kb (none, none) ∅` premise on `NewStore`/`newWatchableStore`/
`New` (`678a84c392`). It was vacuous for a real backend: `fkCl` gives one client half of
`fkdOwn`/`dlsOwn`, which `kbNoCmp` (`bkNoCmp = fkOwn 0`) already holds. `cmpTrack_new_M1` is back at
`NewStore`. The fix: pin the values in the no-compaction token `restore` threads (`NC`): a
`kbNoCmp` at known values (`fkOwn` with `fkdOwn (none, none)`, `dlsOwn ∅`), or `restore` giving its
`NC` back as it took it, so that `NewStore` reads the values out after `restore`.

**Breaks outside mvcc** (not fixed; `etc/importers.py --uses` of `BkRef`, `mvccBackendFor`,
`mvccImage`, `backendRest`, `mvccW`, `hookIs`, the moved laws): the server (`etcdserver.InvApplier`,
`InvApplyAll`, `KVStoreApi`, `Results`, `SnapRO`, `StoreLatest`, `apply.{AuthDerive,Chain,Contracts,
WriteLemmas}`, `txn.{ApiVocab,Results}` and the txn specs `Spec/.../etcdserver/txn/*`,
`EtcdServer__applyConfChange`), the lessor (`lease.MvccShapes`, `lessor__Revoke` spec and proof),
`examples/mvccrand` (`TxnEnd`, `Writer`, `WriterLease`, `reader`, `writer__txn`, the writer specs) and
the drafts under `notes/`. The rewrite: `B : BkRef` → `B : MvccStorage` (`etcdStorage d` where the
client chose etcd's backend), `B.γB`/`B.b` → `d.γB`/`d.be` through the bridge's equations, import
`EtcdBackend` for the moved names, `mvccBackendFor_open` → `etcdStorage_open` (with
`bridgeParams d.P`, which the server holds).

**Left** (in order):
1. `NewStore`'s values through `restore` (above), then `New.spec`/`NewStore.spec` over
   `mvccStorageFor`: from its body at `mvccStart` the internal premises (`bkView ∅` from `bViewC` and
   `imageOk`, `bkNoCmp` from `fkCl`, `bkRTx` from `rdStock` and the `bOpen` shares, `kbSRM` from
   `srSlot`, the bridge `storeBackend_of_backendC`); `NewStore` must return the API's client parts it
   drops (`absNames_alloc_store`'s `-`), `Perm := True`, `mvccLeases` defined (opaque today),
   `mvccOpen` (`compactRightR_of_closer`, a reader token, the supply); `wsSlot_make_M1`.
2. `store.Restore`'s `cmpTrack_new_M1` (the image's records and cut), `KV.Restore`/`KV.Close`.
3. Phase B (the store's instance a record of the contract's predicates; `mvccStorageFor`'s
   introduction law in the contract's terms).
- TCB: no axiom or `sorry` added or removed.

## Hand-off: M3, `NewStore`'s values through `restore` (2026-11-06; done, see the next section)

**Done**: the backend's flag alone, `backend.fkFlag γ n` (the client's half of the compaction-key flag,
without `fkOwn`'s values' halves), `fkOwn_flag`, and its read laws `fkRd_absF`, `fkRd_openF`
(`ReadLemmas`): additions only, no statement changed.

**The design (next)**: the values' halves must reach the batch lock's `cmpTrack` at `NewStore`'s first
`Unlock`, *before* `restore()`, which today takes the no-compaction token `NC = kbNoCmp`
(`bkNoCmp = fkOwn 0`, values inside). `restore()` reads the compaction keys with the flag only
(`fkRd_abs`/`fkRd_open` use nothing else), so:
1. `bkNoCmp γB` exact: `fkFlag γB 0 ∗ fkdOwn γB (none, none) ∗ dlsOwn γB ∅` (`bkNoCmp_of_fkCl` from
   `fkCl_exact`; `NewStore`'s premise `kbNoCmp` unchanged in name, so the server's boot,
   `bootBackend_of_newPost`, `BuildLemmas`, is unchanged).
2. The contract's and `restore`'s token flag-only: `bkNoCmpF γB := fkFlag γB 0`, `kbNoCmpF`;
   `storeBackend`/`storeBackendT`/`keyCleanRead`'s `NC`, `RestoreNC`'s `specNC`, the bridge's read
   clauses (`BackendBridge` 757-1681, 2771-2819, 3357, 3540, 3753, 3843) at `bkNoCmpF`; `bkRecs`/`kbRecs`
   (the records' token, also an `NC`) flag-only: empty `kbNoCmpF`, else `∃ n, fkFlag n ∗ fkOpen …`;
   `restoreImageM`'s on-arm gains the values `kbVals (some d') (recBytes r.fin, recBytes r.sched) ∅`
   (from `fkCl_exact` in `restoreImageM_of_openOn`).
3. `NewStore`: `kbNoCmp` split into `kbNoCmpF` (to `restore`) and the values (to `cmpTrack` when
   compacting: `cmpOk [[], []] ∅ ∅ CmpRecs.empty (-1, ⟨0, 0⟩)`, `logEnts_init`), reassembled for the
   writer's loan when not compacting; `cmpTrack_new_M1`'s `NewStore` use gone. `store.Restore` likewise
   from `restoreImageM`'s values, with its record allocated at `r` (not `(none, none)`) and the cursor
   at `(r.finRev, ⟨0, 0⟩)`.
Outside mvcc only `SnapRestoreM`'s proof (`kbRecs_empty`, `keyCleanReadR_empty`, `kbRecs_some` chain)
may need its rewrites re-checked; no statement outside mvcc changes.

**Left after it**: `New.spec`/`NewStore.spec` over `mvccStorageFor` (the previous hand-off's item 1),
`store.Restore`'s tracking, `KV.Restore`/`KV.Close`, phase B.

## Hand-off: M3, `NewStore`'s tracked compaction proved (2026-11-06)

**Done** (no axiom; `cmpTrack_new_M1`'s `NewStore` use gone, its `store.Restore` use left; no frozen
statement changed): the design of the previous section, as written.
- `bkNoCmp γB` exact (`fkFlag γB 0 ∗ fkdOwn γB (none, none) ∗ dlsOwn γB ∅`; `bkNoCmp_of_fkCl`,
  `bkNoCmp_fkV_of_fkCl` from `fkCl`'s exact body, `fkVals_of_noCmp`); `bkNoCmpF`/`kbNoCmpF` (the flag
  alone), `kbNoCmp_split` (`kbNoCmp ⊣⊢ kbNoCmpF ∗ kbVals kb (none, none) ∅`), `kbNoCmpF_MWf`,
  `kbNoCmpF_some`.
- The `NC` of `storeBackend`, `storeBackendT`, `restoreView`'s `keyCleanRead`, `RestoreNC`'s
  specs, `RestoreOff`'s, `RestoreMoves.restoreView_of`, `RestoreRecs`' `restoreViewR` and the bridge's
  read clauses (`BackendBridge`, `Results.mvcc_backend_bridge`) is `bkNoCmpF`/`kbNoCmpF`; `bkRecs`/`kbRecs`
  are flag-only (`kbRecs_empty : … = kbNoCmpF …`; `kbRecs_MW` → `kbRecs_MWf`, into `mwInv`'s flag).
- `restoreImageM`'s on-arm: `(kbRecs … r ∗ kbVals (some d') (recBytes r.fin, recBytes r.sched) ∅)`, grouped
  so that `etcdserver/SnapRestoreM.restoreImageM_fkV`'s pattern is unchanged (`restoreImageM_on`,
  `restoreImageM_of_openOn` from `fkCl`'s exact body). `store.Restore` binds the values (`Hvals`, unused
  until its tracking) and, off, splits the token for `restore` and rejoins it for the writer's loan.
- `NewStore`: `kbNoCmp` split at the start; `cmpTrack_fresh` (with `cmpOk_fresh`) makes the tracked
  compaction from the values when compacting and gives them back (`⌜¬ kbCmpM⌝ -∗ kbVals …`) for the
  writer's loan otherwise; `restore` takes the flag; `kbNoCmpF_MWf` for `mwInv`.

**Statements changed outside mvcc's own uses** (none in other packages): `kbRecs_empty`'s right side
(`kbNoCmpF`), `keyCleanRead_of_backend`'s and the bridge lemmas' `NC` (`bkNoCmpF`), `kbRecs_MW` renamed
`kbRecs_MWf` (flag part), `restoreImageM`'s body. `SnapRestoreM` uses the first two and the body through
`restoreImageM_fkV`; its rewrite chain is consistent with them, **but it could not be built**: its
imports (`SnapApplyDefs` → `SnapApply`, `InvWatchBuilt`, `InvServe`) fail on the server's own pending
migration (`apply.AEnv.s`, `MvccName.kb`, `txn.isKV`), not on these changes. `mvcc.Results` likewise
waits on them.

**Left**: `New.spec`/`NewStore.spec` over `mvccStorageFor` (internal `NewStore` to return the API's
client parts, `absNames_alloc_store`'s; `mvccLeases` defined; `mvccOpen`'s reader token by
`storeReader_retire`; `Perm := True`); `store.Restore`'s tracking (`Hvals`, the record at `r`, the cursor
at `(r.finRev, ⟨0, 0⟩)`), `KV.Restore`/`KV.Close`; phase B.

## Hand-off: M3, `NewStore.spec` over `mvccStorageFor` (2026-11-06)

**Done** (no axiom; one new listed placeholder, `mvccDeleter_M1`; no frozen statement changed):
- `Api/NewStoreApi.lean`: `api.NewStore.wp_proof` (the API's `NewStore.spec`, from the internal
  `mvcc.NewStore.spec` and the bridge's 26 backend specs; not linked: `Link.lean` is generated).
  `mvccStorageFor` at `mvccStart` gives the internal premises (`imageOk_start`: an empty `Key` bucket,
  no records, so `bkNoCmp_fkV_of_fkCl`; `storeBackend_of_backendC` over the registration fixed at fresh
  index names; the view from `bViewC`; the reader tokens, `bkRTx_of_rdToks`; the slot, the tokens,
  the registration); the post: `isMvcc` (`isMvccPlain`, `Perm := True`), `mvccState γ mvccStart` (the
  client's parts), `mvccOpen` (`compactRightR_of_closer`, the right's quarter, a reader retired from
  the pool with the internal spec's new credit, `storeReader_retire`, the supply), `mvccBackend γ 1`
  (the share token, the writer's fragment, the registration, `hookP` from `hookInit`).
- The internal `mvcc.NewStore.spec`'s post gains, at its end, `writerReg s γ`, the client's parts
  `∃ pr, ⌜pndW γ + pr = 1⌝ ∗ api.newClient γ.api [[], []] (-1) pr s` (`Api/Ghost.lean`, the
  `absNames_alloc_store` parts it dropped) and `£ 1` (`wp_auto_lc 1` at its first steps). Its
  callers' patterns end in `-` (`newWatchableStore`, `NewStore_backend`; the server's `New.spec`
  callers see the internal `New.spec`, unchanged).
- `mvccLeases` defined (`(γ : StoreNames).leases`; was opaque).

**Placeholder added**: `mvccDeleter_M1 : ⊢ mvccDeleter rd γ` (`Api/NewStoreApi.lean`, listed in
`M1Placeholders.lean`'s header): the range deleter is the store's `Write`, so its contract is
`KV.Write.contract`'s (M1-REPLACE: `KV.Write.contract`, with `mvccTxn` defined; still opaque `True`).

**Left**: `New.spec` (the watchable store: the internal `New.spec`'s post with the client's parts and
the watch layer's, `wsSlot_make_M1`); `store.Restore`'s tracking, `KV.Restore`/`KV.Close`;
`KV.Write.contract` (then `mvccDeleter_M1` goes); phase B.

## Hand-off: M4, track B, the write path's commit steps (2026-11-06)

**Done** (no axiom; placeholders removed, none added; no frozen statement changed):
- `Api/TxnSteps.lean` (new): the internal `End`s take the moves of the API's slots as their
  caller's ghost steps, fired where §3 puts them, and the frozen state's excluder as the caller's
  `G` (`□ (slotF γ ∗ G -∗ False)`, given back; the API's `G` is the backend share,
  `slotF_share_excl`). `endCb γ ilog pend crev Y R`: with no change, at the check-in, the
  transaction's writer slot `Y` back to `slotY γ ilog` (given `idxCert γ.idx ilog`); with a change, at
  the bump under `s.revMu` (given the committed log's certificate), `slotX γ 1 ilog crev ∗ Y` to both
  slots at `ilog ++ [pend]` (the lock's compaction revision is the transaction's: `muHeld_crevUB`).
  `wsEndCb γ ilog pend crev R` (the watchable `End`): with a change, at its notification under its
  `s.mu` (given the sealed log), `slotY ∗ wsSlot γ 1 ilog` to the API's `nlLb (ilog ++ [pend])` (what
  the notify's sends carry) and some `Y` with the commit's `endCb` from it, giving
  `wsSlot γ 1 (ilog ++ [pend]) ∗ R`; with none, `endCb`. `storeTxnWriteCoreY`/`isTxnWriteCoreY`/
  `isTxnEndY`: the cores with the writer's slot any `Y` (between the watchable notification and the
  commit the writer's part of the pending revision is at `some pend`, so it is not `slotY`);
  `txnEndX`/`txnEndXPost` (`metricsTxnWrite.End`'s extra pre/post, `True` for a read transaction).
- **Statements changed** (all in mvcc; none used outside mvcc but through the linked results and
  the `specR` corollaries): `storeTxnWrite.End.spec` (core at `Y`, `G`, `endCb`; post `G ∗ R`),
  `metricsTxnWrite.End.spec` (`isTxnEndY`, `txnEndX`; post `txnEndXPost`), `watchableStoreTxnWrite.End.spec`
  (`G`, `wsEndCb`; post `G ∗ R`), `writeView.Put.spec`/`DeleteRange.spec` (`G`, and the commit's step
  `∀ ilog crev, endCb γ ilog pend crev (slotY γ ilog) R` at the pending changes they make; post
  `G ∗ R`), `ReaderSpecs`' `storeTxnWrite.End.specR` and `metricsTxnWrite.End.specR` (likewise); the
  read callers of `metricsTxnWrite.End` (`readView.{Rev,Range,FirstRev}`, `store.Rev`,
  `watchableStore.rev`, `txnReadWrite.End`) pass `True`s.
- **Placeholders**: `slotX_step_M1` and `slotY_step_M1` deleted (no use left); `slotF_excl_M1`'s two
  `End` uses and `wsSlot_step_M1`'s `End` use gone (left: `slotF_excl_M1` in `store.Write` and
  `CmpCb`'s `restore()` excluder; `wsSlot_step_M1` in `watchableStore.Restore`, track A).
- `Api/EndSteps.lean` (new, over `import all` of `Api.lean`): `endCb_of_au`, the plain store's commit
  step from `Txn.End.contract`'s nested update, for a transaction whose writer slot is at its begin
  state `σ₀` (`Yat γ σ₀`: `slotY` with its compaction revision named, `Yat_slotY`): no change, both
  steps by agreement (receipt from `idxCert ilog`, `logCh_append_nil`); a change, both at the bump
  (the pending revision with the writer's half, the notified log's authority extended, the receipt
  and `LogWf` from the committed log's certificate; the view with `s.revMu`'s and the writer's
  quarters).

**What `KV.Write`/`Txn.*` still need** (in order; none is a frozen statement found false):
1. **The writer's slot at `σ₀` carried from `Write` to `End`.** `mvccTxn (.write σ₀ pend)` must fix
   `σ₀.crev` to the writer slot's compaction revision (End's `⌜σ = σ₀⌝` is by agreement with it);
   `slotY`'s is existential. Either `storeTxnWriteIs`/`isTxnWrite` (and the txn methods' specs over
   them) take the slot as a parameter, as the cores now do (`Y := Yat γ σ₀`), or `slotY` names its
   compaction revision. Then the watchable `wsEndCb`'s no-change arm at `Yat` too.
2. **The tie of the write transaction's `crev` (its `s.mu` share's) to the API's `σ.crev`**, which
   `Txn.Range`'s `rangeOutcomeC … k.state.crev` needs (the range reads `compactMainRev` under `s.mu`)
   and which `store.Write` cannot learn (it does not take `s.revMu`, which is where `slotX` and the
   index's `crevUB` meet). Proposed: a ghost the writer's slot and `muInvAt` share (e.g. a ghost
   variable of the compaction revision, half `muInvAt` at the lock's fraction, half `slotY`), updated
   by `updateCompactRev` and `Restore`, which hold `s.mu` exclusively and the writer's state. An
   `InvStore` change (`muInvAt`'s producers), so a request to the coordinator.
3. **The handle's resources for a writer** (`isMvccPlain`; `isMvccWatchable` has the readers' pool,
   track A): the plain store's readers' pool (`storeReaderC` by `threadTok`), `certFree γ`
   (persistent, minted from `NewStore`'s `γ.cok` authority, which `NewStoreApi` drops), the write-back
   supply (`storeWT`), and **the writer's revision token and pin** (`store.Write` takes `revToken γ`
   and `writerPin γ log`; `NewStore` returns `ownToks γ.revs (2^63-5)` and `writerPin γ [[], []]`,
   which `NewStoreApi` drops). Only the batch lock's holder may take them (writers are concurrent,
   serialized by the lock), so they belong with the writer's state (`writerL`, or `slotY`): with all
   the tokens there, `ilog.length + ntok + 3 ≤ 2^63` and `ntok = 2^63 - 3 - |ilog|`, one is free while
   `|ilog| ≤ 2^63 - 4`, which the receipts give (`|L| ≤ logCh L + 2 < 2^48 + 2` for a reachable state).
4. `store.Write`'s hook at `nil` (`hookRun`'s view-shift arm; `lockCtxM` as `Compact`'s core) and its
   fragment at `curAt (q/8)` (`mvccBackend`'s; `hookIs` wants an eighth).
5. `KV.Read`/`Rev`/`FirstRev`: `readCb`'s result at the lock's compaction revision too (`F L c`; today
   `F L`), for `mvccTxn (.read σ)`'s `σ.crev`.
Then `mvccTxn`'s definition (§2), `KV.Write`/`Read` at both store types, `Txn.End.contract` from
`endCb_of_au` (plain) and its watchable counterpart, the other `Txn` contracts, `KV.Put`/
`DeleteRange` (`writeView.*`, whose specs now take the step), `mvccDeleter` (`mvccDeleter_M1`),
`mvccTxn_leaseDelete.law`.

## Hand-off: M4, track A, the constructors, `Close` and `Restore`'s tracking (2026-11-06)

**Done** (no axiom; placeholders removed: `wsSlot_make_M1`, `cmpTrack_new_M1`; none added; no frozen
statement changed):
- **`New.spec`** (the API's; `Api/NewApi.lean`, `api.New.wp_proof`), as `NewStore.wp_proof`: the
  handle `isMvccWatchable` (the watch tokens' pool `watchTokPool_alloc`, the readers' pool
  `threadPool.init` from the watch readers but the compactor's), `mvccState γ mvccStart`, `mvccOpen`,
  `mvccBackend γ 1`, the deleter by `mvccDeleter_M1` (its docstring now names both stores).
  `newWatchableStore` makes its lock's slot (`wsSlot γ 1 [[], []]`) from `NewStore`'s client parts (a
  quarter of the pending revision, the notified log's lower bound); the internal
  `newWatchableStore.spec` and `mvcc.New.spec` return, at the end, `writerReg st γ.st ∗
  api.newClient γ.st.api [[], []] (-1) ½ st ∗ £ 1`.
- **`mvccOpen` gains `openRest γ p s`** (private, `Api.lean`): `⌜kbCmpM p.kb⌝` and, for a watchable
  store (`γ.watchQ`), its own closer (`∃ w rv stc`, the inner store's `ReadView` at `rv`, `rv.kv` at
  the watchable store `w`, `w.stopc ↦□ stc`, `stopCloser stc`, `wsWaiter w`): found from the inner
  store's location, so `Close` at the receiver agrees with it. `CmpCb` carries it (pattern `Hor`).
- **`mvccReaderN := backend.rdStockN - 3`** (sealed body; `EtcdBackend.mvccReaderN_eq` restated):
  the readers' pool of `isMvccWatchable` needs `threadBound ≤ n + 1` for its `n` copies, and the two
  sync loops' and the compactor's slots are held for good. The frozen premise `threadBound GF ≤
  mvccReaderN` is unchanged in text; the server's `threadBound ≤ 2 ^ 28` still meets it.
- **`KV.Close.contract` at both types** (`Api/CloseApi.lean`, `store.Close.wp_api`,
  `watchableStore.Close.wp_api`, over `store.Close.spec`, the trust boundary): the right to close by
  the mode from `mvccOpen` (`storeCloserM_on`); the watchable store's stop channel and waiter from
  `openRest`, agreeing with the receiver through the read view.
- **`store.Restore`'s tracking** (`cmpTrack_new_M1` gone): `cmpOk_restored`, `cmpTrack_restored`
  (`store__Restore.lean`): the meta keys' record allocated at the image's records `(r.sched, r.fin)`,
  the finished counter at `crevN (finRev r.fin)`, the records' compaction revision at `r.crev`, the
  lower bounds' authority at `crevN r.crev`, the job's cursor at `(r.finRev, ⟨0, 0⟩)` (the queue's
  `compactTok` at `r.finRev ≤ r.crev`), the values' halves from `restoreImageM`'s `Hvals`.
- **`names_nonempty.law`** (`Api/NamesLaw.lean`, `names_nonempty.law_holds`).

**Statements changed that modules outside mvcc use**: `mvcc.New.spec`'s post (three conjuncts
appended): `etcdserver/BuildLemmas.lean` no longer calls it (the boot calls `mvcc.api.New.spec`,
`52d72250bc`); any remaining caller's pattern needs a trailing `-`. `mvccReaderN_eq`'s right side
(no user). `mvccOpen`'s body (sealed; only mvcc's `import all` files unfold it).

**Not linked**: `New.wp_proof`, `NewStore.wp_proof`, the `Close` and names results (`Link.lean` is
generated by `etc/gen-link.py`; the TCB baseline needs `--check --update` for the two removed
`sorry`s, `etc/`).

**Left, `KV.Restore.contract`** (not started; what it needs, in order):
1. The handle/open token must carry what the internal `store.Restore.spec` takes and `NewStoreApi`
   drops today: `fieldShare s γ ¼ ∗ wsDep γ`, `writerOwn γ` (the retired readers), `writerPin`,
   `idxCert`, the revision tokens `ownToks γ.revs (2^63 - 3 - |L|)` (with request 3 below: in the
   writer's state), for a watchable store `logQ`; and `certOk γ L'` (from `certFree`, request 3).
2. A bridge from `mvccStorageFor B' Pk' σ'.log σ'.crev u` to the internal premises at a general image
   (records `r`): `restoreImageM` (`restoreImageM_of_openOn`), `storeBackendTR`/`keyCleanReadR`
   (the bridge's), `restoreRcptM`, `restoreRegM`, the reader tokens (`nReaders`); `r.crev = σ'.crev`
   from `imageOk`.
3. `RestoreMoves`' five placeholders need the restorer's API parts threaded through the internal
   `store.Restore`/`watchableStore.Restore` specs (statements used by the server's snapshot apply):
   the takeover's two (excluding the frozen state, depositing `slotFr`) take `api.shareTok γ.api 1`
   (`mvccBackend γ 1`'s); the switch's slot step and the finish's writer slot need the client's
   update (the contract's AU at `σ'`, with `rcvW`'s other half at `r.crev`, which `store.Restore`
   allocates and drops today); **the finish's frozen exclusion has no witness**: the restorer
   deposited its whole token in the restoring arm, so in the checked-in arm at the new names it holds
   nothing the frozen arm (`slotFl ½ true ∗ slotF`) conflicts with. A fix: the restorer keeps a part
   (e.g. `slotFr := shareTok ½`, the other half kept until the finish, with `slotFr_share_excl`'s
   users given the restorer's half), or the frozen arm keyed by the current names' eighth. A design
   choice, for the coordinator.
4. `wsSlot_step_M1` (`watchableStore.Restore`): the lock's notified log to `L'` (the client's
   `nlAuth` update at the switch).

**Requests from the coordinator** (2026-11-06), not done: track B's exact shapes are not yet in its
section. (3) the plain handle's readers' pool, `certFree`, the supply, the revision tokens and pin in
the writer's state: `NewStoreApi` has them to give (`rdStockN - 2` `storeReaderC`s after the
compactor's, `ghostMapAuth γ.cok 1 ∅` → `certFree` by `ghost_map_insert_persist`, `ownToks γ.revs
(2^63-5)`, `writerPin γ [[], []]`). Two constraints: `CmpCb`'s watchable `Compact` builds an
`isMvccPlain` of the inner store from the watchable handle, so a `storeReaderC` pool in
`isMvccPlain` needs one in `isMvccWatchable` too, and two pools of `threadBound - 1` copies each need
`2 · threadBound ≤ rdStockN` (`mvccReaderN` about half the stock; the server's `2 ^ 28` still
fits); and a persistent write-back supply is per backend instance (`kbWTSupplyM p.kb`), so after a
`Restore` it is the new backend's: in the handle it must be at the current names (as `mvccOpen`'s
is, under `p`), not at `γ.kb`. (2) the compaction revision's ghost at `Restore`'s switch: waits on
track B's definition.

**The coordinator's decisions (2026-11-06) and their status:**
1. **`restore_finish`'s frozen exclusion: `slotFr := shareTok ½`, the restorer keeping the other
   half** (decided). Not applied yet, because it would break a proved lemma: `slotFr_share_excl`
   (`ghostVar γ.wr 1 () ∗ slotFr γ ∗ shareTok q ⊢ False`, `KV.Compact`'s excluder of the restoring
   state at the compactor's share `q`, `CmpCb`) holds only while `slotFr` is the whole token; at `½`
   it is false for `q ≤ ½` (the restorer's kept half is not in the lemma). Two ways out, for the
   coordinator: (a) as decided, and `KV.Compact`'s core excludes the restoring state by `s.mu`'s
   deposit ghost (`wr_restoring_excl`'s form, `γ.wr 1` from `muInv` whole under `updateCompactRev`'s
   exclusive `s.mu`) instead of the share (a change to `store.Compact`'s core, `CmpCb`); or (b) keep
   `slotFr` the whole token and split the frozen flag instead: the restoring arm holds `slotFl γ ½
   false`, the restorer keeps the other half from the takeover to the finish, where it agrees
   (`false`) with nothing in the frozen arm's `slotFl γ ½ true` (a contradiction), and the finish
   rejoins it to `slotFl γ 1 false` for the checked-in arm. (b) changes only `writerInvBody`'s
   restoring arm (`InvStore`) and `RestoreMoves`; the restoring arm's other openers put it back as
   they found it.
2. **Request 3's pool: one pool** (decided): the watchable handle's readers' pool, the inner store's
   `isMvccPlain` built over the same pool (parameterized by it, or by a reader-supplying resource the
   watchable handle lends), `mvccReaderN = rdStockN - 3` kept (recorded in
   `notes/mvcc-api-candidate.md`). The write-back supply at the current names (agreed). Not applied
   yet: waits on track B's exact shapes (its hand-off) and on its uncommitted `InvStore`/`NewStore`
   edit (`api.wcrPart`, `muInvAt`'s `HwcM`), which also touches `store.Restore`'s `muInvLag`/`muInvAt`
   (request 2: `store__Restore.lean` must add the new conjunct where it builds them).
