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

## P2 as built so far (internal specs in either mode, beside today's)

- `storeTxnWrite.End.specA` (`absCommit γ ilog pend Q`: the caller's update run at the commit on
  `absAt`/`pndAt`, giving `Q`), `metricsTxnWrite.End.specA` (`txnEndPreA`/`txnEndPostA`),
  `store.Read.specA` (`absRead γ Q`: run where the log read is fixed, on `absAt` and `crevUB`),
  `store.Write.specA` (`hookOk` and a pin `curAt γ dq o` at any fraction for `hookIs`),
  `NewStore.specA` (at a mode `aq`; `NewStore.wp_proof` is its corollary at `aq = false`).
- Each `specA` proof is today's with the update applied at the linearization point; the
  `specA`s sit in the same spec and proof files as today's (a second declaration per file: a
  known layout exception until the candidate specs replace today's).

## P4's design (the API's predicates over the implementation, plain store first)

- `mvccState γ σ := ghostVar γ.abs ½ σ.log ∗ ghostVar γ.pnd ½ σ.pending ∗ crevUB γ.idx ½ σ.crev ∗
  idxCert γ.idx σ.log ∗ ∃ M, ghostMapAuth γ.cok 1 M ∗ ⌜every entry n ↦ L is not empty, of length n,
  a prefix of σ.notifiedLog⌝ ∗ ⌜MvccReachable σ ∧ bound⌝`: the certificate map (`certOk`), the
  caller's authority today, links the logs the implementation certifies (reads, watch events) to
  the client's notified history by pure entailment (the watch laws are `⊢`, no invariant).
- A commit's first update (the notification) inserts the next log's entry (it is the
  notified log's), which is today's `certOkNext`; a plain store's wrapper fires it before `End`
  (reads see `σ.log`; nothing else reads `pending`), the second inside `absCommit`.
- `mvccTxn` of a write transaction: `isTxnWrite` (with the writer's `pndAt ½ none`) and `certOk` of
  its log: `mvccTxn_write_agree` from `idxCert σ.log` (σ's log a prefix of the transaction's, by the
  index writer's authority) and `certOk` (the transaction's a prefix of the notified log), with
  nothing pending (the writer's half).

## P4/P5 as built so far (2026-11-02)

- **The implementation** (`ApiImpl.lean`): `MvccImpl` (store names, the readers' pool's name, the
  mode); `mvccStateI` (the client's halves of `γ.abs` and `γ.pnd`, half of `crevUB`, `idxCert` of
  the log, the certificate map `γ.cok` with `certMapOk` against the notified history, the notified
  log's certificate while pending, reachability and `|log| + 3 ≤ 2 ^ 63`); `isMvccI` (`isStore`,
  the mode, a persistent pin of the objects, the readers' `threadPool` of `storeReaderC`, the
  receipt-paid `revPool`, the write-back supply); `mvccTxnI` (today's read or write transaction at
  the state, the pool's loan); `mvccBackendIsI`, `mvccWatchersOkI`. `Api.lean` defines its
  vocabulary over them (the watch stream's, the views', the hash's still opaque).
- **The lemmas** (`ApiLemmas.lean`): `mvccHook_hookOk`; the certificate map's; `commit_second`,
  `absCommit_of_au` (a plain store's commit update: both of the caller's updates at the bump, the
  next log's certificate inserted at the notification), `commitAU_nil`; `mvccTxn_read_eq`,
  `mvccTxn_write_eq`.
- **Proved candidate specs** (`<F>.wp_proofC`, from `specA` or today's `spec`): `store.Read`,
  `store.Write`, `metricsTxnWrite.End`, `.Range`, `.Rev`, `.Put`, `.DeleteRange`.
- **Changes to the candidate API found by the proof**: `mvccHook` requires a non-nil hook (today's
  real-backend hook fact, `bkHookIs`, does: a store without a hook cannot write); `Put`'s key bound
  `|k| < 2 ^ 63 - 1` is unconditional (today's `Put` needs it of every key);
  `mvccState_reachable`'s bound is `|log| + 3 ≤ 2 ^ 63` (the revision budget's), not `< 2 ^ 62`.
- **Internal specs changed for the abstract mode** (`specA`s): the reader's ticket after the
  call's first step (`£ 1 ={⊤}=∗ storeReaderC ∗ T`, the pool's borrow needs a later credit), the
  revision and write-back tokens paid by receipts of the call's resolution steps; the commit's
  certificate produced by the commit update (`absCommit` gives `certOk` of the next log), not taken
  beforehand.
- **Since** (same day): `NewReadOnlyTxnWrite`, `txnReadWrite.Range/Rev/Changes/End`,
  `metricsTxnWrite.FirstRev` (read; write: `sorry`) proved. `mvccTxn` of a read transaction is the
  store's or its read-only write transaction's. `MvccImpl` is over the watchable store's names
  (`ws : WsNames`, `γ.st := γ.ws.st`); the client's state holds, on a watched store, half of
  `γ.wlog` (the watchers' synced log; the watchable store's commit update advances it with the
  other half, `s.mu`'s). The client's compaction revision is by the store's mode: half of `crevUB`
  when it compacts, else `-1` (the store's `crevFrozen`; `isMvcc` carries `wsFrozenM`; a write
  transaction records it, `txn_crev_fact`). `NewStore.spec` and `newWatchableStore.spec` are now
  stated at a mode `aq` (their callers, in mvcc, pass `false`); `New.specA` likewise, `New.spec` its
  corollary (the etcd server's). In the abstract mode `newWatchableStore` gives the range deleter's
  code (`rdCode`: its spec is any spec of the watchable `Write`'s), the deleter's contract
  (`mvccDeleter`) being over the pools `New`'s candidate makes.
- **The watchable store** (same day, `3b8688c4ad`..`ee182aca37`): `isWatchableMvcc`, `mvccOpen`,
  `mvccDeleter` defined. `MvccImpl` gained the watchable store's location `wl`, the store's `sl`
  (`isMvccI s γ` pins `γ.sl = s`, so a transaction's store is the names'), and the open token `op`.
  The readers' pool lends `poolR` (the store's reader and, watched, a reader slot of the watchable
  store's `s.mu`: `watchReader`, which the watch stream needs); a transaction holds `mvccLoan` (the
  pool's loan and that slot; `mvccBorrow`/`mvccGiveBack`). `isMvccI` holds, watched, the watch
  tokens' pool `wtPool` (receipt-paid, as `revPool`). `mvccOpenI γ q` is the token's share and an
  invariant holding the whole token or the closer (`wsCloserM`; `mvccOpen_take`). The write case of
  `mvccTxnI` is the store's transaction or the watchable store's wrapper over it (its fields, the
  watchable store over the transaction's store).
- **Proved since**: `watchableStore.Write` (from `store.Write.specC`), `watchableStoreTxnWrite.End`
  (`specC` from `metricsTxnWrite.End.specA`: the caller's first update at the seal, `notify_first`,
  which inserts the next log's certificate in the client's map, the events' certificate; the second
  at the bump, `absCommit_of_au2`, with `s.mu`'s half of the watchers' log, which it advances with
  the client's half; called at a writer's part not notified it finds that certificate in the map of
  a history without it, impossible; the notified log pinned by the committed log's authority,
  `body_pinA`), `New` (`specC` from `New.specA` true and the backend's specs: the pools, the pin, the
  state at `mvccStart`, the open token, the deleter), `watchableStore.Close`.
- **Changes to the candidate API found by the proof** (since): `New.specC` takes the batch limit in
  range (`batchLimitOk`), `threadBound GF + 2 ≤ 2 ^ 30` (Go's `2 ^ 30 - 1` readers, two kept by the
  loops), a backend that does not compact (`d.cm = false`), its deletable-keys registration
  (`dlInit`) and two write-back tokens (what `NewStore` spends). `mvccTxn_unwrap` is false at a
  read view `k'` (the watchable wrapper is only ever a write transaction): restrict it to writes.
- **Proved since** (`8a0cbdff40`..): `metricsTxnWrite.Changes` (both views), `store.Rev` (a watched
  store: `readView.Rev` over the watchable store, `store.Read.specC` at a KV over the store,
  `kvOver_ReadC`; `isMvccI` holds, watched, `isWatchableStore`, whose fields give the store's views;
  an unwatched store's views are not yet in `isMvccI`: `sorry`), `store.Commit` (the backend's
  reader token checked out of the store's readers' pool for `ForceCommit`, with a deposit split off
  the exclusive lock's whole `γ.wr`, `wr_dep`, checked back in before `Unlock`; the write-back token
  from the deferred `Unlock`'s resolution receipt). Laws (`ApiLaws.lean`): `mvccState_excl`,
  `mvccState_reachable`, `mvccTxn_write_agree` (always the transaction's own state),
  `mvccTxn_unwrap` (restricted to write views), `isWatchableMvcc_store`, `mvccDeleter_spec` (from
  `watchableStore.Write.specC`; the deleter carries the watchable store and the package's init),
  `mvccWatchersOk_unwatched`, `mvccWatchersOk_nil`. Not yet: `FirstRev` (write: the tester does not
  call it), `persistent` (needs the opaque predicates defined), `mvccTxn_trace`, `isMvcc_views`, the
  hash and restore laws, the watch laws.
- **The watch stream's design inputs** (a survey of the old specs, 2026-11-02): the old stream is
  over `WatchParams` (`InvWatchStream.lean:188`), instantiated by `storeWatchParams s st γ`
  (`InvWatchStore.lean:1718`): `R = watchReader` (lent to each call: the pool's `poolR` copy), `T =
  watchTok γ ∗ noCompactor γ.st` (consumed by every `Watch`, failed ones too: the `wtPool` pays it),
  `IWF = watcherIs` (range, filters, first revision `lo`: the start revision, or `C.length` of an
  `idxCert C` at 0). `NewWatchStream.spec` gives `isWatchStream`, the channel `ch` and its invariant
  `inv watchN (watchChanInv γ ch γc)`, `watchStreamOpen γo`, `watchConsumer γc []` (half of
  `γc.recv`), with the caller's `Q` (what an id `-1` response proves) and `Ψ` (a cancel's reason).
  The consumer receives with `wp_watch_receive`/`watch_recv_au` (`WatchRecv.lean:454/275`):
  `watchRecvResult` gives the next `RespM r` (`respIs v r`: id, revision, events, compaction 0),
  `respOk r`, and the persistent `watchRecvOk γ r.w rs_w` (`WatchRecv.lean:86`: the watcher's
  responses so far are the kept deliveries of `watchEvents L r lo d`, `L` an `evLog`, sealed and
  certified, so in the client's certificate map, a prefix of its notified log), `chanRegFact`
  (the watcher's id, `chanIdAssigned`, agreeing with the stream's `idAssigned`), `progFact` for id
  `-1`, `respCov` (an event-less response covers its watcher up to its revision; an id `-1` one every
  watcher registered before it, `regsAt`, or cancelled), `r.idx = |received|`. The v3rpc proofs
  (`serverWatchStream__sendLoop.lean`, `rcvOk`/`rcvOk_snoc`) accumulate these facts per received
  index: `wsRecv ι rs` is to be the consumer's half and such an accumulator over the `RespM`s, `rs`
  their views; `wsWatchers ι W` the registrar's (the `Watch` caller's) record of the ids it got, each
  `idAssigned` with its `watcherIs` facts; the laws then from the accumulator and `certMapOk`.
  `Watch`'s old post consumes `T` even on `ErrEmptyWatcherRange`; `RequestProgress(All)`' posts say
  nothing (the facts come at the receive). The old guarantee theorems cited by `WatchRecv.lean`'s
  docs (`watchRecvOk_cert`, ...) do not exist; `recv_unfiltered`
  (`Proof/go_etcd_io/etcd/client/v3/WatchContent.lean:412`) is the closest.
- **The watch stream, as built** (`cde8dc6545`..`1930c006e7`, `ApiWatchImpl.lean`): `WsName` the old
  stream's and channel's names with the API's (`reg`, `rcv` tokens; `op`, the open token's shares;
  `cl`, a closed mark); `isMvccWatchStream` the old stream at `storeWatchParams` (progress fact and
  cancel reason `True`), its channel and invariant, and the open invariant (`op` whole with `cl`
  persistent, or the old open token with `cl` whole); `wsWatchers ι W` its token, each id's `idTok`
  and `wInfoOk` (the id's watcher, `watcherIs` at the view's range, filters, first revision);
  `wsRecv ι rs` its token, the channel's consumer half at `ms` (`rs = ms.map respView`) and each
  received response's `rcvFact` (`watchRecvResult`'s facts). Proved: `NewWatchStream`, `Chan`,
  `Close` (the old open token from the open invariant), `RequestProgress(All)` (the watchable store's
  reader borrowed, `mvccBorrowW`, for a credit of the body's first steps), `Watch` (the reader
  borrowed; the watch token from `watchTokPool` for the receipt of the store `watch`'s resolution;
  the caller's update fired once the store's `watch` returned, the id fresh by its `idTok`), and the
  law `wsChan_recv` (`ApiWatchLaws.lean`, `watch_recv_au`).
- **Changes to the candidate API found by the watch stream's proof**: the registrar's view is a map
  keyed by the stream's ids (`GMap w64 WInfo`; the old stream's proof records no counter of the ids
  it assigns: `idsInv` bounds them by `nextID` only); `Watch` at a positive start revision (at `0`
  the first revision is the state's at the registration, inside the store's `watch`, which the
  late-fired update cannot see); `Watch`'s closed arm refutes a share of the open token under a fancy
  update (`□ (∀ q, wsOpen ι q ={⊤}=∗ False)`: the old open token is then in the stream's mutex
  invariant, out of reach). **Open**: `wsRecv_resp`'s third conjunct (`r.evs ≠ [] → (W !! r.id).isSome`)
  is false for the late-fired update (a watcher's events can be sent and received while its `Watch`
  is in flight, before the view has it); the events and progress laws only speak of ids the view
  has, so they hold. A client (the tester's receiver, under the lock its registrar holds across
  `Watch`) needs "every id with events is in the view" when no `Watch` is in flight: either fire the
  update inside the store's `watch` at the registration (a fancy update in its `Hreg` callback, in
  the 1277-line proof), or give the law a premise no `Watch` holds.
- **The watch laws** (`eda33cfa6b`..): `wsRecv_events`, `wsRecv_progress`, `wsRecv_resp` proved
  (`ApiWatchLaws.lean`), restated: the events and progress guarantees are for watchers without
  filters (a filter's spec, `filterSpec`, does not determine its predicate: two specs of one function
  need not agree, so the received events cannot be shown filtered by the registrar's predicates);
  only an event-less response's revision is bounded (`respRev`; an event response's is not recorded
  in its facts); progress is a watcher's own progress responses only (a stream-wide one, `-1`, covers
  the watchers registered before it through `regsAt`, which spends a later credit under a fancy
  update: a plain entailment cannot); a response with events has a watcher's id (`≠ -1`), not "an
  id the registrar's view has" (false for the late-fired update, above). The view's facts
  (`wInfoOk`) record the id is not `-1` and the first revision is positive. The proof: a watcher's
  last received response's `watchRecvOk` covers all its responses (`last_idx`); the view's id and
  watcher agree on every response with events (`rcv_agree`: `respOk`, `chanRegFact`, the stream's
  and channel's id maps the same); without filters the deliveries are whole (`deliv_nofilter`); a
  watched log is a prefix of the notified history (`evLog_notified`: in the certificate map, or one
  of the first logs, comparable with the certified one).
- **What the tester needs that the watch laws do not give**: its receiver checks that a response's
  watcher is in its map (`c.watchers[resp.WatchID] != nil`), under the lock its registrar holds
  across `Watch`: "every id with events is in the registrar's view when no `Watch` is in flight".
  Options: fire `Watch`'s update at the registration (inside the store's `watch`, whose callback
  `Hreg` is a basic update run with the channel's invariant open, before the watcher's `watcherIs`
  facts exist: the view would need a "registered, facts pending" state); or a counter of the stream's
  ids in `idsInv` (a mode of `WsStreamNames`, as `absQ`), whose half the view holds.
- **Next**: the lessor's `Grant`/`Revoke` over the API (today's are over the old mode's resources:
  `rdIs`, `watchWriter`, `storeReader`, and the lease ghost over the writer's log `stateAfter log`)
  and `NewLessor` without `clusterOk`; the registrar's completeness (above); then the tester's proof.

## Log

- 2026-11-02: plan; the tester translated (`etc/goose.py` project `mvccrand`; its type `rec`
  renamed `kvRec`, Lean's recursor's name).
- 2026-11-02: P1 built and committed (`cad9d508e3`; full `lake build` green, 11331 jobs).

## The end state: one canonical spec (the user's, 2026-11-02)

The user wants a single canonical spec per mvcc function: `Spec/.../mvcc/<F>.lean` holding one
`<F>.spec`, the candidate's; today's `spec` and the `specA` variants demoted to internal lemmas in
`Proof/` (the candidate proofs rest on them); every client moved onto the API. As of `e59d153a1a`
no client outside mvcc uses a `specC`: the etcd server's 34 files (`etcdserver/txn` 15, `etcdserver`
10, `v3rpc` 6, `apply` 2, `lease` 1) use today's specs, and the linked results (`Link.lean`) are
today's. What the API lacks before the server can move onto it:
- `Watch` at start revision `0` (etcd's clients watch from it), filters (v3rpc's `NOPUT`/`NODELETE`),
  stream-wide progress, and registrar completeness (v3rpc's send loop may need more than `WInfo`:
  `idAssigned`, `chanRegFact`, `streamRegAt`, review B6);
- compaction (the abstract mode excludes it; the server's store compacts), `Restore`, the hashes,
  `NewStore.specC` and an unwatched store's views;
- the lease package's `Revoke`/`Grant` over the API (the lease bucket written inside the store's
  write transaction);
- the server's proofs themselves, in the abstract mode (today's use the old mode's resources:
  `watchWriter`, `writerFrag`, `storeReader`).
Then: rename each `specC` to `spec`, move today's specs and the `specA`s to `Proof/` as internal
lemmas, regenerate the links, the TCB baseline and the interfaces.
