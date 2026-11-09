# Batch 3b: etcd's server transactions (report)

Scope: `server/etcdserver/txn/*.go` (Range, Count, Put, DeleteRange, Txn over mvcc; compares,
nested transactions, the range response's sort/limit/count/keys-only/filters, `prevKV`; the
warnings and metrics). Everything builds (`etc/specs-build.sh --dir
Spec/go_etcd_io/etcd/server/v3/etcdserver/txn`: 48 modules); the snippets pass `go vet` and `gofmt`.

## Files

- Vocabulary: `Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/Api.lean` (namespace `Txn`).
- Specs (47, one per function with an old spec), same directory:
  - client-facing: `Range`, `Count`, `Put`, `DeleteRange`, `Txn`, `IsTxnReadonly`,
    `IsTxnSerializable`, `IsDefaultOrdering`, `HasRevisionFilters`,
    `WarnOfExpensiveReadOnlyRangeRequest`, `WarnOfExpensiveReadOnlyTxnRequest`,
    `WarnOfExpensiveRequest`, `WarnOfFailedRequest`, `ApplySecObserve`;
  - internal (mirror the code, short comments): `executeRange`, `rangeLimit`, `filterRangeResults`,
    `sortRangeResults`, `asembleRangeResponse`, `checkRange`, `pruneKVs`, `kvSort__Swap`,
    `kvSort__Len`, `kvSortBy{Key,Version,Create,Mod,Value}__Less`, `mkGteRange`, `deleteRange`,
    `put`, `checkPut`, `checkLease`, `checkAndGetPrevKV`, `getPrevKV`, `txn`, `newTxnResp`,
    `executeTxn`, `checkTxn`, `compareInt64`, `compareToPath`, `applyCompares`, `applyCompare`,
    `compareKV`, `warnOfExpensiveGenericRequest`, `isNil`, `RangeSecObserve`.
- Snippets: `examples/specreq/txn/{read,write,helpers}.go` (13 `REQ`s).

Left out: the sorters' promoted `Swap`/`Len` wrappers (`kvSortByKey.Swap`, ...: goose's
`MethodUnfold` wrappers of `kvSort`'s, no old spec); nothing else.

## The design, in short

(The draft's; round 1 restated it over 3e's API: see "Round 1 repairs" at the end, which wins where
they differ.)

- **State**: the member store's history `h : KVHist` (W0's), in mvcc's client-owned `mvccState γ h`;
  for writes, 3c's lessor writer token `Lease.lessorState γl n ls` (its `ls.table` is W0's lease table
  for `PutReq.check`).
- **Reads** (`Range`, `Count`, read-only `Txn`): the caller's atomic update, state unchanged, fired at
  mvcc's `Read`; post `∃ h, Q h ∗` the answer at `h`. Any context (its error an outcome).
- **Writes** (`Put`, `DeleteRange`): one update fired at mvcc's `End` (or at the failing check),
  moving `h` to W0's next history (`putHist`, `h.commit (delEvents l)`). No store pin: one mvcc write
  transaction is atomic under mvcc's writer lock.
- **A writing `Txn`** (read txn, checks, then a write txn: `txn.go:60-63`) takes its update **pinned**
  at `h0`: `AU <{ ∃∃ h, ⌜t.readonly ∨ (h = h0 ∧ attached h.store ls)⌝ ∗ mvccState γ h }> …` — one spec
  for both modes, the pin only for a write (a case split on the input).
- **Answers are functions** (`putAns`, `rangeOut`, `run`): `goSort` (opaque) names Go's `sort.Sort`
  output, so a range's answer is unique. Laws `rangeOut_answers`, `run_txnRun` relate them to W0's
  `RangeReq.answers` and `TxnRun`.
- **Errors**: `errIs err e` (the sentinels for W0's `e`), `ctxErr err` (mvcc's context error).

## Exported vocabulary (`Txn`)

Pure, transparent:
- `targetOk r`: the sort target is `KEY`..`VALUE` (else `lg.Panic`).
- `countReq`: `Count`'s request.
- `rangeLimitZ`: `rangeLimit`'s result.
- `sortOut`: `sortRangeResults`.
- `assemble`: `asembleRangeResponse`'s cut and keys-only.
- `rangeOut r wtc all`: `executeRange`'s answer from the range's keys `all`. Its count is truncated
  at the pushed-down limit without `withTotalCount` (`RangeStream`).
- `rangeAll`: the range's present keys (unique).
- `kvFits`: the record's numbers fit `int64`.
- `hdrAt rev`: a header with only the revision.
- `ignores`, `needsPrev`.
- `putEvents`, `putPrev`, `putAns`, `putHist`: the put's step.
- `delEvents`.
- `attached s ls`: the store and the lessor agree (3c's attachment invariant: every key's lease is
  live and is `itemMap`, each live lease's item set is its keys, `0` never live).
- `sameLeases`: a KV request changes only the lessor's attachments.
- `cmpsHold`.
- `opCheck`/`opsCheck`: `checkTxn`.
- `execOp`/`execOps`: `executeTxn`.
- `opPath`/`opsPath`/`txnPathOf`: `compareToPath`.
- `run t h ls skip`, `runHist`, `runRev`: the transaction's run, next history and header revision.
- `opIgnTaken`/`opsIgnTaken`, `opIgnKeys`/`opsIgnKeys`, `opDelRanges`/`opsDelRanges`.
- `opSafe`/`opsSafe`, `txnSafe t`: no empty operation, known sort targets, no ignore-put after a
  covering delete, at any depth and in both branches.
- `TxKind`, `viewRev`, `viewStore`, `viewErr`: an open mvcc transaction's view.
- `rangeOk`, `putOk`, `delOk`, `txnOk`: the replies, over W0's `Wire.lean`.
- `rrOwn`: mvcc's `*RangeResult`.
- `msgOpt`: a message the warnings size.

Opaque:
- `goSort` (pure function).
- `errIs`, `ctxErr` (persistent).
- `roTxnResp` (a read-only transaction's partly filled response).
- `respSkel` (internal: `newTxnResp`'s tree).

Provisional, the callees' slots:
- 3e's: `MvccName`, `mvccN`, `mvccKV`, `mvccState`, `mvccWriter`, `mvccTxn`, `mvccLessor`.
- 3h's: `stringerOk`.
- 4b's: `traceAt`.

Laws:
- `goSort_sorted`: a sorted permutation.
- `rangeAll_eq`.
- `rangeOut_answers`: `rangeOut r true all` is a W0 answer, for a valid sort.
- `run_txnRun`: `run` is W0's `TxnRun` for a valid transaction, and its events do not depend on
  `skip`.
- `runHist_readonly`.
- `errIs_persistent`, `errIs_ne_nil`, `errIs_agree`.
- `ctxErr_persistent`, `ctxErr_ne_nil`, `ctxErr_not_errIs`.
- `traceAt_persistent`, `stringerOk_persistent`, `mvccKV_persistent`, `mvccLessor_persistent`,
  `mvccState_excl`.

## Main changes from the old specs (`specs-ref`'s 47)

- **The model**: W0's `KVHist` and `Resp` replace mvcc's `MvccState` log and the txn model
  (`srvRunTxn`, `srvRangeOk`, `txnResponseIs`). The answers are deterministic functions related to
  W0's relations by laws.
- **One update per call**: the old `beginAU`/`commitAU`/`putAU`/`delAU`/`txnBeginAU` pairs and the
  wand from the read update to the write updates are gone. `Txn`'s two triples (`specSole`,
  `specRead`) are now one triple, pinned only for a write.
- **The batch lock's critical section** (`csA P f Pre Q Post`) and the backend share (`kvBackend`)
  are folded into 3e's `mvccWriter`.
- **The lessor**: the owner `lessorUser L I` and `leasesKnown` are replaced by 3c's writer token
  `lessorState` with `attached`. The item map is now stated, so that the applier can keep 3c's
  attachment invariant.
- **Relaxed**:
  - the context: any context for reads and for `Put`/`DeleteRange`. A cancelled context is an
    outcome, no longer a `neverDone` premise. Only a *writing* `Txn` takes `ctxDone ctx -∗ False`,
    because the code panics there.
  - The reader slot (`mvccReaders γ 1`) is now a thread token.
  - `Put`/`DeleteRange` take no store pin.
- **Restated**: the paths' premises (`PathsIgnOk`, `txnGetsOk`) become the state-free `txnSafe`,
  which the gRPC checks give (asked of 2a). The internal `executeTxn` keeps the path-exact need
  (`opsIgnTaken` present).

## Decisions for the user

1. **The answer as a function needs a functional `sort.Sort` spec in Perennial.**
   - Why: 2c's read registry and 2d's commit-time answers (`applyStep_fun`) need the answer of a
     range (alone or inside a transaction) to be a function of the store. W0's
     `RangeReq.answers` allows any order among ties (several keys with version 1 sorted by version),
     and Go's `sort.Sort` (pdqsort) is deterministic.
   - What I did: `Txn.goSort` names its output (opaque, law `goSort_sorted`). Perennial's
     `sort.Sort.spec` today gives only "a sorted permutation", so `sortRangeResults` cannot be proved
     against `goSort` until Perennial states the sort as a function of its input and comparator.
     That is a general change, true of the code, not shaped by this proof.
   - The alternative: keep the relation. 2c's registry fires every answer `Step` allows (finitely
     many). 2d's commit-time firing for a write transaction with a sorted range then needs another
     device (a prophecy of the apply's answer).
   - My recommendation: the Perennial change (`notes/perennial-changes.md`, to be recorded by the
     coordinator).
2. **Compaction at revision 0** (W0's model `compacted = 0` means "never compacted"; mvcc's
   `FirstRev` is then `-1`). A `Compact(0)` would set mvcc's to `0`, and a range at revision `-1`
   would then differ from W0's `txnRevErr`. W0 and 2c already restrict compactions to `rev ≠ 0`
   (`issues/etcd-restore-scheduled-compact-zero.md`); txn inherits that restriction and adds none.

## Open questions

- 3e's API is not written yet: my mvcc slots and `req/..._storage_mvcc.md` "from 3b" fix what I
  assume. Three points matter most:
  - the state is W0's `KVHist`, or projects to it;
  - `Write` keeps the state from the begin to `End`;
  - mvcc's put/delete thread 3c's writer token and keep `attached`.
- `errIs` → 2c's `srvErrOf`, and `ctxErr` → `srvIndef`: integration laws for 2c (`togRPCError`'s
  map holds the four sentinels; a context's wrapped error is unmapped).
- 3a: its applier passes `context.TODO()` and the server's lessor. It holds the writer token,
  `mvccWriter`, and `attached` from its state machine. A revocation (3c's range deleter) must also
  keep `attached`, which is 3a's composition.

## The callers' needs, answered (`req/go_etcd_io_etcd_server_v3_etcdserver_txn.md`)

- **2c**:
  1. `Range.spec` (any `withTotalCount`).
  2. `Txn.spec` for read-only transactions: unpinned, any context; `IsTxnReadonly.spec`,
     `IsTxnSerializable.spec`.
  3. `Count.spec`.
  4. The answer function (`rangeOut`, with `goSort`: decision 1).
  5. The warnings: `WarnOfExpensiveReadOnlyTxnRequest` also takes the partly filled response after
     a context error (`roTxnResp`, which `Txn.spec` gives).
- **2a**: `intervalsOk` ties to `Txn.txnSafe` (the law asked in 2a's `req/`).
- **3a**:
  1. Each call is W0's step, deterministic: `putAns`/`putHist`, `delEvents`, `run`/`runHist`,
     `rangeOut`.
  2. `skip`: `run … skip`; the events do not depend on it (`run_txnRun`).
  3. No panic for an admitted transaction: `txnSafe`, `attached`, and `Context.ctxDone ctx -∗ False`
     (from `context.TODO()`, asked of W0).
  4. The warnings: **not "any response"**. `WarnOfExpensiveRequest`/`WarnOfFailedRequest` call
     `proto.Size` on the response, which reads it and recurses once per nesting level. A trusted
     spec true at every input therefore takes the response's content and a depth bound (`msgOpt`).
     3a builds its responses and owns them (W0's and 1c's reply predicates; 3h's relation laws give
     `msgAt`).
  - 3a's `kvSt`/`lessorSt`/`kvOk` are its names for my slots (`mvccState`, `Lease.lessorState`,
    `mvccWriter`). At integration both sides take 3e's names.

## `req/` sections written (`## from 3b`)

- `go_etcd_io_etcd_server_v3_storage_mvcc.md` (3e): `Read`, `Write`, a transaction's view
  (`Range`/`Rev`/`FirstRev`/`Changes`), `Put`/`DeleteRange` with the lessor's token, `End`,
  `NewReadOnlyTxnWrite`, revisions fit.
- `go_etcd_io_etcd_server_v3_lease.md` (3c): `Lookup` through `lessorIface`; lease `0` never live; the
  attachment invariant as `Txn.attached`.
- `go_etcd_io_etcd_api_v3.md` (W0): an empty range end is `nil` in the request predicates.
- `context.md` (W0): `TODO()`/`Background()` never done.
- `go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md` (2a): the checks give `Txn.txnSafe`.
- `go_etcd_io_etcd_api_v3_etcdserverpb.md` (3h): stringers, sizes, getters.
- `go_etcd_io_etcd_pkg_v3_traceutil.md` (4b): `traceAt` from `EnsureTrace`/`Get`.

## Round 1 repairs (`reviews/3b-review-1.md`)

All 48 modules build; the snippets pass `go vet` and `gofmt`.

**F1, an empty `RangeEnd`.**
- The `nil`-slice request to W0 is withdrawn. W0 is now asked for the review's option (a): the
  request predicates read the end slice as mvcc does. A `nil` end is `[]` (the key alone); a
  non-`nil` empty end is `[0#8]` (from the key on). This is `req/..._api_v3.md`, "from 3b",
  rewritten.
- The specs keep W0's `KeyRange`.
- `Count.spec`'s premise is gone: its raw slice is read the same way (`endOf`).

**F2, keys-only sorting.** `rangeOut`'s fast keys-only path now clears values as well as leases
before the filter and the sort, which is 3e's `keysOnlyM`. `assemble` clears values anyway, so the
answer and `rangeOut_answers` are unchanged.

**F3, `checkRange`/`checkTxn`.** Both are now stated only at a read transaction (`.read σ`), the
only kind Go passes. Their errors are `txnRevErr σ.kv`.

**F4, 3e's API.** My provisional mvcc slots are gone. The specs now cite:
- 3e's `Mvcc.isMvcc`, `mvccState` over `MvccState` (answers at `σ.kv`), `mvccReaders γ 1` (in place
  of the thread token), `mvccTxn tx γ tr k` with `MTxn`, `mvccLessorIs`, `mvccBackend`;
- 3e's `txnStore`, `putLs`, `delsLs`.

Writes:
- They take their caller's update **pinned at `σ₀`** (`σ₀.pending = []`) and nested as 3e's commit:
  notify with the request's events, plus the history receipt `⧖`, then the bump, then `Q`.
- 3e's `Txn.End` asks `σ = σ₀`, which only the store's sole writer can assert, so `Put` and
  `DeleteRange` are pinned too; this is noted to 3e.
- An error (before or after the write transaction began) commits nothing and gives the update back.

The writer's resources are the storage's share plus a transparent bundle, `txnWriter B Pk Post`:
3e's hook run and the way back to `Pk`.
- On success the caller gets `Post`.
- On an error before the write transaction, it gets the bundle back.

The trace follows 4b's API:
- the caller lends its context's trace (`TraceUtil.ctxTraceIs ctx o` and `ctxTraceOwn o`);
- `EnsureTrace` keeps a non-empty trace;
- the caller gets back the returned one (`traceBack o tr`);
- internal specs take `ctxTraceIs ctx (some tr) ∗ traceOwn tr`.

**F5, `errIs`.** `errIs` is now transparent: the value of the sentinel's package variable
(`globalAddr <sentinel> ↦□ err`), `False` for other errors. `errIs_ne_nil`/`errIs_agree` follow from
the packages' initializations. The same mapping is given to 2c and 3a in `req/` (etcdserver's and
apply's files, "from 3b"), and 3e is asked that its context error be none of the sentinels.

**Second tier:**
- S1: the snippets cite 3e's `mvccState_reachable`.
- S2: new snippets:
  - `ReqRangeSortedKeysOnly`: a keys-only range sorted by descending mod revision, with a filter;
  - `ReqApplyDeletePrevKv`;
  - `ReqApplyTxnCheckFails`: a dead lease in a transaction, so nothing is written and the sentinel
    is returned;
  - `warn.go` (`ReqWarnReadOnly`, `ReqWarnApply`): the warning calls as the request path and the
    uber applier make them.
- S3: the lessor's state after a write is exact, by `evsLs` (3e's steps). `sameLeases` is gone.
  The premise is the code's need, `leasesLive`. The attachment invariant `attached` stays as 3a's,
  with the law `attached_evsLs`.
- S4: `DeleteRange` no longer takes the lessor handle.
- S5: `txnSafe`'s docstring says it is a state-free sufficient condition, and names the exact one
  as the margin.
- S7: `rangeAll`'s docstring is fixed.

**Open after round 1:**
- S6, for 3a/2d: the pin needs the apply thread to hold an authority over the store's state, while
  2c's reads fire their updates over the same `mvccState` concurrently. 3a's draft holds the store's
  state exclusively (`kvSt kv h`), which would leave 2c's readers no update to fire. That
  composition is 3a's and 2d's.
- S8: zap's `Error` of any error value is W0's (`zap/Api.lean`).
- From 3e (`req/..._storage_mvcc.md`, "from 3b"):
  - a record's lease fits `int64` (`kvFits` for `compareKV`);
  - `Mvcc.traceOwn` is to be identified with 4b's `TraceUtil.traceOwn`.
