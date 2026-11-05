# etcd's `txn` package onto mvcc's API (strict M1): hand-off

Branch `mvcc-api`. The task: txn's specs restated as `notes/mvcc-api-clients/TxnSpecs.lean` drafts
them (frozen), its proofs over the API's contracts and laws, no mvcc internal imported.

## Done

- **The specs** (commit `645402be7a`): the 18 spec files of the draft (`Range`, `Count`, `Put`,
  `DeleteRange`, `Txn` = `specSole ∧ specRead`, `checkRange`, `applyCompare`, `applyCompares`,
  `compareToPath`, `getPrevKV`, `checkAndGetPrevKV`, `checkPut`, `checkTxn`, `executeRange`, `put`,
  `deleteRange`, `executeTxn`, `txn`), verbatim but for the prefix (`txn.api.X` is `txn.X`); the
  comparators' and `sortRangeResults`' premise over `mvcc.api.kvSortOk` (`txn.kvOk` deleted). Every
  `Spec/.../txn/` module builds.
- **The vocabulary**: `Proof/.../txn/ApiVocab.lean` (the draft's `mstate`, `MTxn.isRead`,
  `MTxn.append`, `Reach`, `putPend`, `delPend`, `TxnPreA`, `txnChs`, `readAU`, `beginAU`,
  `commitAU`, `csA`, `kvBackend`, `putAU`, `delAU`, `txnBeginAU`, `srvPre_stateOk`; `txnRespShell`
  moved there from the old `Spec/.../txn/txn.lean`, where it was a layout violation).
  `TxnRun.sortSmall` is the draft's `sortSmallA` (kept the name); `RangeModel.kvSortOk_nonneg`; the
  draft's `pendItems_nil` is the API's own `mvcc.api.pendItems_nil` (not duplicated).
- **Imports**: txn's vocabulary modules import, of mvcc, only `Spec/.../mvcc/Api.lean` and
  `ApiState.lean` (`Base`, `Lemmas`, `Defs`, `InvTxn`, `SoleWriter`, `Write`). Deleted with the
  internals they were written over: `isKV`, `wlogOwn(W)`, `storeWTs`, `putMax_ge` (`Defs`);
  `soleWriter*`, `soleBudget` (`SoleWriter`, pure `soleLog` kept); `Pinned`, `pinned_sole`,
  `storeTxnWriteIs_pinned`, `isTxnWrite_*`, `isTxn_kindOk`, `isTxn_crev` (`Write`); `txnViewIs`,
  `KindIs`, `txnWriteIs`, `txnViewIs_*`, `isRoTxnWrite_pure`, `kindOk_read`, the trace accessors,
  `sortSmall_of_sortOk` (`InvTxn`); `TxnPre` (`TxnRun`); `sortOk`, `stateAt_small`, `kvOk`
  (`RangeModel`); `kvOk_kvRead`, `srvPre_small`, `isTxnRead_pure/_cert` (`RangeLemmas`).
  `LogSmall`/`logChanges` stay (the server's draft uses them). `KindOk`/`kindState` are now over
  `MTxn` (`Write.lean`), with `prevKvIs_of_outcome`/`rangeOutcome_sel` over them.
- **Proofs that build** against the new vocabulary (no mvcc callee): the comparators, `kvSort*`,
  `sortRangeResults`, `filterRangeResults`, `mkGteRange`, `rangeLimit`, `pruneKVs`,
  `asembleRangeResponse`, `newTxnResp`, `isNil`, `IsTxnReadonly`, `IsTxnSerializable`,
  `HasRevisionFilters`, `IsDefaultOrdering`, the `Warn*`/`warnOf*` and `*SecObserve` proofs,
  `checkLease`, `compareInt64`, `compareKV`, `ClientLaws`, `HistoryLaws`.

## Found: statements that cannot be proved over the frozen API/draft

**Gap A (the API too weak; blocks `executeRange`, `getPrevKV`, `applyCompare`, `deleteRange`).**
`Txn.Range.contract`'s post gives the outcome as `rangeOutcomeC r err k.readLog k.readRev ...`,
which is over mvcc's *index answers* (`rangeAnswers`/`rangeTaken`/`rangeTotal` of the log). Every
txn statement is over the *state* (`rangeResult`: `srvRangeOk o (stateAt log r) ..`,
`srvCount o (stateAt ..)`, `prevKvIs r (mstate k) key`, `delChanges (pendState ..)`). The bridge is
the model's main theorem (`mvcc.kiGet_indexOf`, through `txn.rangeAnswers_stateAt`,
`taken_stateAt`, `delKeys_client`), which needs `LogOk k.readLog`: `LogWf` of the read log and
**every revision's change count below `2 ^ 63`** (the index's sub-revisions are `w64`; without the
bound the index's answers are not the state's). Until M1 the internals gave it (`idxCert`'s pure
part, `isTxn_kindOk`). Over the API nothing does: `txn.Reach` (`MvccReachable σ`, the length bound)
gives `LogWf'` of `σ.log` (`reach_logWf`) but no change count, and nothing at all of a write
transaction's pending revision; `stateOk` bounds states, not revisions.
*Minimal fix* (the API, where the round-15 decision (D) put the range's size facts): `Txn.Range`'s
post (and `KV.Range`'s, for the same reason, at `σ.log`) also gives
`⌜LogWf' k.readLog ∧ ∀ cs ∈ k.readLog, cs.length < 2 ^ 63⌝` (what `isTxn_kindOk` proved from the
internals, so the implementation has it). With it `KindOk k` follows (`LogWf.of_wf'`, the length
from `Reach`), and the four proofs go through as before.

**Gap B (the draft too weak; blocks `checkRange`).** `txn.checkRange.spec` takes
`mvccTxn t γ trace (.read σ)` and no `⌜txn.Reach σ⌝`, but its post `checkRangeErr (W64 σ.rev)
σ.crev o err` compares the request's revision with `σ.crev : Int` while the code compares it with
`rv.FirstRev()`, `W64 σ.crev` (`Txn.FirstRev.contract`): equal only for `σ.crev` in `w64`'s signed
range, which nothing gives (`mvccTxn` is opaque; no law gives its state reachable).
*Minimal fix* (the draft): add `⌜txn.Reach σ⌝` to `checkRange.spec`'s precondition, as every other
internal spec has; its one caller, `checkTxn`, holds it. (Or an API law
`mvccTxn t γ trace k ⊢ ⌜MvccReachable k.state⌝`.)

## Left

- The proofs over the API (each `wp_proof` taking the API's laws/contracts as hypotheses):
  see "Status per proof" below.
- `Link.lean` is generated (`etc/gen-link.py --txn` from `etc/link-lean-first-txn.txt`, outside
  this package's paths): regenerate once the `wp_proof` hypotheses settle.
- `Results.lean`, `SoleWriterKV.lean`, `KVWrite.lean`, `KeyObs.lean`, `Writer.lean`: over the old
  internals (the sole writer's tokens, `kvWriter`); obsolete over the API (the pin is the
  caller's), to delete or restate with the server track.

## Status per proof

(updated below as the work goes)

## What txn needs re-exported through the API's vocabulary (draft §11)

Named in txn's statements and reached today only through `Api.lean`'s public imports of mvcc's
internals: `mvcc.txnCtx`, `mvcc.rangeCtx`, `mvcc.txnCtx_rangeCtx`, `mvcc.neverDone`,
`mvcc.errorfIs` (and `errorfIs_ne_nil`), `mvcc.isLessor`, `mvcc.kvPtrIs`, `mvcc.kvIs`,
`mvcc.rangeRev`, `mvcc.rangeOutcome(C)` and `rangeKvs` (inside `Txn.Range`'s contract),
`mvcc.Log`, `mvcc.Change`, `mvcc.stateAfter`, `mvcc.stateAt`, `mvcc.findKey`,
`mvcc.applyChanges`, `mvcc.commitLog`, `mvcc.writeRev` (`writeRev_lt`, `stateAt_writeRev`),
`mvcc.delKeys` (`delKeys_eq`), `mvcc.pendItems`, `mvcc.leaseItemsOf`, `mvcc.logCh`
(`logCh_snoc`), `mvcc.limitOf`, `mvcc.takeLimit`, `mvcc.rangeAnswers`/`rangeTaken`/`rangeTotal`
and the model's theorem behind `rangeAnswers_stateAt` (`kiGet_indexOf`), `mvcc.LogWf`/`LogWf'`
(`LogWf.of_wf'`), `mvcc.stateAt_sorted`, `mvcc.inRange`, `mvcc.mvccInit` (the package's facts:
`ErrFutureRev`, `ErrCompacted`), mvcc's `IsPkgInit` instance (today in `mvcc/Base.lean`), and the
Go names `RangeResult`, `RangeOptions`, `ErrCompacted`, `ErrFutureRev`.
