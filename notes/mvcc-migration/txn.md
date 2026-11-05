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

**Gap C (the API too weak; blocks `executeTxn`).** `executeTxn` computes a range's header revision
as `txnWrite.Rev()` plus one when `len(txnWrite.Changes()) > 0` (`txn.go`, a signed `GoGt go.int`
on the slice's length). `Txn.Changes.contract` gives only `uint.nat chs.len = k.pend.length`, no
ownership of the slice: a length `≥ 2 ^ 63` (negative as an `int`) is not excluded, and nothing
bounds a write transaction's pending changes (deletes are of the index's keys, unbounded without
the receipts). Until M1 the internals' `Changes` spec returned the slice's points-to, so
`ownSlice_len` gave `0 ≤ sint.Z chs.len`. (`txn` itself tests `len(..) == 0`, which `uint.nat`
decides: proved.)
*Minimal fix* (the API): `Txn.Changes.contract`'s post `⌜uint.nat chs.len = k.pend.length ∧
0 ≤ sint.Z chs.len⌝` (true of every Go slice; the implementation has the slice's points-to).

**Gap D (the draft too strong a premise; blocks `Txn`'s read-only paths).** `txn.txn.spec` requires
`σ.pending = none` for either kind (`ro = true` too), but `Txn` calls `txn` on the read-only
wrapper of a read transaction whose state comes from `KV.Read`'s update, which says nothing of
`pending` (a read may see a pending revision: it is not visible to reads). Neither `specSole`
(its read-only branch) nor `specRead` can supply it. `txn`'s own proof never uses the premise.
*Minimal fix* (the draft): `txn.spec`'s `σ.pending = none` conjunct as `ro = false → σ.pending =
none`, or dropped. `Txn.lean`'s proof is complete but for these two obligations, each a `sorry` marked
`M1-REPLACE: gap D` (the coordinator's go-ahead for placeholders, 2026-11-05); with the fix each is
dropped.

## Left

- **`Link.lean`, `Results.lean` do not build** (the only txn modules that do not). `Link.lean` is
  generated (`etc/gen-link.py --txn` from `etc/link-lean-first-txn.txt`, outside this package's
  paths): the txt must list the new hypotheses, in order, per proof (below); the API's laws
  (`mvcc.api.shapes.law`, `persistent.law`, `mvccState_reachable.law`) and `mvcc.api.
  NewReadOnlyTxnWrite.spec` are not functions of the txt's form: the script needs a way to pass
  mvcc's law proofs (mvcc's Link). `Results.lean` restated the sole writer's results over
  `soleWriter`/`kvWriter`: to redo over the new specs (or drop: the server's `KVStoreCore` holds
  the pin now).
- The placeholders: below; each closes when its gap's fix lands.

## Status per proof (every module of the package builds but `Link`, `Results`)

Proved over the API (no sorry): `put`, `checkAndGetPrevKV`, `checkPut`, `applyCompares`,
`compareToPath`, `checkTxn`, `txn`, `Range`, `Count`, `Put`, `DeleteRange`, and every proof with no
mvcc callee (the list in "Done"). `Txn` proved but for gap D's two `M1-REPLACE`s.

`M1-REPLACE` placeholders (whole proofs, `sorry`): `executeRange`, `getPrevKV`, `applyCompare`,
`deleteRange` (gap A), `checkRange` (gap B), `executeTxn` (gap C); the old proofs over the internals
are in the history (`645402be7a~1`), most of each reusable once the gap closes (`executeRange_core`
was already parametric in the transaction; `KindOk`/`prevKvIs_of_outcome`/`rangeOutcome_sel` are
over `MTxn` in `Write.lean`).

New `wp_proof` hypotheses (for `etc/link-lean-first-txn.txt`), in order:
- `put`: `shapes`, `traceutil.Get`, `Trace.AddField`;
- `checkAndGetPrevKV`: `getPrevKV`; `checkPut`: `checkLease`, `checkAndGetPrevKV`;
- `applyCompares`: `applyCompare`; `compareToPath`: `applyCompares`; `checkTxn`: `checkRange`, `checkPut`;
- `txn`: `shapes`, `newTxnResp`, `executeTxn`, `zap.Error`, `zap.Logger.Error`;
- `Range`: `shapes`, `persistent`, `mvccState_reachable`, `EnsureTrace`, `RangeSecObserve`, `executeRange`;
- `Count`: `Range`;
- `Put`: `shapes`, `persistent`, `mvccState_reachable`, `EnsureTrace`, `proto.Size`, `checkLease`,
  `checkAndGetPrevKV`, `put`;
- `DeleteRange`: `shapes`, `persistent`, `mvccState_reachable`, `EnsureTrace`, `deleteRange`;
- `Txn`: `shapes`, `persistent`, `mvccState_reachable`, `EnsureTrace`, `IsTxnReadonly`,
  `Trace.StepWithFunction`, `compareToPath`, `Trace.AddField`, `checkTxn`, `Trace.Step`,
  `mvcc.api.NewReadOnlyTxnWrite`, `txn`;
- placeholders: `executeRange`: `shapes`, `Get`, `rangeLimit`, `mkGteRange`, `filterRangeResults`,
  `sortRangeResults`, `Trace.Step`, `asembleRangeResponse`; `getPrevKV`: `shapes`,
  `StepWithFunction`, `context.TODO`; `applyCompare`: `shapes`, `context.TODO`, `mkGteRange`,
  `compareKV`; `deleteRange`: `shapes`, `mkGteRange`; `checkRange`: `shapes`; `executeTxn`:
  `shapes`, `Get`, `StartSubTrace`, `executeRange`, `StopSubTrace`, `proto.Size`, `getPrevKV`,
  `put`, `deleteRange`.

## Renamed and replaced (for the server track)

| Old (over mvcc's internals) | New |
|---|---|
| `txn.isKV kv s γ` | `mvcc.api.isMvcc kv γ` (`txn.isMvcc_shape`: its `isKV` contracts) |
| `txn.kvWriter s γ log`, `txn.soleWriter`, `soleWriterOpen`, `soleBudget`, `mvcc.storeWT`, `storeWTs`, `idxCert`/`certOkNext` premises | none in txn: the caller's `mvcc.api.mvccState γ σ` in its invariant, given to txn as updates `txn.readAU γ (fun σ => ⌜σ.log = log⌝ ∗ Qr σ)` and `∀ σ, Qr σ -∗ txn.txnBeginAU γ log t Qw` (`Txn.specSole`), `txn.putAU`, `txn.delAU` |
| `txn.wlogOwn`, `wlogOwnW` | none (the watchable store's notified log is mvcc's, inside `mvccState`) |
| `mvcc.csContract P f Pre Q Post` + `mvcc.hookOk γ P f` | `txn.csA P f Pre Q Post` + `txn.kvBackend γ q B P f` (`mvccBackend γ q B P ∗ hookIs B f`) |
| `txn.TxnPre log t` | `txn.TxnPreA log t` (`OpsOk` alone) |
| `txn.Pinned`, `pinned_sole` | none (the pin `σ.log = log` is in the caller's updates) |
| `txn.txnViewIs`, `txnWriteIs`, `KindIs`, `mvcc.TxnKind` in txn | `mvcc.api.mvccTxn t γ trace k`, `k : mvcc.api.MTxn`; `txn.mstate k`, `txn.MTxn.isRead`, `txn.MTxn.append` |
| `txn.kvOk` | `mvcc.api.kvSortOk` (`txn.kvSortOk_nonneg`) |
| `txn.sortOk`, `stateAt_small`, `sortSmall_of_sortOk`, `srvPre_small` | `txn.srvPre_stateOk` (from `Txn.Range`'s `stateOk`); `txn.sortSmall` now over `kvSortOk` |
| `txn.Txn.specSole`'s `F`/`idxCert`, `specRead`'s `m`/`log₀`/`LogSmall` premise | the read update's `Q σ`; post `∃ σ, Q σ ∗ ⌜txn.Reach σ⌝ ∗ ..` |
| `txn.Range.spec`, `Count.spec` (`storeReader`, tokens, `idxCert log₀`, `sortOk`) | over `readAU γ Q`; post `∃ σ, Q σ ∗ ⌜Reach σ⌝ ∗ rangeResult .. σ.log (W64 σ.rev) σ.crev ..` |
| `txn.Put.spec`, `DeleteRange.spec` (`m`, `log₀`, `Lw`, the `Hsole`/`HIp`/`Hcok` premises) | `putAU γ o L I R` (only for a live lease) / `delAU γ o I R`; post at `∃ σ₀, ⌜Reach σ₀ ∧ σ₀.pending = none⌝ ∗ R σ₀ ..` |
| `KindOk`, `kindState` over `TxnKind` | the same names over `MTxn` (`Write.lean`) |
| `Writer`, `KVWrite`, `KeyObs`, `SoleWriterKV` modules | empty modules importing `ApiLemmas` (their content obsolete) |
| (new) | `txn.readAU_reach`, `beginAU_reach`, `end_read`, `end_write`, `mvccTxn_shape`, `isMvcc_shape`, `reach_len` (`ApiLemmas.lean`) |

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
