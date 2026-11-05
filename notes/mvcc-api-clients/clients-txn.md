# etcd's `txn` package over mvcc's API (round 16): the restated specs (draft, 2026-11-03)

The draft in Lean: `/home/ubuntu/.claude-D/jobs/e4ba2bf8/tmp/clients/txn/TxnSpecs.lean` (scratch, outside
the repository; names under `txn.api.*`, beside today's `txn.*`; adopted, the prefix goes and each
replaces today's spec in its file). **It typechecks** against branch `mvcc-api` at `d810bc697a`
(round 16; `lake env lean FILE` from the worktree: no error, no warning but Lake's "manifest out of
date"), with three pure lemmas proved: `srvPre_stateOk` (the sort's premise from `Txn.Range`'s
`stateOk`), `kvSortOk_nonneg`, `pendItems_nil`. No repository file edited.

Updated for rounds 15-16 and the cross-review `xreview-clients.md` (§4, §10, §11):
- every size premise is gone: `VersOk`, `RunSmall`, `WriteSmall`, `StateSmall`, `TxnPreA`'s write
  conjunct, `executeRange`'s `sortSmall` premise (§2);
- `commitAU` now has `Txn.End`'s exact shape, with the notify receipt `⧖ (logCh (σ.log ++ [pend]))`
  passed to the caller (round 16): txn must not drop it, the server keeps it;
- `txn.kvOk` unified with the API's `kvSortOk` (§2).

(Earlier correction, kept: `Write`'s `⌜σ.pending = none⌝` and `End`'s `⌜σ = σ₀⌝` are mvcc's promises to
the client; only `Txn`'s read-then-write pin is the caller's.)

## 1. The shape

Every entry point (`Range`, `Count`, `Put`, `DeleteRange`, `Txn`) is logically atomic: it takes the
caller's updates in the API's exact shapes and passes them to mvcc's contracts.

| Name | What |
|---|---|
| `readAU γ Q` | `KV.Read`'s update (state unchanged, `COMM Q σ`) |
| `beginAU γ R` | `KV.Write`'s (mvcc promises `pending = none`; the caller gives `R σ`) |
| `commitAU γ σ₀ pend Q` | `Txn.End`'s two nested updates (mvcc promises `σ = σ₀` and gives the notify receipt, then the commit) |
| `csA P f Pre Q Post` | today's `csContract` over `hookRun` (covers a `nil` hook); the server's `csContractA` is the same: one definition, beside `hookRun` in the API (xreview §8) |
| `kvBackend γ q B P f` | `mvccBackend γ q B P ∗ hookIs B f` |
| `putAU`, `delAU` | the begin update whose `COMM` carries the lessor facts and the commit updates for `putPend o σ₀` / `delPend o σ₀ ok` |
| `txnBeginAU γ log t Qw` | `Txn`'s write updates: begin with the pin `σ.log = log`, then commit of `txnChs log t` |
| `mstate k`, `MTxn.append`, `MTxn.isRead` | a transaction's read state; its kind after changes |
| `Reach σ` | what txn records at an update (`mvccState_reachable`), carried to the internal specs |

Per spec (18 files, plus `sortRangeResults`, §2):

- **`Range`, `Count`, `Txn.specRead`**: `readAU γ Q`; post `∃ σ, Q σ ∗ ⌜Reach σ⌝ ∗` today's result at
  `σ.log`, `W64 σ.rev`, `σ.crev`. Gone: `storeReader`, the revision tokens, `idxCert log₀`, `certOk`,
  `crevLb`, every size premise (`sortOk`, `LogSmall`).
- **`Put`**: `putAU γ o L I R`, required only for a live lease (`decide (leaseID = 0 ∨ leaseID ∈ L)`);
  post `∃ σ₀, ⌜Reach σ₀ ∧ σ₀.pending = none⌝ ∗ Post ∗ R σ₀ ∗` (`ErrKeyNotFound`: `putPend = []`) or the
  response at `σ₀.log.length`. Gone: `revToken`, `storeWT`, `ownToks`, `idxCert`, `Pinned`, `certOk`,
  `wlogOwn`.
- **`DeleteRange`**: `delAU γ o I R`, commit updates for both outcomes (`∀ ok`); post `R σ₀ true` /
  `R σ₀ false`.
- **`Txn.specSole`** (the apply thread, `log` known in advance): `readAU γ (fun σ => ⌜σ.log = log⌝ ∗
  Qr σ)` and, for a request that writes, a wand `∀ σ, Qr σ -∗ txnBeginAU γ log t Qw` applied after
  `checkTxn` passed; a failed check or a read-only request returns `Qr σr`, a write `Post ∗ ∃ σw,
  ⌜σw.log = log⌝ ∗ Qw σw`. Premises kept: `leasesKnown`, `lessorUser … (leaseItemsOf (stateAfter
  log))`, `neverDone`, `TxnPreA log t` = `OpsOk` alone. Gone: `kvWriter`, `idxCert F`,
  `certOkNext`, `storeWT`, `hookOk`, `TxnPre`'s two size conjuncts.
- **Internal** (`checkRange`, `applyCompare(s)`, `compareToPath`, `getPrevKV`, `checkAndGetPrevKV`,
  `checkPut`, `checkTxn`, `executeRange`, `put`, `deleteRange`, `executeTxn`, `txn`): over `mvccTxn t
  γ trace k` (dispatch by `shapes.law`), the trace lent, plus `⌜Reach k.state⌝`; no size premise.

## 2. The sort's premise: from `Txn.Range`, no premise left

`executeRange` sorts the results of its own `Txn.Range` call, whose post (round 15) gives `stateOk
(stateAt k.readLog r')` for every `r'` with `k.state.crev ≤ r'` and `r' + 1 ≤ k.readLog.length`: at a
read transaction every revision from the compaction revision to its own, at a write transaction
also the pending one (`readLog = σ.log ++ [pend]`, read at `writeRev ≤ σ.log.length`). When the range
answers, `rangeRev` is in that interval (below it `ErrCompacted`, above it `ErrFutureRev`), and
`srvPre_stateOk : stateOk st → sortSmallA o st` (proved) gives the sort's premise. So the read path
and the write path need nothing from the caller.

**`kvOk` and `kvSortOk`.** `txn.kvOk` (`RangeModel.lean:190`) is `0 ≤ version ∧ 0 ≤ createRev ∧ 0 ≤
modRev`; round 16's `kvSortOk` is `0 < createRev ∧ 0 < modRev ∧ 0 < version`: **stronger**, not a
reordering any more. The direction every lemma needs is `kvSortOk → (≥ 0)` (`kvSortOk_nonneg`,
proved): the comparators (`kvSortBy{Create,Mod,Version}__Less`) need only values in `[0, 2^63)` for
Go's `(a - b) < 0` to be the signed order. Unification: delete `txn.kvOk`; restate `sortSmall` over
`kvSortOk` (`sortSmallA` in the draft) and `sortRangeResults.spec`'s premise (`Spec/.../txn/
sortRangeResults.lean:38`) over it (a stronger premise, but its one caller, `executeRange`, has it
from `stateOk`); the comparators' proofs use `kvSortOk_nonneg` where they now `unfold kvOk; omega`.
`stateAt_small` and `sortSmall_of_sortOk` (from `LogSmall`) have no user left in txn and go
(`stateAt_small` would not prove positivity anyway: its bound on revisions starts at `0`).

**`LogSmall`.** No txn spec needs it any more. The definition stays in `RangeModel.lean` for its
users outside txn (client/v3's `kmLog`/`idxCert_logOk`, `InvWatch`, the server's `KVLogOk.lean`), which
now get it from the notify receipt that `commitAU` passes to the server (`preceipt_lt`,
`receiptBound ≤ 2^62`). txn's own `ClientLaws.etcdState_revs` (from `LogSmall`) is client-model
vocabulary, not a txn spec premise.

## 3. The invariant txn keeps: none

txn allocates no ghost state and no invariant. Its one addition to the caller's updates is a
**wrapper** (per entry point, `aupd_intro`/`aacc_aupd_commit` of `Iris/BI/Lib/Atomic`): given `isMvcc
kv γ`, a caller's update with `COMM X σ` becomes the update passed to mvcc with `COMM X σ ∗ ⌜Reach
σ⌝` (txn opens the caller's update and applies `mvccState_reachable` to the `mvccState γ σ` in hand).
The receipt in `commitAU`'s notify step is passed through unchanged.

## 4. What the callers supply (the update builders)

**The apply thread (the sole writer).** Its invariant (the server's `kvStoreInv`): `∃ σ, mvccState γ σ
∗ ghostVar γw ½ σ ∗ monoListAuth γl σ.log ∗ Model σ.log ∗ ⧖ (logCh σ.notifiedLog)`. Builders over it,
with the apply thread's half as the private resource:
- `readAU` for `Range`/`Txn.specSole`: the halves agree, giving `σ.log = log` (the pin); `Qr σ`
  returns the half;
- the wand `Qr σ -∗ txnBeginAU …`, `putAU`, `delAU`: the begin agrees (pin, `pending = none`, the
  lessor facts `pendItems σ₀.log [] = I` by `pendItems_nil` and `Model`, `IgnoreLease`'s live lease);
  its `COMM` builds the commit updates from the half;
- `commitAU σ₀ pend`: the notification sets both halves to `σ₀.notify pend` and stores the receipt
  (`⧖ (logCh (σ₀.log ++ [pend]))`, which is `logCh` of the new notified log); the commit sets them to
  `commitPending`, extends `γl`, and re-establishes `Model` of `commitLog log pend` (today's
  `certOkNext` argument).

**The server's read path**: `readAU γ Q` with `Q σ := ⌜logR <+: σ.log⌝ ∗ (Model's persistent fact of
σ.log)`: the floor from a `γl` fragment, replacing `idxCert log₀`/`idxCert_join` and `certOk`. No
`VersOk`, no `storeSmall` (`InvRead.lean:84`): the read path's size premises are gone with txn's.

## 5. API facts relied on

Contracts: `KV.Read`, `KV.Write`, `Txn.Rev`, `Txn.FirstRev` (`checkRange`), `Txn.Range`
(`rangeOutcomeC` and `stateOk`), `Txn.Put`, `Txn.DeleteRange`, `Txn.Changes` (`txn`'s `rev++`),
`Txn.End` (its notify receipt, passed on), `NewReadOnlyTxnWrite.spec`. Laws: `shapes` (dispatch at
`mvccTxn`/`isMvcc`), `persistent` (`isMvcc`, `hookIs`), `mvccState_reachable` (`Reach`). Pure
definitions of `ApiState`: `stateOk`, `kvSortOk`, `MvccState`, `MTxn`.

## 6. The mvcc-internal names the draft uses (for re-export into the API vocabulary, xreview §11)

Named in the draft's statements (exact list, by `grep` of `TxnSpecs.lean`):
- predicates: `mvcc.txnCtx`, `mvcc.neverDone`, `mvcc.errorfIs`;
- pure: `mvcc.Log`, `mvcc.Change`, `mvcc.stateAfter`, `mvcc.stateAt`, `mvcc.findKey`, `mvcc.applyChanges`,
  `mvcc.commitLog`, `mvcc.writeRev`, `mvcc.pendItems`, `mvcc.leaseItemsOf`, `mvcc.rangeRev`,
  `mvcc.logCh` (in `commitAU`, as `Txn.End`), `mvcc.limitOf`, `mvcc.takeLimit` (the last two in
  `srvPre_stateOk`'s proof only).

Reached through the txn definitions the statements use (`txn.rangeResult`, `txn.prevKvIs`,
`txn.respsIs`, `txn.isTxnLessor`, ...):
- `mvcc.kvPtrIs` (`InvStore.lean:5063`: a `*KeyValue`'s points-to, in `rangeResult`, `prevKvIs`; also
  inside the API's own `rangeOutcomeC`);
- `mvcc.isLessor` (`InvStore.lean:1716`, inside `txn.isTxnLessor`);
- the Go names `mvcc.RangeResult`, `mvcc.RangeOptions`, `ErrCompacted`, `ErrFutureRev` (generated:
  not internals).

Not mvcc's (no re-export): `rangeIn`, `kvFilterOk`, `EtcdKv`, `OpFull` (`cache/v3/InvEtcd.lean`);
`lease.leaseOwn`, `lease.lessorUser`, `lease.ErrLeaseNotFound`; `traceutil.*`.

**The shared lemma** (txn and the server), for `ApiState`:
`theorem pendItems_nil (log : Log) : pendItems log [] = leaseItemsOf (stateAfter log) := rfl`
(checked in the draft).

On adoption, txn's own vocabulary modules (`InvRange`, `InvTxn`, `Write`, `Defs`) must import only
the API: today they import `InvStore`, `KVView`, `InvWatchStore`, `InvRoTxn` for the definitions
above and for the predicates that go (`isTxn`, `twWrap`, `isRoTxnWrite`, `isWatchableStore`,
`writerPin`, `idxCert`, `storeWT`, `putMax`).

## 7. Gaps

| Gap | Status |
|---|---|
| txn 1: `shapes.law` missing | **closed** (restored, xreview §10) |
| txn 1a: the write path's size (`WriteSmall`), the read path's versions (`VersOk`) | **closed** by `Txn.Range`'s `stateOk` (rounds 15-16; §2) |
| 2. callers hold `threadTok` | the server's (xreview §8: every caller holds one) |
| 3. `W64 σ.rev` vs `W64 (log.length - 1)` | a pure rewrite at `2 ≤ length` |
| 4. the hook `f : GoFunc`, a `mvccBackend` share in apply's environment | the server's (`AEnvA`) |
| 5. unused updates | designed out (`Put`'s only for a live lease, `Txn`'s by a wand); `DeleteRange`'s `∀ ok` builds a no-change commit the apply thread never fires |
| 6. pure lemmas for the proofs | a write transaction reads `pendState σ.log pend`; `rangeRev` in `[crev, readRev]` when a range answers (for `srvPre_stateOk` at `Txn.Range`'s interval) |
| 7. mvcc definitions re-exported | §6 |

Nothing left that the API cannot meet: no statement needed from it beyond round 16.

## 8. Superseded during the migration (2026-11-05, decided by the coordinator)

The proofs found four statements unprovable as frozen (`notes/mvcc-migration/txn.md`, gaps A-D).
Decided by the coordinator, 2026-11-05:
- **B** (this draft): `checkRange.spec` takes `⌜txn.Reach σ⌝` (the code compares with `FirstRev()`'s
  `W64 σ.crev`, which is `σ.crev` only for a reachable state);
- **D** (this draft): `txn.spec` takes `ro = false → σ.pending = none` in place of `σ.pending = none`
  (`Txn` runs `txn` on the read-only wrapper of a read transaction, whose state may have a pending
  revision; `txn`'s proof never used the premise);
- **A, C** (the API, the mvcc track): `KV.Range`/`Txn.Range` posts give `⌜LogWf' log ∧ ∀ cs ∈ log,
  cs.length < 2 ^ 63⌝` of the read log (the model's theorem relating the index's answers to the
  state needs it); `Txn.Changes` gives `⌜0 ≤ sint.Z chs.len⌝` (`executeTxn`'s signed `len(..) > 0`).
- **E** (this draft): `getPrevKV`, `checkAndGetPrevKV`, `checkPut` and `checkTxn` give the trace back
  as `∃ te', ownTrace trace te'` (`getPrevKV` reads inside `Trace.StepWithFunction`, which gives back
  `∃ e'`). *Superseded*, decided by the coordinator, 2026-11-05: traceutil's StepWithFunction keeps
  the flag (`f` and its post give back `ownTrace t e`; `isEmpty` is written only at a trace's
  creation), so the four posts give `ownTrace trace te` again, as this draft had them; with it
  `executeTxn`'s gap E′ placeholder is gone;
- **F** (the API, the mvcc track): `Txn.DeleteRange`'s post gives `⌜LogWf' (σ.log ++ [pend]) ∧ ∀ cs ∈
  σ.log ++ [pend], cs.length < 2 ^ 63⌝` (`deleteRange` without `PrevKv` reads no range).
`TxnSpecs.lean` is updated for B, D and E.
