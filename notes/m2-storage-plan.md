# Plan: M2, the storage side (spec-first; branch `m2-storage`)

Status (2026-10-30): **item 17 switched with the lease** ("Item 17 switched: the jobs' share
leased", the last section: 17, item 4's step-2 text, 20, 23, 24 real; item 31 stopped, its `none`
arm needing a nil-hook `SetScheduledCompact` no approved text states). Before: **the approved items switched** ("The switch of the approved items", the last
section: 1-13, 19, 26, 28, 29's pure vocabulary, 34, 35 and item 4's supply line real; item 17
stopped, not provable as drafted (non-atomic loads), with 4's step-2 text, 20, 23, 24 and 31; 14, 27
and 29's backend part waiting with the restore chain). Before: **review round 4 repaired** ("After review round 4", the last section: A1 by
evidence (the records' reads proved; today's index invariant shown false over a compacted image,
repaired as `IdxCRepN` with readers unaffected, proved; round 3's bucket shape refuted, the job's
`entsCutAt` in its place; the rebuild's pure theorem stated, not proved; two more facts found: the
writer's receipts, Q8, and the view's widening); A2 by the backend's nil arm (`bt_lockInNil`
proved); Q7's premise drafted at the request and the committed log; the Q2 list at 37 items, marked
approvable now or waiting). Before: **review round 3 repaired** ("After review round 3", the last section: the
image's compaction records and the generalized `store.restore`, the scheduler's payload, the second
tier; the Q2 list complete at 26 items; Q7 for the user: Q5 (a) fails in a `Compact(0)` corner). Before:
**step 2 drafted** ("Step 2: restore in compaction mode", the last section:
the restorable compaction right, `Restore.specM` by the mode with off-mode laws, the supply as one
stock per backend, D22's statements drafted for the collaborator, Q4-Q6 for the user, a Go liveness
bug recorded). **Step 1 on the merged `lean` done** ("Step 1 on the merged lean": Supply repaired,
N1 drafted end to end, F2 dropped, the Q2 list). Earlier: **Draft** written and checked (`fe466ad8d5`; full `lake build` passed, 10957 jobs, no error); internal repairs made; for the
user: the drafted statements below and the questions at the end. Q1 answered **(a)** and drafted
("Q1 (a), drafted", below; `mvcc/M2StorageDraftSupply.lean`; `12343a4cc9`, full `lake build` passed,
10958 jobs, no error); review round 1 (`notes/spec-first-study/m2-storage-review-1.md`) answered and
repaired ("After review round 1", below: F1 and F2 by the user's decisions, drafted; S1-S10 each
fixed or rejected); Q2 open. M2's plan is `notes/m2-plan.md` on
branch `m2`; the findings this step answers are the backend-cmp Probe's
(`notes/spec-first-study/backend-probe.md`: P3, S1, S2, S3; P4 as decided).

## Scope (the user's, 2026-10-30)

- **Only the storage side**, below the apply loop: the auth-mode merge has not landed for the apply
  loop (`applyEntries`, `apply`, `applyAll`, `run`, `start`, `applyEntryNormal` still have
  `spec`/`specOn`). Not touched: the apply loop's specs, `apply.dispatchOk`,
  `applierV3backend.Compaction`, the request path, the `m2` branch.
- **P4**: in compaction mode the server keeps the no-snapshot bound as a premise (no snapshot restore
  while compacting); the multi-member gap (a follower installing a snapshot while compaction runs)
  is a stated scope limit.
- The items: (1) P3, `newWatchableStore`/`New` in compaction mode return the compaction right's
  half beside the closer instead of freezing, with "no watchers in compaction mode", the closer
  given up only after `NewServer`'s last error return; (2) `server_kv_watchable_of` at `cm = true`;
  (3) boot keeps `srSlot` and `fkV`, a law `srSlot` to `kbSRM (some d)`; (4) `writerOwn` at
  `2 + nJobRd`; (5) `kbWTSupplyM`: an allocation law, and its server source (R2-7), no-snapshot only.
- Out of scope: the etcd pin bump for `NoDelPutAt` (#22377), the apply loop, `NewServer.spec`'s
  merge with `specCompact` (listed below: what each needs from this step).

## What was done

**Draft modules** (imported by nothing; no `axiom`, no `sorry`; checked with `etc/lean-check.py`):
- `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/M2StorageDraft.lean`: the drafted mvcc statements
  and their laws.
- `Proof/go_etcd_io/etcd/server/v3/etcdserver/M2StorageDraft.lean`: the server's glue over them.

**Internal repairs, switched** (decided by the agent; every statement reads as before at
`cm = false`):
- **(4) `mvcc.writerOwn γ := storeRT γ ∗ retiredAt γ (2 + nJobRd γ.kb)`** (was `retiredAt γ 2`),
  with `writerOwn_off : nJobRd γ.kb = 0 → writerOwn γ ⊣⊢ storeRT γ ∗ retiredAt γ 2`. A compacting
  store's pool starts its retired count at `nJobRd = 1` (the job's reader), and the server retires
  two (the storage-version monitor's, the writer's): `3 = 2 + nJobRd`. Options were this or taking
  the job's reader out of the count (`NewStore`'s statement, the readers' pool's invariant); this
  is one definition and two proof sites (`store.Restore`, which is never in compaction mode, and
  `NewServer`, at `{ d with cm := false }`).
- **(3) `bootBackend_of_newPost`** (etcdserver, internal) also returns `backend.fkV γ true`
  (`mvcc.bkNoCmp_fkV_of_fkCl` in place of `bkNoCmp_of_fkCl`); it already returned `srSlot`.
  `NewServer`'s proof names both (`HfkV`, `HsrS`) instead of dropping them, and drops them at
  `mvcc.New`, whose store does not compact yet.
- **(3) `mvcc.kbSRM_some : backend.srSlot d.be ⊢ kbSRM (some d)`** (`mvcc/InstanceLaws.lean`), in
  either mode (no `cm` premise needed).
- **(5) `mvcc.kbWTSupplyM_alloc (d) (n) (h : receiptBound GF ≤ n + 1) (E) : ownToks d.γB.wb n ⊢
  |={E}=> kbWTSupplyM (some d)`** (`InstanceLaws`): a receipt-backed invariant
  (`∃ a m, ⧗ a ∗ ownToks d.γB.wb m ∗ ⌜receiptBound GF ≤ a + m + 1⌝`, as `srvWTPool`). The bound is
  the law's: a non-server creator holding the `wbInit - 2` tokens `NewStore` leaves needs
  `receiptBound GF ≤ 2^40 - 2`, stronger than the stores' `receiptBound GF ≤ 2^48` (Probe S1's
  "~2^40 vs 2^48"); the export's docstring should name it when a client uses the law.

## The drafted statements (for the user's review)

None is switched: `New.spec`, `newWatchableStore.spec` and `watchableStore.NewWatchStream.spec` are
linked (`mvcc/Link.lean`), and `New.spec` is a callee of `NewServer`'s trusted proof.

**(1) The mode-gated facts** (new mvcc definitions):
```lean
def mvcc.wsFrozenM (γs : mvcc.StoreNames) : IProp GF :=
  if mvcc.kbCmpM γs.kb then iprop(True) else mvcc.crevFrozen γs
def mvcc.crevRightM (kb : Option mvcc.KBReal) (γs : mvcc.StoreNames) : IProp GF :=
  if mvcc.kbCmpM kb then mvcc.crevUB γs.idx (1 : Qp).half (-1) else iprop(True)
def mvcc.wsWatchFrozen (γ : mvcc.WsNames) (σ : mvcc.WsState) : IProp GF :=
  iprop(⌜σ.M = ∅⌝ ∨ mvcc.crevFrozen γ.st)
```
**`isWatchableStore`** (internal, redefined in place at the switch; drafted as
`isWatchableStoreD`): its conjunct `"#Hfrz" ∷ crevFrozen γ.st` becomes
`"#Hfrz" ∷ mvcc.wsFrozenM γ.st`; nothing else changes. `isWatchableStoreD_off` proves it equal to
today's at `¬ kbCmpM γ.st.kb`. **`watchStoreInv`** (internal) gains `wsWatchFrozen γ σ`: no watcher,
or frozen (initially no watcher: `wsWatchFrozen_init`).

**`newWatchableStore.spec`** (drafted `newWatchableStore.specD`): the post's `isWatchableStore s st γ`
reads over the redefined predicate, and the post gains one conjunct after the inner closer:
```lean
      mvcc.storeCloser st γ.st ∗ mvcc.crevRightM kb γ.st ∗
```
**`New.spec`** (drafted `New.specD`): the same, beside the closer:
```lean
        mvcc.wsCloser s st γ.st ∗ mvcc.crevRightM kb γ.st ∗
```
Pre unchanged in both by P3 (they already take `kbSRM kb` and keep `nJobRd kb` readers back);
since Q1 (a) both lose `kbWTSupplyM kb` (below). At `cm = false` (`¬ kbCmpM kb`) the new conjunct is `True` (`crevRightM_off`) and the predicate
is today's: the statements read as today.

**`watchableStore.NewWatchStream.spec`** (drafted `NewWatchStream.specD`; "no watchers in compaction
mode", round 1's persistent "no compactor" fact): the pre gains `mvcc.crevFrozen γ.st`:
```lean
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ mvcc.crevFrozen γ.st }}
```
(post unchanged). An off server has it: `isWatchableStoreD_frozen : ¬ kbCmpM γ.st.kb →
isWatchableStoreD s st γ ⊢ crevFrozen γ.st` (a law, so no client unfolds the predicate).

**The glue, proved:**
- `mvcc.crevRight_split` (`γs.kb = kb → crevUB γs.idx ½ (-1) ⊢ |={⊤}=> wsFrozenM γs ∗ crevRightM kb
  γs`): `newWatchableStore`'s one changed step (in place of `crevFrozen_alloc`). A copy of
  `newWatchableStore`'s proof with it elaborated up to the lease deleter `rdIs`, whose
  `watchableStore.Write.spec` takes today's `isWatchableStore` (a different name in the Draft; the
  same predicate after the in-place switch). Not kept.
- `mvcc.compactRight_of_wsCloser (h : kbCmpM kb) : wsCloser s st γs ∗ crevRightM kb γs ==∗
  compactRight γs (-1) ∗ storeStop st γs`: the step `NewServer` takes **after its last error
  return** (the transport's `Start`, `server.go:429`; Go's deferred `newSrv.kv.Close()` closes the
  store on any earlier error, and `v3compactor.New`'s error at `:385` is one of them). It gives up
  the watchable store's own stop channel and waiter: a compacting store is never closed.
- `server_kv_watchable_ofC` (etcdserver): `server_kv_watchable_of` at `hcm : d.cm = true`, over
  `New.specD`, the compacting bridge `storeBackend_of_backendC` (the registration fixed by
  `backend.dlReg_fix` at `storeDlReg d.γB γi`), `fkV d.γB true`, `srSlot d.be` (through
  `kbSRM_some`), three more callee specs (since Q1 (a) no `kbWTSupplyM (some d)` premise)
  (`LockForSafeRangeDelete`, `UnlockForSafeRangeDelete`, `UnsafePut`). Its post: the store at
  `γw.st.kb = some d`, `actualMaxReaders - 1 - 2` watch readers, `retiredAt γw.st 1`, the closer and
  `crevRightM (some d) γw.st`. **Gap**: it gives `watchWriter`/`writerFrag` and no `txn.isKV`, where
  `server_kv_watchable_of` gives `txn.kvWriter` and `txn.isKV`: both are defined over
  `isWatchableStore`, so they follow only after the in-place switch.
- `kbWTSupplyM_of_srvWTPool : srvWTPool E γp ∗ dghostVar E.γbe DFrac.discard d ⊢ kbWTSupplyM (some
  d)` (etcdserver): R2-7's conversion, from `srvWTPool_take_extra_d`.
- `newServer_compactRight`: `compactRight_of_wsCloser` at `some d`, `d.cm = true`.

**Decided by the agent** (internal predicates, layout):
- *The frozen fact gated by the mode inside `isWatchableStore`* (vs. moving it out of the predicate
  into `New`'s post as a separate conjunct): at `cm = false` the predicate stays today's, so its
  consumers (`syncWatchers`, the server's restore path) are unchanged there, and the "no compactor"
  fact is a law of it (`isWatchableStoreD_frozen`).
- *The mode is the logical names' (`γ.st.kb`)*, not the current backend's (`withPhys`): no restore
  in compaction mode, so it never changes.
- *The "no compactor" fact is `crevFrozen γ.st` itself* (vs. a new ghost token): persistent, already
  what an off server's store has, and exactly what `syncWatchers` needs.
- *The closer stays in `New`'s post; the caller makes the right* (vs. `New` returning `compactRight`
  and `storeStop`): Go's deferred `kv.Close()` needs the closer until `NewServer`'s last error.
- *`kbWTSupplyM_alloc` and `kbSRM_some` in `InstanceLaws`* (the instance's laws, a module few import).

## What the switch costs (when the statements are approved)

- mvcc: `isWatchableStore`'s definition (`InvWatchStore.lean`); `watchStoreInv` gains
  `wsWatchFrozen` (every proof that re-establishes it: `newWatchableStore`, `watch`,
  `cancelWatcher`, `syncWatchers`, `moveVictims`, `Restore`, ...: a frame, `M` unchanged or the fact
  in hand); `syncWatchers`' non-empty branch takes `crevFrozen` from the invariant
  (`watchableStore__syncWatchers.lean:181`, `:304`); `NewWatchStream`/`watch` keep the fact in the
  stream (`storeWatchParams` or `isWatchStream`); `newWatchableStore`'s proof (`crevRight_split`);
  `New`'s proof (frames `crevRightM`).
- Above mvcc: `NewServer`'s proof frames `crevRightM` (at `cm = false`, `True`); v3rpc's
  `watchServer.Watch` (the one caller of `NewWatchStream`) needs `crevFrozen` from the server's
  watch state (`srvWatchBuilt`), which an off server's `NewServer` gets from
  `isWatchableStoreD_frozen`.
- `RestorePre.restorePre_of_apply` (D22's) has a `sorry` for `crevFrozen E.γ` today: the
  `isWatchableStore` it holds has it (`Hfrz`); a law `isWatchableStore s st γ ⊢ crevFrozen γ.st`
  (today) or `isWatchableStoreD_frozen` (after the switch, with `srvEnvOk`'s `d.cm = false`) closes
  it without an unfold. For the collaborator.

## What the apply-loop side (and the merges) will need from this step

- **`NewServer.spec` merged with `specCompact`**: the store built at `cm := (retention ≠ 0)` instead
  of `{ d with cm := false }`; at `cm = true`, `server_kv_watchable_ofC` (switched to the real
  `New.spec`), its pre's `fkV`/`srSlot` from `bootBackend_of_newPost` (now kept), no supply (Q1 (a): `store.Compact` takes it);
  after the transport's `Start`, `newServer_compactRight`; the readers' hand-outs from
  `actualMaxReaders - nJobRd - 2` (one fewer); the retired count `1 + 2 = 3`, which `writerOwn` now
  accepts (`writerOwn_off` only at `cm = false`).
- **The server's state** (`srvBuiltG`, `apply.kvOwn` or `srvApplyKV`, D22's `srvKVCloser`): at
  `cm = true` the KV's closer is gone (made into the right), so `srvKVCloser` holds `compactRight
  γ c ∗ storeStop` instead, or is mode-gated; `srvEnvOk`'s `d.cm = false` becomes
  `d.cm = false ∨` the no-snapshot configuration (P4); the watch state (`srvWatchBuilt`) carries
  `crevFrozen` at `cm = false` only.
- **The apply's compaction arm** (`applierV3backend.Compaction` over `mvcc_store_Compact`): lends
  `storeRT` from `writerOwn` (`writerOwn_rt`, any count), passes `hookIs` (returned since P1) and
  `compactRight`, and needs `storeStop`; since Q1 (a) also the supply `kbWTSupplyM (some d)`, from
  `srvWTPool` (`kbWTSupplyM_of_srvWTPool`, with the boot backend's discarded `E.γbe` part: P4).
- **The etcd pin bump for `NoDelPutAt`** (#22377): nothing from this step; it re-proves
  `keyIndex.doCompact`/`store.Compact` without the premise, and every statement drafted here is
  independent of it.

## Questions for the user (one batch)

- **Q1, R2-7's timing (found by this Draft).** *Answered (a), 2026-10-30; drafted below.* `mvcc.New` takes `kbWTSupplyM (some d)` when the store
  is built, inside `NewServer`; the server's write budget `srvWTPool` is allocated by `start`
  (`EtcdServer__start.lean:432`, from `srvWTStock` in the built server's state), after `NewServer`
  returns. It cannot simply be allocated earlier: its invariant holds the storage-version monitor's
  read token, which `NewServer` retires from the store after `New`. So R2-7's conversion
  (`kbWTSupplyM_of_srvWTPool`, proved) has no pool to convert at `New`. Options:
  - (a) **the supply per compaction, not per store**: `NewStore`/`newWatchableStore`/`New` lose
    `kbWTSupplyM kb` from their pre, and `store.Compact.spec` takes it (persistent, `kbWTSupplyM
    γ.kb`; the job's closure keeps a copy). The apply thread has it from `srvWTPool` after `start`
    (R2-7's law, the boot backend's `E.γbe` part discarded). Changes the exported
    `mvcc_store_Compact`'s and `mvcc_NewStore_backend(_cmp)`'s statements (the premise moves) and
    mvcc's `physCmp` (where the supply sits in the store's invariant). **Recommended**: the supply is
    needed only to compact, and it is persistent, so the per-call premise costs callers nothing.
  - (b) allocate `srvWTPool` in `NewServer` before `New`, its monitor's-token disjunct allocated as
    checked out (a deposited part of `E.γbe`), the monitor checking its retired token in later:
    D22's statements (`srvWTStock` in `InvBuild`/`InvStart`, `start`).
  - (c) a pool of the job's own (two stocks): reverses R2-7 (the user's), and needs about twice the
    receipt bound in tokens (a stronger premise in compaction mode).
- **Q2, the drafted statements above**: `New.spec`/`newWatchableStore.spec` (one conjunct,
  `crevRightM kb γ.st`), `NewWatchStream.spec` (pre: `crevFrozen γ.st`), and the in-place
  redefinitions of `isWatchableStore` (`wsFrozenM`) and `watchStoreInv` (`wsWatchFrozen`).
- **Q3, `Cleanup`** (a scope note, no decision needed now): `EtcdServer.Cleanup` (`server.go`)
  closes the KV. A compacting server has given its closer up at `NewServer`'s end. Today this is
  unreachable in the model: `Cleanup` runs only in `run`'s deferred shutdown, which is never reached
  (`EtcdServer__run.lean`: `run` never returns). If the shutdown is ever modelled, the closer must
  be mode-gated there.

## Q1 (a), drafted (2026-10-30)

The user's answer to Q1: **(a)**, the write-back supply per compaction, not per store. Drafted in
`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/M2StorageDraftSupply.lean` (new, imported by nothing;
no `axiom`, no `sorry`), and in the two existing Draft modules (`New.specD`/`newWatchableStore.specD`,
`server_kv_watchable_ofC`). Nothing switched: the internal predicates `physCmp` and `compactJobPre`
cannot change in place without `updateCompactRev.spec` changing, hence `store.Compact.spec`
(exported, `mvcc_store_Compact`), so they are drafted too (`physCmpD`, `compactJobPreD`).
`compactJobResM` (the job's exclusive budgets) and `compactRes` are untouched: the supply is
persistent and travels in the job's persistent premise, not in its token.

**The drafted texts** (each replaces the definition or statement of the same name without `D` at the
switch; only the changed parts shown, the full texts in the Draft module):
- `mvcc.physCmp` (internal, `InvStore.lean`) loses the supply:
  ```lean
  def physCmp (s : Loc) (γ : StoreNames) : IProp GF :=
    if kbCmpM γ.kb then iprop(mwInv γ ∗ storeRegd s γ) else iprop(True)
  ```
  with `physCmp_on`/`physCmp_off`/`mwSwap_of_physOk` restated (`physCmpD_on`, `physCmpD_off`,
  `mwSwap_of_physCmpD`), and `physCmp_alloc` without its `kbWTSupplyM γ.kb` argument
  (`physCmp_allocD : mwRest γ ∗ kbMW γ.kb γ.bucket ∗ storeRegd s γ ={⊤}=∗ physCmp s γ`).
- `mvcc.compactJobPre` (internal, `InvCompact.lean`) gains it, after `crevLb`:
  ```lean
  def compactJobPre (s : Loc) (γ : StoreNames) (rev : w64) : IProp GF :=
    iprop(isStore s γ ∗ storeStop s γ ∗ schedule.schedLive γ.sch ∗ ⌜storeCmp γ⌝ ∗
      crevLb γ.idx (sint.Z rev) ∗ kbWTSupplyM γ.kb ∗
      ∃ log : Log, idxCert γ.idx log ∗ idxNevLb γ.idx log ∗
        ⌜0 ≤ sint.Z rev ∧ sint.Z rev < log.length ∧ NoDelPutAt log (sint.Z rev)⌝)
  ```
  plus an instance `kbWTSupplyM_persistent` and a law `kbWTSupplyM_on (h : kbCmpM kb) :
  kbWTSupplyM kb ⊣⊢ kbWTSupply kb` (`InvStore.lean`).
- **`store.Compact.spec`** (exported, `mvcc_store_Compact`): the pre's last line becomes
  ```lean
      mvcc.csContract P f Pre Q Post ∗ traceutil.ownTrace trace te ∗ mvcc.storeRT γ ∗
      mvcc.kbWTSupplyM γ.kb }}
  ```
  (post unchanged). Its docstring gains: "**The write-back supply** (Q1 (a), 2026-10-30): the
  caller gives the compaction's supply `kbWTSupplyM γ.kb` (persistent; the server's from
  `srvWTPool`, R2-7), which the store no longer keeps; the job gets it in its premise."
- `store.updateCompactRev.spec`, `store.compactLockfree.spec` (internal, linked): the same pre line
  (`… ∗ mvcc.storeRT γ ∗ mvcc.kbWTSupplyM γ.kb }}`); `updateCompactRev`'s docstring's "from the
  store's supply (`physCmp`'s `kbWTSupply`)" becomes "from the caller's supply". Posts unchanged
  (`compactJobPre` read over the redefinition).
- `store.compact.spec`, `store.scheduleCompaction.spec`: unchanged text (over the redefined
  `compactJobPre`).
- **`NewStore.spec`**, **`newWatchableStore.spec`**, **`New.spec`**: the pre line
  `mvcc.kbSRM kb ∗ mvcc.kbWTSupplyM kb ∗` becomes `mvcc.kbSRM kb ∗` (nothing else; `New.specD` and
  `newWatchableStore.specD` carry it beside P3's changes). `NewStore`'s docstring: "and its
  write-back supply (`kbWTSupplyM`)" goes; `kbWTSupplyM`'s and `kbWTSupply`'s docstrings
  (`InvStore.lean`) say `store.Compact` takes it.
- The internal bridge `mvcc.NewStore_backend` (`StoreBackend.lean`) and the exports
  **`mvcc_NewStore_backend`**, **`mvcc_NewStore_backend_cmp`** (`Results.lean`): the pre line
  `backend.wbTok d.γB ∗ backend.wbTok d.γB ∗ mvcc.kbSRM (some d) ∗ mvcc.kbWTSupplyM (some d) ∗`
  becomes `backend.wbTok d.γB ∗ backend.wbTok d.γB ∗ mvcc.kbSRM (some d) ∗`. `_cmp`'s docstring: its
  client brings the supply to `store.Compact` (with the contract, the trace and the reader's token).

**What was proved** (`etc/lean-check.py` and a targeted `lake build`):
- **The compaction chain, against the drafted specs, linked**: copies of today's proofs of
  `updateCompactRev`, `scheduleCompaction`, `compact`, `compactLockfree` and `Compact`
  (`…wp_proofD`), each against its `specD` over `compactJobPreD`; the store's `physCmp` read only
  through `physCmpD` (`physCmpD_of_physCmp`, then `iclear`: the copies cannot use today's supply);
  the supply from the pre (`updateCompactRev`) or the job's premise (`scheduleCompaction`). And
  `mvcc_store_CompactD : store.Compact.specD` and `wp_compactLockfreeD`, linked with today's
  callees: no hypothesis. The changes against today's proofs are the marked lines (`Q1 (a)`):
  two `wp_start` patterns, the `physCmp` destructuring (two sites), four `compactJobPre`
  destructurings, the hypotheses' names. At the switch they replace today's proofs as they are.
- **The creation side**: `physCmp_allocD` (`NewStore`'s one changed step: it drops `Hwts`);
  `NewStore_backendD` (the bridge, over `NewStore.specD`), and the exports
  `mvcc_NewStore_backendD`/`mvcc_NewStore_backend_cmpD` over `NewStore.specD` (a hypothesis: the
  linked `wp_NewStore` proves today's `NewStore.spec`). Not proved: `NewStore.specD` itself, since
  `NewStore`'s proof builds `isStore`, whose `physOk` holds `physCmp`, so it can only be re-proved
  over the in-place redefinition; its change is `physCmp_allocD` and dropping `Hwts`.
  `newWatchableStore`/`New` pass the pre through to `NewStore` (drop `Hwts` from two patterns).
- **The server glue**: `server_kv_watchable_ofC` (over `New.specD`) without its `kbWTSupplyM
  (some d)` premise, re-checked.

`mvcc_store_CompactD` rests on exactly `mvcc_store_Compact`'s axioms (`#print axioms`, the same 1118).

**At the switch, elsewhere**: `etcdserver/BuildLemmas.lean:134` (for `New`) and
`etcdserver/Results.lean:855` (for `mvcc_NewStore_backend`; its one caller outside mvcc) each make
`Hwts : mvcc.kbWTSupplyM … $$ []` at `cm = false` and pass it: both lines go. The apply loop's
compaction arm (later) gives `store.Compact` the supply from `srvWTPool` through
`kbWTSupplyM_of_srvWTPool` (at `start`'s pool, the boot backend's `E.γbe` part discarded, P4).

## The tally

Drafting: one finding (Q1, R2-7's timing) that the Probe and the backend-cmp reviews had not
seen: they checked `kbWTSupply`'s statement and R2-7's conversion, not when `NewServer` holds a pool
to convert. No Go bug found.

## After review round 1 (2026-10-30)

The report: `notes/spec-first-study/m2-storage-review-1.md` (on `40fb781417`; F1, F2, S1-S10). The
user's decisions (2026-10-30): **F1**, "no watchers in compaction mode" is a client-side premise,
in the Watch stream's client-facing contract; **F2**, freeze `E.γbe` in compaction mode, drafted
against D22's predicates (the collaborator's track: draft only). The rest decided here. Nothing
exported, trusted or D22's switched; no `axiom`, no `sorry`.

### The gRPC mechanism (checked for F1)

gRPC's stream model (`Proof/google_golang_org/grpc/InvGrpcStream.lean`) gives a stream method three
parameters: the per-run resource `S` (the server's slot pool), the stream specification
`Spec γs Dn` (the server's, fixed at registration, given to both ends at the stream's creation),
and the client's content of each request `Up i m` (given with the client's `Send`, received with
the handler's `Recv`; `srvStreamIs`, read by the watch server through `v3rpc.upOk`). A client's
`NewStream` presents nothing. So **a client's fact reaches the handler per request, not at the
stream's opening**; `watchServer.Watch` calls `NewWatchStream` before any `Recv` (`watch.go:177`),
so the round's `NewWatchStream.specD` premise could not be met from the client. But a watcher is
registered only by a create request, and a create request already carries a watch token through
`Up` (`watchUp`, D19b; the client takes it from `watchTokPool`, which its member facts hold): the
"no compactor" fact rides with it. (The auth work's grants travel the other way, in `Dn`.)

### F1, drafted: the create token carries the "no compactor" fact

- **mvcc** (`mvcc/M2StorageDraft.lean`): `storeWatchParams`'s per-watch token (internal,
  `InvWatchStore.lean:1599`) becomes
  ```lean
    T := iprop(mvcc.watchTok γ ∗ mvcc.crevFrozen γ.st)
  ```
  (`storeWatchParamsD`; the rest unchanged). `watchStream.Watch.spec` and `watchableStore.watch.spec`
  take `P.T` already, so their texts are unchanged; `watch` re-establishes `wsWatchFrozen` with it.
  **`NewWatchStream.spec` keeps today's text** (the round's `NewWatchStream.specD` premise is
  withdrawn: the stream it returns is over the redefined parameters, so it takes the fact per
  create). Exported: `NewWatchStream.spec`'s post and `watchStream.Watch`'s `P.T` read over the
  redefinition, in every mode.
- **v3rpc** (`api/v3rpc/M2StorageDraft.lean`): `upOk` and `watchUp` (`InvWatch.lean:209`, `:225`), the
  create arm
  ```lean
       | .create _ => iprop(mvcc.watchTok γ ∗ mvcc.crevFrozen γ.st)
  ```
  (`upOkD`, `watchUpD`, `upOkD_watchUpD`; `createArm_T`: the arm is the drafted `T`). `recvLoop`'s
  proof destructures one more conjunct (`serverWatchStream__recvLoop.lean:274`). **Unchanged**:
  `watchServer.Watch.spec` (over `upOk`), `watchSrvOk`, `isWatchServer`, `grpcCfgOk`, `v3rpc.Server`,
  `common.Serve`, `NewServer.specCompact`'s hand-outs (`srvWatchBuilt`, `srvWatchReaders`): mode-free.
  A compacting server serves Watch streams; no client can register a watcher on it (no `crevFrozen`
  exists there: the authority's other half is the compaction right's).
- **client** (`client/v3/M2StorageDraft.lean`): the member's facts gain the fact,
  ```lean
  def client.watchMemberFactsD (V : WEnv GF) : IProp GF :=
    iprop(mvcc.watchTokPool V.R.γ ∗ mvcc.crevFrozen V.R.γ.st ∗ srvLogsSmall V.R ∗
      ⌜V.R.γ.st = V.R.E.γ⌝ ∗ watchLaws V ∗ srvKVFacts V)
  ```
  and `watchConnFactsD` (over it and `watchUpD`), `watchAddrFactsD` (`InvClientNewResult.lean:44`:
  `mvcc.crevFrozen V.R.γ.st ∗` after the pool; `watchUpD`); `watchUpD_create` (a create's content
  from the member's facts and a token: the client's three create sites, `watchGRPCStream__run.lean`
  `:518`, `:1619`, `:2718`). These are the premises of `NewWatcher`/`watcher.Watch`/... (the Watch
  stream's client-facing contract). `putgetc`'s client never watches (`client.New` without
  `isNewClient_watcher`): it owes nothing.
- **The off server's source**: `NewServer.spec`'s post (exported) gains `mvcc.crevFrozen E.γ ∗`
  (persistent; its proof: `mvcc.isWatchableStoreD_frozen` at `{ d with cm := false }`), which the
  examples whose clients watch pass on (`watchkv/Served.lean:98`, `linkv3p/WatchEnv.lean:82`,
  `cache/v3/Results.lean:269`, beside `watchTokPool_of_server`). `specCompact`: nothing. The merged
  spec: `□ (⌜(retention) = 0⌝ -∗ mvcc.crevFrozen E.γ)` (a compacting server has none).
- A creator other than the server that wants to watch a store over mvcc's assumed backend
  (`kb = none`, "compacting" for the watch API) freezes it: `mvcc.crevFrozen_of_new` (S5).

### F2, drafted: the apply thread's part of the backend's name discarded in compaction mode

**Withdrawn** (2026-10-30, the user's decisions after `lean`'s Stage P: restore must work in
compaction mode); the drafts were removed in step 1 ("Step 1 on the merged lean", below).

(`etcdserver/M2StorageDraft.lean`.) A discarded part of a ghost variable forbids every update of
it (an update needs the whole), so discarding **one** holder's part freezes `E.γbe`; the apply
thread's quarter (`srvBeOwn`) is the one to discard: the apply thread runs the compaction arm, and
holds it directly (not in an invariant). The others (`bemuP`'s half, `srvWTPool`'s and
`srvWTStock`'s quarters, the monitor's checked-out parts) stay as they are.
```lean
def srvBeFrac (E : apply.AEnv GF) : DFrac :=
  if mvcc.kbCmpM E.γ.kb then DFrac.discard else DFrac.own (1 : Qp).half.half

def srvBeOwnD (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ d : mvcc.KBReal, ⌜E.γ.kb = some d⌝ ∗
    srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d.be ∗
    dghostVar E.γbe (srvBeFrac E) d)
```
Proved: `srvBeOwnD_off` (off, today's `srvBeOwn`), `srvBeOwnD_frozen` (on, a discarded part at the
store's backend, copied out), `kbWTSupplyM_of_srvBeOwnD` (`srvWTPool E γp ∗ srvBeOwnD s E ⊢
srvBeOwnD s E ∗ mvcc.kbWTSupplyM E.γ.kb` in compaction mode: `store.Compact.specD`'s supply, which
closes Q1 (a)'s chain to its real caller), `srvBe_allocD` (the boot's three-way split, the apply
thread's part persisted when the backend compacts).

**The D22 statements that would change** (for the collaborator; none changed here):
1. `srvBeOwn` (`InvApplier.lean:555`): `srvBeOwnD`'s text.
2. `srvBeOwn_frag` (`InvApplier.lean:913`): the lent part at `srvBeFrac E` (its users,
   `srvWTPool_take_at_d`, `srvWTPool_take_extra_d` and `ApplyNormalOn.lean:718`'s agreement, are
   generic in the fraction).
3. `srv_be_swap` (`SnapApply.lean:119`): gains `¬ mvcc.kbCmpM E.γ.kb` (it gathers the whole of
   `E.γbe`); its caller (`applySnapshot`'s walk, `SnapApplyWalk.lean:452-465`) has it from
   `srvEnvOk`'s `d.cm = false` today, and after the merge (`d.cm = false ∨` the no-snapshot
   configuration) from the no-snapshot branch, where no snapshot is installed (P4).
4. The snapshot state's rebuild at the new backend (`SnapApplyKV.lean:117`): `srvBeOwnD` there
   needs the received backend off (`d'.cm = false`, D22's received backends never compact): a
   premise if it is not already known.
5. `NewServer`'s proof: the allocation (`NewServer.lean:644-648`) by `srvBe_allocD`, `srvBeOwn` at
   boot (`:1561`); the merged spec builds at `cm := (retention ≠ 0)`.
Unchanged: `srvWTPool`, `srvWTStock`, `bemuP`, `srvBemuReaderAt`, `kbWTSupplyM_of_srvWTPool`.

### The second tier

- **S1, fixed.** One glue lemma, `server_kv_watchable_ofD`, over the backend record `d` (the mode
  `d.cm`): the deletable keys fixed by the mode inside (`storeDlReg_fix` or `dlNoDel_fix`, with
  `storeBackend_of_backendC`/`storeBackend_of_backend`), `□ (⌜d.cm = true⌝ -∗ backend.fkV d.γB
  true)` and `srSlot` (any mode) in the pre, the post at `kb = some d` with
  `actualMaxReaders - nJobRd (some d) - 2` readers, `retiredAt γ (nJobRd (some d))` and
  `crevRightM γw.st`. Replaces `server_kv_watchable_ofC`; at the switch it replaces today's
  `server_kv_watchable_of` (with `txn.isKV`/`kvWriter` back, the Draft's gap).
- **S2, fixed.** Laws, no unfolds in the glue: `mvcc.kbCmpM_some`, `mvcc.nJobRd_some_on`
  (`InstanceLaws.lean`, switched: new laws only); `isWatchableStoreD_isStore`,
  `isWatchableStoreD_readView`, `storeDlReg_fix` (in the Draft; to `InvWatchStore`/`InstanceLaws`
  with the redefinition). `newServer_compactRight` dropped: at the call, `mvcc.compactRight_of_wsCloser _ _ _ h` with `h`
  from `γw.st.kb = some d` and `(mvcc.kbCmpM_some d).2 hcm`. Left: `txn.storeWTs`'s unfold (inherited from today's
  lemma; txn's, not this round's).
- **S3, fixed.** `crevRightM γs := if kbCmpM γs.kb then crevUB γs.idx ½ (-1) else True`; the posts
  read `crevRightM γ.st`; `crevRight_split` and `compactRight_of_wsCloser` lose `kb`/`hk`.
- **S4, fixed.** The false header claim corrected (mvcc Draft's header, "What reads differently
  at `cm = false`", and STATUS): with F1's route, the create token (`P.T`, `upOk`, `watchUp`, the
  clients' member facts) gains `crevFrozen` in every mode, and `NewServer.spec`'s post gains it;
  `RestorePre.restorePre_of_apply` takes it from `isWatchableStoreD_frozen` with `srvEnvOk`'s
  `d.cm = false`. `srvWatchBuilt`/`srvWatchReaders` are unchanged (with F1 on the client side,
  nothing above mvcc needs a mode-gated watch state).
- **S5, fixed.** `mvcc.crevFrozen_of_new : isWatchableStoreD s st γ ∗ crevRightM γ.st ={E}=∗
  crevFrozen γ.st` (any mode; on, it spends the half). `wsFrozenM`'s docstring says `kb = none`
  counts as compacting for the watch API; `kbCmpM`'s docstring (`InvStore.lean`) says so at the
  switch.
- **S6, rejected** (`notes/decisions.md`, "M2: the frozen fact stays in `isWatchableStore`"): with
  F1 on the client side, `Hfrz` (mode-gated) is where the off server's two readers find the fact,
  through a law from what they already hold (`isWatchableStoreD_frozen`): `NewServer`'s new post
  conjunct and D22's `RestorePre`. Dropping it would put `crevFrozen` into D22's server state.
- **S7, superseded by F1's route.** No closure capture: the fact is `P.T`'s, which
  `watchableStore.watch.spec` already takes (text unchanged).
- **S8, fixed.** `kbWTSupplyM_alloc`'s docstring: "for a creator other than the server (whose supply
  is `srvWTPool`'s, R2-7): a stock of its own", with the margin (`2^40 - 2` against `2^48`).
- **S9, fixed.** `store.Compact.specD` carries today's full docstring and the supply paragraph
  (both sources named).
- **S10.** `isWatchableStoreD_off` dropped (an `Iff.rfl` at the in-place switch). `writerOwn`'s
  `2 + nJobRd`: kept, as the reviewer accepts.
- **The reviewer's open checks.** `WsOk` gives `Wu ≠ ∅ → M ≠ ∅` (proved:
  `mvcc.wsOk_M_ne_of_Wu`, by `live_st` and `st_m`); the gRPC mechanism, above.

### What the switch costs, revised

Beyond the round's list ("What the switch costs"): mvcc's `storeWatchParams` (one field) and the
proofs that consume a create token (`watch`, `watchStream.Watch`: one more conjunct); v3rpc's
`upOk`/`watchUp` and `recvLoop`'s pattern; the client's `watchMemberFacts`/`watchConnFacts`/
`watchAddrFacts` and its three create sites; `NewServer.spec`'s post (`crevFrozen E.γ`) and the
three watching examples; D22's five statements above (the collaborator's). No longer: v3rpc's
`watchServer.Watch` taking `crevFrozen` from the server's watch state, `srvWatchBuilt` carrying it.

### Checked

`etc/lean-check.py` on the four Draft modules and `InstanceLaws.lean`; `lake build` of the Draft
modules (targeted), and a full `lake build` of `5c897670ef` (passed, 10960 jobs, no error). `#print axioms` of the new results: no
`sorryAx`.

## After review round 2 (2026-10-30; stopped early)

The report: `notes/spec-first-study/m2-storage-review-2.md` (on `e6ed00dee8`; N1, S1'-S6'),
committed on its own (`725f70d2f0`). **Stopped early at the coordinator's request**: `lean` moved
by 622 commits (NewServer, applyAll, the D22 predicates), so the round was cut at a checked point,
without the full build; the coordinator merges `lean` and re-checks the Drafts. What is done and
what is not:

### Done (checked: targeted `lake build` of the five Draft modules, no error; no `axiom`, no `sorry`)

- **S4', fixed.** `mvcc.noCompactor γs` (`mvcc/M2StorageDraft.lean`), `@[no_expose]`, body
  `crevFrozen γs`; laws `noCompactor_persistent`, `noCompactor_frozen` / `noCompactor_of_frozen`
  (mvcc's and the server's own proofs), `isWatchableStoreD_noCompactor (h : ¬ kbCmpM γ.st.kb)`,
  `noCompactor_of_new` (was `crevFrozen_of_new`, S5). The client-facing statements now name it:
  `storeWatchParamsD.T := watchTok γ ∗ noCompactor γ.st`; v3rpc's `upOkD`/`watchUpD` create arm
  `mvcc.watchTok γ ∗ mvcc.noCompactor γ.st`; the client's facts. `wsWatchFrozen` stays over
  `crevFrozen` (internal; `watch` converts with `noCompactor_frozen`).
- **N1, the law and the client glue.** v3rpc (`api/v3rpc/M2StorageDraft.lean`): `watchSrvOkD`,
  `isWatchServerD` (Draft-only copies over `isWatchableStoreD`: at the switch `isWatchableStore` is
  redefined in place and their texts are unchanged), and the laws
  `v3rpc.isWatchServerD_noCompactor (h : ¬ mvcc.kbCmpM R.γ.st.kb) : isWatchServerD p R ⊢
  mvcc.noCompactor R.γ.st` (the reviewer's law), `isWatchServerD_link` (`⌜R.γ.st = R.E.γ⌝`, a v3rpc
  law in place of the client's unfold) and `isWatchServerD_noCompactor_env` (the mode at `R.E.γ.kb`).
  Client (`client/v3/M2StorageDraft.lean`): `watchMemberFactsD_of_server (h : ¬ kbCmpM V.R.E.γ.kb) :
  watchMemberFacts V ∗ isWatchServerD p V.R ⊢ watchMemberFactsD V` (what each watching site does,
  `watchkv/Served.lean:98`, `cache/v3/Results.lean:269`, `linkv3p/WatchEnv.lean:82`: one `ihave`
  more, plus the hypothesis `h`); `watchMemberFactsD_of`.
- **S3', fixed.** The new conjunct appended last in `watchMemberFactsD` and `watchAddrFactsD`, and a
  projection `watchMemberFactsD_noCompactor` (used by `watchUpD_create`). Sites that destructure by
  position anyway (for the switch's cost): `client/InvWatch.lean:469` (`⟨-, -, %Hst, -⟩`: unaffected
  when appended last), `client/watcher__Watch.lean:54-55` (`⟨-, -, -, -, #Hkf0⟩`: breaks, `#Hkf0`
  would bind the pair: use a projection), `client/InvClientNewResult.lean:112` (unfolds),
  `examples/linkv3p/WatchEnv.lean:89` (unfolds); `watchAddrFacts`'s destructuring sites not yet
  counted.
- **S6', in part.** `mvcc.storeWatchParamsD_T`/`_R` dropped; `v3rpc.createArm_T` kept, marked
  Draft-only (dropped at the switch).

### N1: the route to the examples (decided, not yet drafted)

**Why not `memberBuilt`'s text**: the watching examples hold `memberBuilt`/`memberUp`, whose `E` is
existential and whose parameters (`s ρ E₀ lg γn id N served`) carry no mode; both
`newServer.spec` and `newServer.specCompact` return `memberBuilt`. So the server's mode can reach
the examples only through a parameter they already pass: the stand-in `E₀`, through `envAgree E E₀`
(a pure conjunct `memberBuilt`/`memberUp`/`NewServer.spec`'s post already carry). This is the
`m2` branch's route (its `apply.AEnv.cmp`, `envAgree … ∧ E.cmp = E'.cmp`, `memberBoot … (cmp :=
false)`, `memberBoot_cmp`, linkv3p's `memberWatch` `⌜… ∧ E.cmp = false⌝`): `memberBuilt` and
`memberUp` keep their texts. The drafted statements (exact text; not yet in a Draft module):
- `apply.AEnv` (`apply/Chain.lean`) gains the field `cmp : Bool := false` (the `m2` branch's).
- `envAgree E E' := E.γ.idx = E'.γ.idx ∧ E.γ.cok = E'.γ.cok ∧ E.γrev = E'.γrev ∧ E.cmp = E'.cmp ∧
  (mvcc.kbCmpM E.γ.kb ↔ E.cmp = true)` (the last conjunct: the server's own mode is its store's,
  one reading, S5'; the field is truthful on the server's environment too).
- `NewServer.spec`: a premise `E₀.cmp = false →` beside `cfg.AutoCompactionRetention' = 0 →`
  (exported; the post's text unchanged, its `envAgree E E₀` now gives `¬ kbCmpM E.γ.kb`);
  `NewServer.specCompact`: `E₀.cmp = true →`; the merged spec: `(E₀.cmp = true ↔
  cfg.AutoCompactionRetention' ≠ 0) →`.
- `common.memberBoot … (cmp : Bool := false)` with `E₀.cmp = cmp` appended to its pure facts;
  `StartCompactingServer.spec` at `memberBoot … true`; `alloc1`/`alloc3` (and linkv3p's alloc)
  `(cmp := false)` defaults; a law `memberBoot_cmp` to read it before `NewServer` takes the bundle.
- `etcd_cache_served` (`cache/v3/Results.lean`, exported) and `watchkv`'s `wk_served` gain
  `(hoff : ¬ mvcc.kbCmpM V.R.E.γ.kb)`; linkv3p's `memberWatch`/`memberAt` gain `¬ mvcc.kbCmpM
  E.γ.kb` in their pure facts (appended), from `envAgree` in `startCluster`.
- Costs at the switch: NewServer's anonymous `AEnv` constructor (`NewServer.lean:1032`, one more
  component) and its `envAgree` proof (`⟨…, rfl⟩` gains `rfl` and the mode); `srvC_agree`
  (`InvBuild.lean:386`) and `srvCM_agree` (`ServerOn.lean:565`) destructure `⟨hi, hc, hr⟩`
  (become `⟨hi, hc, hr, -⟩`); `newServer.lean`'s two `memberBoot` destructurings; the call sites
  passing the new premise. Not drafted: `envAgreeD`, `memberBootD`, `envAgreeD_of_new`,
  `envAgreeD_off`, and the examples' glue; all to redo against the merged `lean` (NewServer moved).

### Not done (as of the stop; step 1 below takes them up)

- **S1'** (`kbWTSupplyM_of_srvBeOwnD`'s needless mode premise), **S2'** (`srvBeFracOf`),
  **S5'** (`srvBeFrac`'s docstring: the store's `γ.st.kb` and `E.γ.kb` agree, `γ.st = E.γ` from
  `srvWatchBuilt`/`watchSrvOk`; D22's install keeps both off), **S6'**'s remaining unfolds
  (`backend.wbTok`: use `wbToks_split`; `txn.storeWTs`: a law `storeWTs_some`) and the
  `applySnapshot`/`srv_be_swap` question for the collaborator in STATUS: all agreed, not yet made.
  They touch D22's drafted predicates, which `lean` has moved.
- The consolidated "Statements for the user's approval (Q2)" list: not written (it depends on the
  merged `lean`'s NewServer and D22 texts). Its known members so far: `New.spec`,
  `newWatchableStore.spec` (`crevRightM`, the supply moved out), `NewStore.spec`,
  `store.Compact.spec`, `mvcc_store_Compact`, `mvcc_NewStore_backend(_cmp)` (Q1 (a)); the in-place
  `isWatchableStore`, `watchStoreInv`, `storeWatchParams` (`noCompactor` in `T`); v3rpc's
  `upOk`/`watchUp`; the client's `watchMemberFacts`/`watchConnFacts`/`watchAddrFacts`;
  `NewServer.spec`/`specCompact` (the `E₀.cmp` premise), `envAgree`, `apply.AEnv.cmp`;
  `etcd_cache_served`; D22's (the collaborator's): `srvBeOwn`, `srvBeOwn_frag`, `srv_be_swap`, the
  snapshot state's rebuild, `NewServer`'s allocation of `E.γbe`.
- No full build (the coordinator's instruction).

## The user's decisions after `lean`'s Stage P (2026-10-30)

- **Three members, not one** (reverses phase 0's decision 2, `notes/m2-plan.md`): raft's snapshots are
  proved, so M2 targets a 3-member cluster. A lagging follower installs a snapshot while compaction
  runs, so **restore must work in compaction mode**; P4's scope limit (no restore while compacting)
  and the F2 anchor (freeze `E.γbe` in compaction mode) are withdrawn. Watchers stay excluded in
  compaction mode (N1's route, unaffected).
- **Order:** (1) finish the parts that do not depend on restore (Q1 (a), N1, round 2's S1'-S6'),
  against the merged `lean`; (2) draft restore in compaction mode as its own increment
  (`store.Restore` taking back the compaction right, `storeStop` and the job's budgets and handing out
  the new store's; the write-back supply following the backend through `applySnapshot`; D22's
  `srvEnvOk`, `applySnapshot.specSnap`, the walk lemmas). Draft only: D22 is the collaborator's, who
  will see it through the notes. The server's restore branch is still SNAPSHOT-SORRY #8
  (`EtcdServer__run.lean:811`); the 3-member program comes after the apply-loop side.

## Step 1 on the merged lean (2026-10-30)

The parts that do not depend on restore, against `lean` merged at `9b09b9f411` (Stage P, the
auth-mode merge's step 6). Commits `e80d70f0c9` (the Supply repaired), `f58a6b6adf` (N1, F2 dropped,
the S-items), and this notes commit. Nothing exported, trusted or D22's switched; no `axiom`, no
`sorry`; no Perennial change.

### What Stage P changed for the Drafts

- **`M2StorageDraftSupply.lean`**: its 64 errors were one cause, the missing
  `go_etcd_io.raft.v3.Assumptions` instance at the linked results (Stage P's instance-argument
  pattern, as in `mvcc/Link.lean`/`Results.lean`); one `variable` line. Nothing else moved.
- **The other Draft modules still say what they did**: `lean` changed mvcc, v3rpc and the client
  only by the same instance lines (and `store.Close`'s `as -`): `isWatchableStore`,
  `watchStoreInv`, `storeWatchParams`, `store.Compact`'s chain, `NewStore`/`New`/
  `newWatchableStore`'s specs, `upOk`/`watchUp`/`watchSrvOk`/`isWatchServer`,
  `watchMemberFacts`/`watchAddrFacts` are textually today's of the Drafts' copies (checked by diff of
  `4e2bc21c8c..9b09b9f411`).
- **The server moved**: `NewServer` now has three specs, `spec` (`= specM false`,
  `NewServer.spec_of_specM`), `specM on` (auth on or off) and `specCompact`; the environment is
  built in `NewServer.wp_proofM` (generic in `on`), its agreement at `NewServer.lean:1039` (`hγs`),
  the store at `{ d with cm := false }` (`Hγw.2.2.1`, from `server_kv_watchable_of`'s post).
  `memberBoot` lost `readCredits` and `γ.dyn` (Stage P), and gained a twin `memberBootOn` (auth on).
  `NewServer.spec`'s post carries `srvKVCloser` (D22 S-g) and no `crevFrozen` (N1's law route).

### N1, drafted end to end

The route decided after round 2 (the mode through the stand-in `E₀`), over the current `NewServer`
and `examples/common`:
- **Server** (`etcdserver/M2StorageDraft.lean`): `apply.AEnvD` (today's `AEnv` extended by
  `cmp : Bool := false`: at the switch a field of `AEnv` itself), and
  ```lean
  def envAgreeD (E E' : apply.AEnvD GF) : Prop :=
    E.γ.idx = E'.γ.idx ∧ E.γ.cok = E'.γ.cok ∧ E.γrev = E'.γrev ∧ E.cmp = E'.cmp ∧
      (mvcc.kbCmpM E.γ.kb ↔ E.cmp = true)
  ```
  Laws: `envAgreeD_agree` (today's `envAgree`, for `srvC_agree`/`srvCM_agree`), `envAgreeD_mode`,
  `envAgreeD_off` (`envAgreeD E E₀ → E₀.cmp = false → ¬ kbCmpM E.γ.kb`), `envAgreeD_on`, and
  NewServer's step `envAgreeD_of_new` (today's agreement, `E.γ.kb = some d`, `d.cm = E.cmp`,
  `E.cmp = E₀.cmp`), `envAgreeD_of_new_off` (today's instance: `{ d with cm := false }`).
- **The specs' premises** (text, at the switch; not copied into Lean: one line each, the rest
  unchanged, the post's `envAgree E E₀` read over the redefinition):
  `NewServer.spec` and `NewServer.specM`: `E₀.cmp = false →` beside
  `cfg.AutoCompactionRetention' = 0 →`; `NewServer.specCompact`: `E₀.cmp = true →` beside
  `0 < sint.Z cfg.AutoCompactionRetention' →`; the merged spec:
  `(E₀.cmp = true ↔ cfg.AutoCompactionRetention' ≠ 0) →`. Their proofs: the anonymous `AEnv`
  constructor at `NewServer.lean:1039` gains `E₀.cmp`, `hγs` becomes `envAgreeD_of_new_off`.
- **Examples' boot** (`examples/common/M2StorageDraft.lean`, new): `env₀D … (cmp := false)`,
  `memberBootD … (cmp : Bool := false)` (pure facts gain `E₀.cmp = cmp`, appended),
  `memberBootD_cmp` (a `Main` reads the mode before `newServer` takes the bundle), `memberBootD_of`
  (the allocations' bundle at `env₀D … cmp`), `memberBootD_to` (what `newServer` passes on).
  `memberBuilt`/`memberUp`/`memberServed` keep their texts. `memberBootOn` (auth on) gets the same
  argument at the switch (authkv does not watch: default).
- **The watching examples' glue**, proved against the drafted watch-stream registration as a
  hypothesis (`v3rpc.etcd_watch_served_chain.specD`: `etcd_watch_served_chain` over `watchUpD`,
  `isWatchServerD`):
  - watchkv (`examples/watchkv/M2StorageDraft.lean`): `wk_servedD`, `wk_served` with
    `(hoff : ¬ mvcc.kbCmpM V.R.E.γ.kb)` and the post's `watchAddrFactsD V`;
  - cache (`cache/v3/M2StorageDraft.lean`): `etcd_cache_servedD`, the same for the exported
    `etcd_cache_served`;
  - linkv3p (`examples/linkv3p/M2StorageDraft.lean`): `memberWatchD`, `memberAtD` (pure facts gain
    `¬ mvcc.kbCmpM E.γ.kb`, appended), `memberWatchD_facts` (to `client.watchMemberFactsD`),
    `memberWatchD_of_at` (MainWatch's step).
  - At each `Main` (`watchkv/Main.lean`, `cachekv/Main.lean`; linkv3p's `startCluster` from
    `memberServed`): `hoff` is `envAgreeD_off` of the unfolded `envAgree E E₀` with the boot
    bundle's `E₀.cmp = false`.
  - Draft-only bridges (the identity at the in-place switch): `mvcc.isWatchableStoreD_to`,
    `v3rpc.isWatchServerD_to`, so the glue reuses today's client lemmas.

### The second-tier items

- **S1'** (`kbWTSupplyM_of_srvBeOwnD`'s mode premise): moot, the lemma is withdrawn with F2.
- **S2'** (`srvBeFracOf`): moot, withdrawn with F2.
- **S3'**: projections `client.watchMemberFactsD_kv` (for `watcher__Watch.lean:54-55`'s
  `⟨-, -, -, -, #Hkf0⟩`, which the appended conjunct breaks: at the switch the site reads
  `ihave #Hkf0 := watchMemberFacts_kv V $$ Hmf0`) and `watchMemberFactsD_st` (`InvWatch.lean:469`,
  `linkv3p/WatchEnv.lean`'s unfold). `InvClientNewResult.lean:112` unfolds all three facts: one
  more conjunct there.
- **S5'** (one reading of the mode): the mode clause of `envAgreeD`, `kbCmpM E.γ.kb ↔ E.cmp =
  true`, with `isWatchServerD_link` (`R.γ.st = R.E.γ`) for the watch side. In step 2 D22's install
  (which replaces `E.γ.kb`, `snapE_kb`) must keep it: the received backend at the server's mode.
- **S6'**: `mvcc.storeWatchParamsD_T`/`_R` were already dropped; `v3rpc.createArm_T` stays marked
  Draft-only. `txn.storeWTs`'s unfold replaced by a law, `txn.storeWTs_someD` (goes to
  `txn/Defs.lean` at the switch). `backend.wbTok`'s unfold **kept**: with a law
  (`wbTok_split`, or `InvApplier`'s `wbToks_split`) in place of `ownToks_add_1` + `unfold`, the
  kernel's check of `server_kv_watchable_ofD` hit deep recursion, then a deterministic timeout at
  `maxRecDepth 8000` (cause not found; the elaborator accepted it).
- **F2's drafts dropped** (`srvBeFrac`, `srvBeOwnD`, `_off`, `_frozen`, `kbWTSupplyM_of_srvBeOwnD`,
  `srvBe_allocD`). `kbWTSupplyM_of_srvWTPool` kept: its discarded part of `E.γbe` has no source now
  (pending step 2).

### Statements for the user's approval (Q2)

Every exported or trusted statement the switch changes (the drafted text in the named Draft
module). None is D22's: F2's five are withdrawn, and step 2 lists its own.
1. **`mvcc.New.spec`** (linked; a callee of `NewServer`'s proof): pre loses `mvcc.kbWTSupplyM kb ∗`
   (Q1 (a)); post `mvcc.wsCloser s st γ.st ∗ mvcc.crevRightM γ.st ∗` (P3), over the redefined
   `isWatchableStore` (`mvcc.New.specD`).
2. **`mvcc.newWatchableStore.spec`**: the same, `mvcc.storeCloser st γ.st ∗ mvcc.crevRightM γ.st ∗`
   (`newWatchableStore.specD`).
3. **`mvcc.NewStore.spec`**: pre loses `mvcc.kbWTSupplyM kb ∗` (`NewStore.specD`, Supply module).
4. **`mvcc.store.Compact.spec`**, export **`mvcc_store_Compact`**: pre's last line
   `… ∗ mvcc.storeRT γ ∗ mvcc.kbWTSupplyM γ.kb }}` (`store.Compact.specD`); internal
   `updateCompactRev`/`compactLockfree` alike.
5. Exports **`mvcc_NewStore_backend`**, **`mvcc_NewStore_backend_cmp`**: pre loses
   `mvcc.kbWTSupplyM (some d) ∗` (Supply module).
6. **mvcc, in place** (exported texts unchanged, meaning changed): `isWatchableStore`'s
   `"#Hfrz" ∷ mvcc.wsFrozenM γ.st`; `watchStoreInv` gains `mvcc.wsWatchFrozen γ σ`;
   `storeWatchParams`' `T := iprop(mvcc.watchTok γ ∗ mvcc.noCompactor γ.st)`, read by
   `NewWatchStream.spec`'s post and `watchStream.Watch`'s `P.T`. New exported names:
   `mvcc.noCompactor` (sealed, body `crevFrozen`) and its laws, `wsFrozenM`, `crevRightM`,
   `compactRight_of_wsCloser`, `noCompactor_of_new`.
7. **v3rpc, in place**: `upOk`'s and `watchUp`'s create arm
   `| .create _ => iprop(mvcc.watchTok γ ∗ mvcc.noCompactor γ.st)`: the registered content of
   `etcd_watch_served(_chain)` (texts unchanged). New law: `isWatchServer_noCompactor(_env)`,
   `isWatchServer_link`.
8. **client, in place**: `watchMemberFacts` and `watchAddrFacts` gain `∗ mvcc.noCompactor V.R.γ.st`
   (appended last); `watchConnFacts` reads them (the premises of `NewWatcher`, `watcher.Watch`, ...).
9. **`apply.AEnv`**: the field `cmp : Bool := false`.
10. **`envAgree`**: `envAgreeD`'s text (the mode clause).
11. **`NewServer.spec`**, **`NewServer.specM`**: premise `E₀.cmp = false →`;
    **`NewServer.specCompact`**: `E₀.cmp = true →` (trusted until proved: its proof is `sorry`).
12. **examples/common**: `env₀ … (cmp : Bool := false)`; `memberBoot … (cmp : Bool := false)` with
    `E₀.cmp = cmp`; `newServer.specCompact` and `StartCompactingServer.spec` at `memberBoot … true`
    (their allocation at `env₀ … true`); `memberBootOn` the same argument.
13. **`etcd_cache_served`** (exported): `(hoff : ¬ mvcc.kbCmpM V.R.E.γ.kb)`; post over the
    redefined `watchAddrFacts` (`etcd_cache_servedD`). watchkv's `wk_served` alike; linkv3p's
    `memberWatch`, `memberAt` gain `¬ mvcc.kbCmpM E.γ.kb` (appended).
14. **The write-back supply's server source**: **pending step 2** (`kbWTSupplyM_of_srvWTPool`'s
    discarded part of `E.γbe` had F2 as its source; with restore in compaction mode `E.γbe` changes,
    so the supply must follow the backend through `applySnapshot`).

### What step 2 will need (seen on the merged lean; not started)

- **`store.Restore.spec`** (`Spec/.../mvcc/store__Restore.lean:120`): pre
  `⌜∃ d, γ.kb = some d ∧ d.cm = false⌝ ∗ ⌜d'.cm = false⌝`, `writerOwn γ`, `crevFrozen γ`; its proof
  uses `writerOwn_off` (`store__Restore.lean:190`, `:390`) and `¬ kbCmpM` at `:295`. Step 2: take the
  compaction right, `storeStop` and the job's budgets (`compactJobResM`), hand out the new store's;
  `writerOwn` at `2 + nJobRd` already accepts a compacting count.
- **`watchableStore.Restore.spec`** (the walk's `hRst`, `SnapApplyWalk.lean:68`).
- **`applySnapshot.specSnap`** (`Spec/.../EtcdServer__applySnapshot.lean:54`): `(hcm : d.cm = false)`.
- **`srvEnvOk`** (`InvApplier.lean:478`): `… ∧ d.cm = false`.
- **The walk**: `SnapApplyWalk.lean:55` (`hcm`), `:291-292` (the new backend `d'.cm = false`),
  `:406-408`, `:461` (`srv_be_swap`, which gathers the whole of `E.γbe`: no discarded part may
  exist, so the supply cannot come from one), `:808`; `SnapApplyDefs.lean:95`, `:181` (`d'.cm =
  false` in the walk's state and post); `SnapApplyIsServer.lean:49` (`hcm'`);
  `SnapApplyPost.lean:116-155`; `SnapApplyKV`'s `snapE_kb` (with N1: the new backend at
  `cm := E.cmp`, so `envAgree`'s mode clause survives the install).
- **`RestorePre.lean:79-80`**: `sorry -- M2 S1` for `crevFrozen E.γ` (closable off by
  `isWatchableStoreD_frozen` with `srvEnvOk`'s `d.cm = false`; in compaction mode there is none:
  `Restore` takes the compaction right instead).
- **`srvKVCloser`** (`NewServer.spec`'s post, D22 S-g): at `cm = true` the closer becomes the right
  after `NewServer`'s last error return, so it holds `compactRight ∗ storeStop` (or is mode-gated).
- **SNAPSHOT-SORRY #8** (`EtcdServer__run.lean:811`, and `:1332` for `run`'s auth-on proof): the
  snapshot payload's job, over `applySnapshot.specSnap`'s premises: where a compacting server's
  restore will enter.
- **The supply**: `kbWTSupplyM_of_srvWTPool` (etcdserver Draft) needs a discarded part of `E.γbe`
  at `d`; with restore in compaction mode the supply must be re-made per backend (from `srvWTPool`
  at the current backend, under `bemu`) or be stated over the current backend.

### Checked

`etc/lean-check.py` on each Draft module; a targeted `lake build` of the nine Draft modules (7142
jobs, no error); the full `lake build` of `f58a6b6adf` passed (11206 jobs, no error).

## Step 2: restore in compaction mode (2026-10-30)

The user's order, item (2): `store.Restore` in compaction mode, the write-back supply following the
backend, D22's statements. Draft only: nothing exported, trusted or D22's switched; no `axiom`, no
`sorry`; no Perennial change. Commits `5e66e2c5b6` (mvcc), `c826174109` (etcdserver), and this notes
and issue commit. New Draft modules, imported by nothing:
`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/M2StorageDraftRestore.lean`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/M2StorageDraftRestore.lean`.

### The Go code (read at the pin, `.lake/go-src/etcd` `249d76bea7`)

- `store.Restore` (`kvstore.go:292-314`): under `s.mu`, `close(s.stopc)`, then `s.fifoSched.Stop()`,
  which cancels the scheduler's context and returns once the worker has run every pending job (with
  the cancelled context) and exited (`schedule.go:150-184`, `<-f.donec`). Only then does `Restore`
  write `s.b`, `s.kvindex`, `s.fifoSched`, `s.stopc` and call `restore()`, which reads
  `finishedCompactRev` into `compactMainRev`, raises `currentRev` to `scheduledCompactRev`, and, when
  the scheduled one is past the finished one, **resumes the compaction** (`compactLockfree`: a
  `SetScheduledCompact` and `ForceCommit` on the new backend, a job on the new scheduler).
- **A job in flight is safe.** The running job (`scheduleCompaction`) reads `s.b`, `s.kvindex`,
  `s.stopc` without a lock between batches; it finds `stopc` closed at its next `select` and returns
  an error, then `compactBarrier(context.TODO(), ch)` closes its channel. Every read of the fields by
  an old job happens before `donec` closes, so before `Restore`'s writes: no race. The barrier's
  re-schedule branch (a cancelled context with `stopc` open, which would take `s.mu` and deadlock
  against `Restore`) is unreachable, because `Restore` and `Close` close `stopc` before `Stop` (PR
  11817's fix). The interrupted job leaves the old backend half compacted, and the old backend is
  closed after the swap. The old backend's pre-commit hook during the job's last `ForceCommit` (after
  `ci.SetBackend(newbe)`) saves index `0`, which `unsafeUpdateConsistentIndex` skips. In
  `applySnapshot` (`server.go:1059-1104`), `Restore` comes before `s.be = newbe`, so every old job is
  done by the swap.
- **A bug: a queued job is dropped without closing its channel.** A compaction still in the queue
  when `Stop` runs gets the cancelled context, calls `compactBarrier(ctx, ch)`, finds `stopc` closed
  and returns without `close(ch)`. A `Physical: true` compaction RPC waits on that channel with no
  other case (`v3_server.go:402`), so it hangs and its handler leaks. Reproduced with a Go test
  (`issues/etcd-restore-pending-compaction-unclosed.md`, with `repro_test.go`). It is a liveness bug:
  the proofs are partial correctness, and `compactDone` already allows a cancelled context, so no
  statement changes.

### The design drafted (the root cause of P4 removed)

- **P4's root cause** is that today's compaction right is made by *discarding* the closer's share of
  the four fields `Restore` writes (`storeStop`: `↦□`, `curAt` and the restoring flag discarded) and
  the scheduler's stop token (`schedLive`). The jobs need the former to read the fields without a
  lock, and the untracked barriers need the latter.
- **The jobs' share in an invariant keyed by the scheduler's run token** (`mvcc.storeStopR`: an
  eighth of the fields at the current objects, `fieldShareAt s γ q8 o`, *or* `schedule.schedDoneD
  γ.sch`). A job runs with the run token (`schedule.jobIs`), so it finds the share there. Drafted for
  `schedule`: `Scheduler.Stop.spec`'s post gains `schedDoneD γ` (the run token's ghost part, given
  up by the worker at exit). The stopper swaps it in and takes the share out
  (`storeStopR_reclaim`). No job's cooperation is needed, so untracked barrier jobs are covered too.
- **A compacting store keeps its closer** (`mvcc.compactRightR s γ c := crevUB γ.idx ½ c ∗
  compactQueue γ c ∗ storeCloserR s γ ∗ storeStopR s γ`). `storeCloserR` is the closer with an
  eighth of the fields (the other eighth is the jobs'), the stop channel's close and the stop token.
  It is made from the closer by a split (`compactRightR_of_closer`, in place of
  `compactRight_of_closer`). After `Stop`, the two eighths are today's quarter again
  (`fieldShare_reclaim`, by `curAt`'s agreement). `Restore` then proceeds as over today's closer,
  with the queue and the revision at `c`. The same holds for `Close`, so Q3 (`Cleanup`) dissolves:
  a compacting server keeps its closer.
- **No `schedLive`.** `updateCompactRev`'s `ErrCompacted` barrier runs inside `Compact`, which holds
  the right (the queue), so it becomes a tracked job. The barrier's re-schedule branch is dead:
  drafted, `Scheduler.Stop` takes a persistent payload (the store's: its stop channel closed) that a
  job finding its context cancelled learns. A first idea, half the stop token in `s.mu`'s resource,
  fails because `store.Close` does not take `s.mu`. This is internal to mvcc and `schedule` and not
  written in Lean.
- **The compaction revision across a restore.** `γ.idx.crev` is logical: `Restore` keeps it, and its
  authority is monotone. The image's revision `c'` (the larger of its two records) is what the store
  ends at. Drafted: `c ≤ c'` as a premise, true because the compaction revision is a function of the
  committed raft log and the image is of a longer prefix. That is the apply side's obligation, as
  `L <+: L'` is today. Alternative (a question below): make `crev` physical.

### The drafted statements (Lean in `mvcc/M2StorageDraftRestore.lean`)

- **`mvcc.store.Restore.specM`** (drafts `store.Restore.spec`, D22 S6's statement, mvcc's Spec): the
  parameters gain `(c c' : Int)` and the premise `c ≤ c'`. The pre changes:
  ```lean
      mvcc.isStore s γ ∗ ⌜∃ d, γ.kb = some d ∧ d'.cm = d.cm⌝ ∗
      mvcc.restoreRightM s γ c ∗ mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗ …
      (∀ p, … → mvcc.keyCleanRead b' (mvcc.bucketViewC (γ.withPhys p)) (mvcc.storeRT (γ.withPhys p))
          (mvcc.restoreNCM (γ.withPhys p))) ∗
      mvcc.restoreImageM d' γb' ([[], []] ++ R) c' ∗ mvcc.kbRegRight (some d') ∗
      mvcc.kbSRM (some d') ∗ mvcc.kbWTSupplyM (some d') ∗ …
  ```
  (in place of `⌜… d.cm = false⌝ ∗ ⌜d'.cm = false⌝`, `storeCloser s γ`, `crevFrozen γ`, `kbNoCmp` in
  the clean read, `kbViewC … (bucketMap L') ∗ kbNoCmp (some d') γb'`). The post changes:
  ```lean
      mvcc.restoreRightPostM s (γ.withPhys p') c' ∗ … ∗
      mvcc.compactJobResM γ.kb ∗
      ([∗list] _x ∈ List.replicate (mvcc.nReaders - 1 - mvcc.nJobRd γ.kb) (), mvcc.storeRT γ) ∗ …
  ```
  The predicates by the mode:
  ```lean
  def mvcc.restoreRightM (s : Loc) (γ : mvcc.StoreNames) (c : Int) : IProp GF :=
    if mvcc.kbCmpM γ.kb then mvcc.compactRightR s γ c
    else iprop(mvcc.storeCloser s γ ∗ mvcc.crevFrozen γ ∗ ⌜c = -1⌝)
  def mvcc.restoreRightPostM (s : Loc) (γ : mvcc.StoreNames) (c : Int) : IProp GF :=
    if mvcc.kbCmpM γ.kb then mvcc.compactRightR s γ c else mvcc.storeCloser s γ
  def mvcc.restoreImageM (d' : mvcc.KBReal) (γb' : GName) (L : mvcc.Log) (c' : Int) : IProp GF :=
    if d'.cm then
      iprop(∃ m : mvcc.Bucket, mvcc.kbViewC (some d') γb' 1 m ∗ backend.fkV d'.γB true ∗
        ⌜mvcc.imageAt L c' m ∧ -1 ≤ c' ∧ c' < L.length ∧ mvcc.NoDelPutAt L c'⌝)
    else iprop(mvcc.kbViewC (some d') γb' 1 (mvcc.bucketMap L) ∗ mvcc.kbNoCmp (some d') γb' ∗
      ⌜c' = -1⌝)
  ```
  Here `imageAt L c m` says the bucket is the log's thinned at `c`: every entry of `m` is
  `bucketMap L`'s, and every missing one is `KeyDel L c`. That covers both a finished compaction
  and a leader's bucket mid-job.
- **`mvcc.watchableStore.Restore.specM`**: the same changes over today's text (`restoreRightM st γ.st
  c` in place of `storeCloser st γ.st ∗ crevFrozen γ.st`).
- **Off-mode laws, proved**: `mvcc.store.Restore.spec_of_specM` and
  `mvcc.watchableStore.Restore.spec_of_specM` (`specM → spec`). At `cm = false` the drafted specs
  give today's, at `c = c' = -1`, through `restoreRightM_off`, `restoreRightPostM_off`,
  `restoreImageM_off`, `restoreNCM_off` and `cmOff_true` (the slot, the supply and the budgets are
  `True`, `nJobRd = 0`).
- **Not drafted in Lean: `store.restore.spec`** (the trust boundary `restore()`; today
  `kbNoCmp`, `compactMainRev = -1`, no resume). Its compaction-mode generalization must:
  - read the two records (`finishedCompactRev` into `compactMainRev`, `scheduledCompactRev`
    resumed);
  - rebuild the index from a thinned bucket (**gap**: the index model's state after `restore` over
    a partially compacted bucket, some keys of the compaction at `c'` already deleted and others
    not, is neither "the index of `L'`" nor "compacted at `c'`"; the resumed job's
    `treeIndex.Compact` makes it the latter; this needs the index model's `keyIndex` of a thinned
    bucket);
  - take the compaction right's pieces at the new names (the new queue, the jobs' invariant, the
    new job's budgets and the supply) and give `compactRightR s γ' c'`.

  This is the first thing to design before `Restore.specM` can be proved, and the largest piece.
- **The compaction chain** (internal, at the switch): `compactJobPre`'s `storeStop s γ ∗ schedLive
  γ.sch` become `storeStopR s γ`. `compactRight` becomes `compactRightR` in `store.Compact.spec`
  (exported, `mvcc_store_Compact`) and the internal chain. `Scheduler.Stop.spec`'s post gains
  `schedDoneD γ` and its pre the cancellation payload. `compactRight_of_closer` and
  `compactRight_of_wsCloser` give way to `compactRightR_of_closer` and `wsCloserR_of_wsCloser`.
  `wsCloserR` (the watchable store's own parts with the inner right) is what a compacting server
  keeps (`wsCloserR_split`/`_join` around `Restore`). `storeStop` and `schedLive` go.

### The write-back supply following the backend (task 2)

**Drafted (recommended): one stock invariant per backend, sharing the pool's receipt counter**
(`etcdserver/M2StorageDraftRestore.lean`):
```lean
def srvWTStockInv (γp : GName) (d : mvcc.KBReal) : IProp GF :=
  inv srvWTStockN iprop(∃ (m n : Nat), monoNatLbOwn γp m ∗ ownToks d.γB.wb n ∗
    ⌜receiptBound GF ≤ m + n + 1⌝)
def srvWTPoolR (E : apply.AEnv GF) (γp : GName) : IProp GF :=
  inv srvWTN iprop(∃ (a : Nat) (d : mvcc.KBReal), ⧗ a ∗
    dghostVar E.γbe (DFrac.own (1 : Qp).half.half) d ∗ srvWTStockInv γp d ∗
    monoNatAuthOwn γp 1 a ∗
    (mvcc.bkRTx d.γB d.P d.be ∨ ∃ q : Qp, dghostVar E.γbe (DFrac.own q) d))
```
- The tokens leave the pool for a stock named by the backend `d`, which never changes. A take
  (`srvWTStock_take`) puts a receipt into the pool (the count `a` up by one) and takes a token from
  `d`'s stock, whose lower bound of the count keeps `receiptBound ≤ m + n + 1`.
- So the supply of any backend with a stock is persistent (`kbWTSupplyM_of_stock : srvWTPoolR E γp
  ∗ srvWTStockInv γp d ⊢ mvcc.kbWTSupplyM (some d)`). A job's supply of the old backend stays good
  after the swap, and the swap still gathers all of `E.γbe`.
- `srv_be_swapR` (proved): `srv_be_swap` with `srvWTStockInv γp d'` in place of `ownToks d'.γB.wb
  n'` and its bound, and without handing out the old backend's tokens (`backend.Close` needs the
  `bOpen` shares, not write tokens).
- The new backend's stock is made from its fresh tokens *before* `Restore` (`srvWTStock_alloc`,
  `snap_supply_before`), because `Restore` needs the supply when `restore()` resumes a compaction.
  The walk takes its three hook and commit tokens first (ghost reordering).
- It needs no more tokens than today: one stock of `receiptBound - 1` per backend, as the pool's
  today. The shared counter bounds all takes together. It follows R2-7 (the supply from the server's
  write budget).
- One cost: the take at the current backend (`srvWTPoolR_take_extra_d`, D22's
  `srvWTPool_take_extra_d`) needs a later credit, since the stock's fact sits under the pool's `▷`.
  Its 8 callers have one from their steps.

**Alternatives, for the user (Q4 below):**
- (b) **A second stock per backend, apart from the pool** (Q1's (c) again). A receipt-backed
  invariant of its own counter per backend (`kbWTSupplyM_alloc`, step 1's law). The D22 pool and
  swap are unchanged. Each backend needs about twice the receipt bound in tokens:
  `hrbw : receiptBound GF ≤ backend.wbInit - 6` becomes about `2 * receiptBound GF ≤ wbInit - 7` in
  `NewServer`/`start`/`specSnap`. This departs from R2-7.
- (c) **A lease: a fraction of `E.γbe` lent to the jobs through the queue**, returned at `Stop`.
  Rejected: the compaction `restore()` resumes runs inside `Restore`, *before* the swap moves
  `E.γbe` to `d'`, so no fraction at `d'` exists yet.

### D22's statements that change (for the collaborator; drafted, nothing edited)

Each drafted in `etcdserver/M2StorageDraftRestore.lean` (Lean) or as text here:
1. **`srvEnvOk`** (`InvApplier.lean:478`): `∧ d.cm = false` becomes `∧ d.cm = E.cmp`, over N1's
   `apply.AEnv` with `cmp` (`srvEnvOkD`; `srvEnvOkD_off`: today's at `E.cmp = false`). The two
   other `∃ d, E.γ.kb = some d` facts of Q5-4 (`InvApplier`'s `:554`, `:830`) go back to having no
   `cm` clause.
2. **`applySnapshot.specSnap`** (`EtcdServer__applySnapshot.lean:54`):
   - `(hcm : d.cm = false)` goes;
   - new parameters `(c c' : Int)`, `(hcc : c ≤ c')` and `(hkI : mvcc.keyImageM d.cm ([[], []] ++ R)
     c' D)`, in place of `hkI : mvcc.keyImage …`. `keyImageM` is to define: off, today's `keyImage`
     and `c' = -1`; on, the image's `Key` bucket thinned at `c'` and its meta records with that
     revision. These are S-j1's premises to discharge;
   - pre `srvKVCloser s E` becomes `srvKVCloserM s E c`, and `srvWTPool E γp` becomes
     `srvWTPoolR E γp`;
   - post: the closer at the new environment `srvKVCloserM s E' c'`.
3. **The walk** (`SnapApplyWalk.lean`):
   - `:55`: `(hcm : d.cm = false)` goes, with the same new parameters as `specSnap`;
   - `:291-293`: the new backend at the old mode, `{ d with γB := γB, be := nb, gx := gx' }` (no
     `cm := false`), so `hcm' : d'.cm = d.cm`;
   - `:385`: `storeBackendT_of_backend … hcm'` (off only). On, the compacting bridge
     (`mvcc_backend_bridge` over `storeDlReg d'.γB γi`, `fkV`, the safe-range slot), with
     `dlNoDel_fix` (`:288`) replaced by `storeDlReg_fix` by the mode;
   - `:391-399`: the image's view and `kbNoCmp` become `restoreImageM` (by the mode, from `hkI`);
   - `:400`: `hRst : watchableStore.Restore.spec` becomes `.specM`, at `c c'`, with the pre's
     `restoreRightM` from `restorePre_of_applyM`, the new slot `kbSRM (some d')` (the new backend's
     `srSlot`) and the supply `kbWTSupplyM (some d')` (`snap_supply_before`);
   - `:406-408`: `⌜∃ d, … ∧ d'.cm = d.cm⌝` in place of the two `cm = false`;
   - `:461`: `srv_be_swap … (wbInit - 5) …` with the tokens becomes `srv_be_swapR … d'` with
     the stock fact, the stock made before `:400` from `wbInit - 5` tokens;
   - `:808`: `hcm'` is `d'.cm = d.cm`;
   - the post's closer by `snap_closer_after`, and the old job's budgets `compactJobResM (some d)`
     (`Restore.specM`'s post) to the old backend's `Close` with the readers.
4. **`SnapApplyDefs`**: `:66`/`:69` drop `cm := false` (the record keeps `d.cm`); `:95` and `:181`:
   `d'.cm = false` becomes `d'.cm = d.cm`.
5. **`SnapApplyIsServer.lean:49`** (`snap_isServer`): `(hcm' : d'.cm = false)` becomes `(hcm' :
   d'.cm = E.cmp)` (`srvEnvOkD_mode_step`); `:64` passes it.
6. **`SnapApplyPost.lean:116-155`**: `hcm'` as above; the closer re-made by `snap_closer_after`.
7. **`srvKVCloser`** (`InvWatchBuilt.lean:70`): by the mode, `srvKVCloserM s E c` (off: today's at
   `c = -1`, `srvKVCloserM_off`; on: `∃ wsl, srvKVAddr s ↦□ … ∗ mvcc.wsCloserR wsl E.s E.γ c`). Its
   readers are `NewServer.spec`'s post (`srvKVCloserM_of_new` after the last error return, on),
   `specSnap`, the walk and `run`'s state.
8. **`RestorePre.restorePre_of_apply`** (`RestorePre.lean:54-80`): becomes `restorePre_of_applyM`
   (proved, no `sorry`). Pre `srvKVCloserM s E c`, post `mvcc.restoreRightM E.s γw.st c` in place
   of `mvcc.storeCloser E.s γw.st ∗ mvcc.crevFrozen γw.st`. Off, the frozen fact is the watchable
   store's `Hfrz` (at the switch `isWatchableStoreD_frozen`); on, none is needed.
9. **`srvWTPool`** (`InvApplier.lean:819`), `srvWTStock`, `srvWTPool_alloc` (`:870`), the take laws
   (`srvWTPool_take_extra_d` `:1040`, `_extra`, `_two`, `_at`: a later credit each) and
   **`srv_be_swap`** (`SnapApply.lean:119`): as drafted (`srvWTPoolR`, `srvWTStockInv`,
   `srv_be_swapR`); `start`'s allocation makes the boot backend's stock and the pool.
10. **SNAPSHOT-SORRY #8** (`EtcdServer__run.lean:811`, `:1332`): its job calls `specSnap` with the
    compaction revision `c` of the server's closer and the image's `c'`, and `c ≤ c'` from the
    apply side's model. **Gap**: the KV model of the raft log (`kvRaftOf`) does not track the
    compaction revision yet (the apply loop's `Compaction` arm is not in scope).

### Glue proved (against the drafted statements)

- mvcc: `compactRightR_of_closer`, `storeStopR_reclaim`, `fieldShare_reclaim` (the right's two
  eighths back to the closer's quarter after `Stop`), `wsCloserR_of_wsCloser`, `wsCloserR_split`,
  `wsCloserR_join`, and the two off-mode laws `spec_of_specM`.
- etcdserver: `srvWTStock_take`, `kbWTSupplyM_of_stock`, `srvWTStock_alloc`,
  `srvWTPoolR_take_extra_d`, `srv_be_swapR`, `srvEnvOkD_off`, `srvEnvOkD_mode_step`,
  `srvKVCloserM_of_new`, `restorePre_of_applyM` (either mode), `snap_supply_before`,
  `snap_closer_after` (`Restore.specM`'s post to the new closer, either mode).
- The restore step composes at the level of its interfaces: `restorePre_of_applyM` gives exactly
  `watchableStore.Restore.specM`'s `restoreRightM` with the watchable store's own parts set aside.
  `snap_supply_before` gives its supply, and `snap_closer_after` takes its `restoreRightPostM`
  back with those parts. The mode step keeps `srvEnvOkD`. **Not done:** a Hoare-level glue through
  `hRst : watchableStore.Restore.specM`. The watchable store the walk calls is `kvOwn`'s `ws`, and the
  closer's `wsl` is a separate existential that the walk equates today; it would duplicate the walk.
- **Gaps** (not proved, not drafted in Lean):
  - `store.restore.spec`'s generalization (the index over a thinned bucket);
  - the compaction chain over `storeStopR` (re-proving `scheduleCompaction`, `compactBarrier`,
    `compact`, `updateCompactRev` with the tracked barrier);
  - `schedule`'s `Stop` changes (the run token out, the cancellation payload) and their proofs;
  - `keyImageM`;
  - the apply side's `c ≤ c'`;
  - `Restore.specM`'s proof (`store__Restore.lean`: `writerOwn_off` and `¬ kbCmpM` at `:190`,
    `:295`, `:390` become by the mode; `restore_switch`'s pool refill at `nReaders - 2 - nJobRd`).

### Questions for the user

- **Q4, the supply's source** (above): (a) stock per backend sharing the pool's counter
  (drafted, recommended: no token doubling, R2-7 kept, a later credit in the take laws), (b) a second
  stock per backend (token premise doubled, D22's pool untouched), (c) a lease (rejected: the
  resumed compaction runs before the swap).
- **Q5, the compaction revision across a restore**: (a) logical, `c ≤ c'` a premise (drafted:
  `Restore` never lowers the store's compaction revision, a true and useful fact; the apply side
  must model the compaction revision of the committed log), or (b) physical (`IdxNames.crev` moves
  into `PhysNames`, D22's definitions; `Restore` allocates a fresh authority at `c'`, no premise; the
  spec then says nothing of the revision across the install).
- **Q6, the scheduler's spec** (internal, `schedule`): `Stop` returns the run token and takes a
  cancellation payload, and `updateCompactRev`'s barrier becomes tracked (drafted), instead of
  keeping `schedLive` (which `Restore` cannot have).

### Q2, step 2 block (statements that change; D22's marked)

15. **`mvcc.store.Restore.spec`** (D22's statement, mvcc's Spec): `store.Restore.specM`'s text.
16. **`mvcc.watchableStore.Restore.spec`** (D22's): `watchableStore.Restore.specM`'s text.
17. **`mvcc.store.Compact.spec`**, export **`mvcc_store_Compact`**: `compactRight γ c` becomes
    `compactRightR s γ c` in pre and post (with Q1 (a)'s supply line). `mvcc.compactRight_of_closer`
    is replaced by `compactRightR_of_closer`; `storeStop` and `schedLive` leave `compactJobPre`.
18. **`mvcc.store.restore.spec`** (trusted, the trust boundary): its compaction-mode generalization
    (to design: the gap above).
19. **`schedule.Scheduler.Stop.spec`** (and `fifo.Stop`): its post gains `schedDoneD γ`, and a
    cancellation payload is added. `Scheduler.Schedule.spec`'s untracked arm keeps `schedLive` (no
    longer used by mvcc).
20. **Step 1's drafts revised**: `compactRight_of_wsCloser` becomes `wsCloserR_of_wsCloser` (the
    closer kept); item 14 (the supply's server source) is `kbWTSupplyM_of_stock` (Q4).
21. **D22's** (the collaborator's): `srvEnvOk`; `applySnapshot.specSnap`; the walk
    (`SnapApplyWalk`); `SnapApplyDefs`; `SnapApplyIsServer`; `SnapApplyPost`; `srvKVCloser`;
    `restorePre_of_apply`; `srvWTPool`, `srvWTStock`, `srvWTPool_alloc`, the take laws and
    `srv_be_swap`. These are items 1-9 of "D22's statements that change" above.
22. **`NewServer.spec`/`specCompact`**: the post's `srvKVCloser` becomes `srvKVCloserM s E (-1)`.

### Checked

- `etc/lean-check.py -a` on both Draft modules.
- Targeted `lake build` of each (mvcc: 2365 jobs; etcdserver: 3651 jobs; no error).
- `#print axioms` of the off-mode laws, `fieldShare_reclaim`, `restorePre_of_applyM`,
  `snap_closer_after`, `srv_be_swapR`, `snap_supply_before`, `srvWTPoolR_take_extra_d` and
  `srvKVCloserM_of_new`: no `sorryAx`.
- The full `lake build` of `c826174109` passed (11208 jobs, no error).
- Go: the reproduction test (`issues/etcd-restore-pending-compaction-unclosed/repro_test.go`) fails
  as the issue says, in 6 runs, 5 of them with `-race`.

**The user's answers on step 2 (2026-10-30).** Q4 (a): one write-token stock per backend, sharing
R2-7's receipt counter (as drafted). Q5 (a): the compaction revision stays logical across a restore,
with the premise `c ≤ c'`; the apply side models the compaction revision of the committed log. Q6:
the `schedule` spec changes approved (`Stop` returns the run token and takes the "stop channel
closed" fact; `updateCompactRev`'s barrier a tracked job).

## After review round 3 (2026-10-30)

The report: `notes/spec-first-study/m2-storage-review-3.md` (on `8d3a172a18`; F1, F2, S1-S7),
committed on its own (`9a510498fd`). Step 1's statements had no first-tier finding (their third
round: converged); step 2's had their first round. Commits: `9a510498fd` (the report), `e327d85393`
(a Go issue, below), `baf2e671ca` (the Drafts), `214ba8a864` (S4), and this notes commit. Nothing
exported, trusted or D22's switched; no `axiom`, no `sorry`; no Perennial change; no generated
file edited.

### F1: the image's compaction records (fixed in the Draft; Q5 (a) has a reachable corner: Q7)

**Go** (`kvstore.go:330-342`, `:389-411`, `store.go:30-36`): `restore()` sets `compactMainRev` to
the finished record (or leaves `-1`), reads the scheduled one as `0` when absent (the found flag is
dropped), and resumes it when it is not `0` and past the finished one (`compactLockfree`, which then
succeeds: `currentRev` was raised to it). So the restored revision is
```lean
def mvcc.CmpRecs.crev (r : mvcc.CmpRecs) : Int := if r.resumes then r.schedRev else r.finRev
-- finRev = fin or -1; schedRev = sched or 0; resumes = (schedRev ≠ 0 ∧ finRev < schedRev)
```
(`mvcc/M2StorageDraftRestore.lean`, "The compaction records"; `CmpRecs` is the pair of `Option w64`
records). A scheduled record of `0` is never resumed.

**The records vocabulary (Draft, the minimal one).** The backend's flag (`fkOwn`, `fkInit D` is 0/1)
tracks only absence; values need one more fact, fixed at the open:
- `backend.fkOpenD γ n v` (persistent): the client's flag stood at `n` when the backend was opened
  over data whose compaction keys hold `v`. At the switch, `OpenBackend`/`New` over bbolt's `D` give
  it at `(fkInit D, (dget D meta fin, dget D meta sched))` beside `fkCl`, on the ghost `γ.fkv`
  already discarded at the open (`fkV γ w` becomes `∃ n v, …` of it: no new name in `BNames`); a put
  of a compaction key raises the flag strictly (`fkPut`: `f` to `f + 1`); `fkOk` gains
  `f = n → the state's keys are v`. So while the client's half stays at `n`, every read returns `v`.
- `mvcc.kbRecs kb γb r := if r = empty then kbNoCmp kb γb else ∃ n, fkOwn d.γB n ∗ fkOpenD d.γB n
  (recBytes r.fin, recBytes r.sched)` (only `empty` over mvcc's assumed backend). Laws, proved:
  `kbRecs_empty` (`= kbNoCmp`), `kbRecs_MW` (it is the compaction-key write right `kbMW`: F1's
  second half, the right the resumed `updateCompactRev` writes through).
- `mvcc.metaReadSpecR rt r Rd Tok`: `metaReadSpec`'s generalization (a read of a compaction key
  returns its record exactly; today's `metaReadSpec rt true` is its value at `empty`). At the switch
  `keyReadLocked`'s meta clause reads `□ (NC -∗ NC ∗ □ metaReadSpecR rt r Rd Tok)` for a new
  parameter `r` (default `empty`), `keyCleanRead` passes it, and the two `UnsafeRead…Compact` specs
  return the record.
- `mvcc.recsOk L r` (each record a revision of `L`, `≥ 0` and `< |L|`); `mvcc.keyImageM cm L r D`
  (D22's image premise by the mode: off, today's `keyImage L D ∧ r = empty`; on, the `Key` bucket
  thinned at `r.crev`, the `Meta` keys holding `recBytes r.fin`/`recBytes r.sched`, `recsOk`,
  `r.crev < |L|`, `NoDelPutAt L r.crev`). S2.5's `imageAt` is renamed `bucketThinnedAt` (S7).
- Not an axiom: the records law is proved in the backend over bbolt's data `D` as `fkCl` already is
  (`Open_kv`, `isDB`, ...: the same axioms). If the backend's re-proof needs a new bbolt-level fact,
  that fact is an axiom and goes through the `axiom` skill before Freeze.

**`restoreImageM` and `Restore.specM`, repaired** (exact text in the Draft):
- `restoreImageM d' γb' L r` (the records `r` in place of `c'`): on,
  `∃ m, kbViewC (some d') γb' 1 m ∗ kbRecs (some d') γb' r ∗ fkV d'.γB true ∗ ⌜recsOk L r ∧
  bucketThinnedAt L r.crev m ∧ r.crev < L.length ∧ NoDelPutAt L r.crev⌝`; off, today's view,
  `kbNoCmp` and `⌜r = empty⌝`. The client's half of the flag (`kbRecs`) is now in the on mode's pre:
  the walk has it from `OpenBackend`'s `fkCl`.
- `store.Restore.specM`, `watchableStore.Restore.specM`: parameters `(c : Int) (r : CmpRecs)
  (f : val) (Pre Q Post : IProp GF)` in place of `(c c' : Int)`; premise `c ≤ r.crev`; the clean
  read's `NC` is `kbRecs (γ.withPhys p).kb (γ.withPhys p).bucket r` (off: `kbNoCmp`;
  `restoreNCM`, whose on mode `True` would have had the clean read promise "no record" of an image
  with records, is gone); new in the pre `mvcc.resumeCsM d' γb' r P' f Pre Q Post` (on and resuming:
  the new backend's hook `kbHookIs (some d') γb' f` and the caller's `csContract P' f Pre Q Post`
  for the resumed `SetScheduledCompact`, as `store.Compact`'s caller gives; else `Pre`); the post's
  right at `r.crev` and `mvcc.resumePostM d' r Pre Post`. The off-mode laws re-proved
  (`spec_of_specM`, at `r = empty`, `Pre = True`).

**`store.restore`, generalized (item 18).** It is **internal and proved** (`store__restore.lean`,
linked in `mvcc/Link.lean`; not in `etc/tcb-baseline.txt`): its Spec header's "the trust boundary
… not yet proved" is stale (fix at the switch). Drafted as `mvcc.store.restore.specR`: today's text
with `kbRecs γ.kb γ.bucket r` in place of `kbNoCmp` (the resource and `isKeyBackendG`'s `NC`),
`recsOk L' r`, the finished record's lock round (`mvcc.revFinW s dql r.fin RevP0 RevP`: `Lock`
lends the lock's part of `compactMainRev`, `Unlock` takes it at the record), and the post `Fin`,
reached through the caller's `mvcc.resumeK s r (restoreDone …) Fin` (resuming: a WP of
`s.compactLockfree(sched)` from `restoreDone`, today's post with `compactMainRev` at the finished
record, to `Fin`; else `restoreDone -∗ Fin`). `store.Restore`'s proof provides `resumeK` from
`compactLockfree.spec`, with the store's invariant re-made at the new names first (today
`physOk` is re-made after `restore` returns, `store__Restore.lean:311`).

**Proof risk (recorded, not a statement change).** With Q5 (a) the logical revision stays at
`c ≥` the old one; when the image resumes a compaction while `c > fin` (a follower that applied
`Compact(5)` installing an image with `fin = 3`, `sched = 5`), `restore()` goes through
`compactMainRev = 3` with the logical revision at 5. No reader sees it (`Restore` holds `s.mu`
exclusively), but `compactLockfree.spec` asks for the lock's normal invariant (`muInvAt`), so
`Restore`'s proof needs a restoring-mode variant of `updateCompactRev`'s step. Internal.

**Q5 (a) checked at SNAPSHOT-SORRY #8: false in a reachable corner (Q7 below; not changed).** With
`c'` what Go computes, `c ≤ c'` fails exactly when `c = 0` and `c' = -1`: a member applied a
client's `Compact(0)` (accepted on a fresh cluster: `0 > -1`; the RPC passes any revision,
`key.go:139`) and the image's compaction at `0` was scheduled but not finished (a leader's snapshot
mid-job, or a leader that restarted in that window and so never finishes it). Then `restore()`
leaves `-1`. Reproduced at the pin (`issues/etcd-restore-scheduled-compact-zero.md`, with
`repro_test.go`: after `Restore`, `compactMainRev = -1` and a re-issued `Compact(0)` succeeds where
the member that applied it answers `ErrCompacted`). No other corner: a scheduled record `≠ 0` past
the finished one is resumed, and every member that applied `Compact(r)` holds `sched ≥ r` in its
image (written with `ForceCommit` in the apply). It is not a soundness problem of the drafted
statement (a false premise), but the caller at #8 cannot meet it, and the store's logical revision
cannot follow Go (it would go from `0` to `-1`). Per the brief this piece is stopped and asked (Q7).

### F2: the scheduler's payload (drafted: `pkg/v3/schedule/M2StorageDraft.lean`, new)

The least change that carries Q6's "stop channel closed" fact to a job:
- **`SchedNames` gains `pay : GName`** (drafted as `schedule.SchedNamesD`): the name of a saved
  proposition the creator fixes. `schedule.schedPayIs γ P := savedProp γ.pay P` (persistent; which
  payload), `schedule.schedPay γ := ∃ P, savedProp γ.pay P ∗ □ P` (persistent; it holds). Laws,
  proved: `schedPay_of`, `schedPay_true`, `schedPay_elim` (`schedPayIs γ P ∗ schedPay γ ⊢ ▷ □ P`).
- **`jobDoSpec`/`jobFnSpec`** (drafted `jobDoSpecD`, `jobFnSpecD`, `jobIsD`): the pre gains
  `□ (cd.PDone -∗ schedule.schedPay γ)` for the context the job is given. Laws, proved:
  `jobFnSpecD_of`, `jobIsD_of` (a job proved against today's contract is one).
- **`NewFIFOScheduler.spec`** (`specD`): `∀ (lg : Loc) (Pay : IProp GF)`, post gains
  `schedule.schedPayIs γ Pay`.
- **`Scheduler.Stop.spec`** (`specD`): pre gains `schedule.schedPay γ`; post gains
  `schedule.schedDoneD γ.toSchedNames` (moved here from mvcc's Draft, with `schedDoneD_excl`).
- **`NewJob.spec`, `Scheduler.Schedule.spec`** (`specD`): today's texts over `jobFnSpecD`/`jobIsD`.
- Internal to `schedule` at the switch: `fifoCtxDesc`'s `PDone := stopped F ∗ schedPay γ`
  (`NewFIFOScheduler`'s `WithCancel`), `fifo.Stop` cancels with it, `executeJob` gives the job the
  implication, the worker gives `dghostVar γ.run 1 ()` to `donecCarry` at exit (`Stop` takes it).

**Its users** (found by grep of the specs' and predicates' names over `Proof/`, `Spec/`):
- mvcc's store: `NewStore`, `store.Restore` make the scheduler with `Pay = mvcc.stopPayD γx`
  (drafted: `∃ c, dghostVar γx □ c ∗ ∃ γc, ownBroadcastChan c γc True .Done`, through an agreement
  name allocated before `NewFIFOScheduler`, since `stopc` is made after the scheduler,
  `kvstore.go:309-310`); `store.Restore`, `store.Close` close `stopc` before `Stop`, so they have
  `schedPay`; `compactBarrier`'s cancelled branch learns `stopc` is `Done`, and Perennial's
  nonblocking receive on a `Done` broadcast needs no proof of the not-ready branch
  (`ownBroadcastChan_nonblocking_receive`): the re-schedule branch is dead, `schedLive` goes
  (`compactBarrier.spec`, `compact.spec`'s job, `updateCompactRev`'s barrier, now tracked through
  the right's queue).
- The server's `run` (`EtcdServer__run.lean`, both proofs: `:531`, `:1052` the `hFifo` call gains
  `iprop(True)`; the snapshot/apply job closures `:863`, `:1384` through `jobFnSpecD_of` or one more
  `-` in their `iintro`; `Stop` is never reached, `run` never returns).
- `etcdserver.scheduler_fifo` (exported, `Results.lean:2252`): text unchanged, over the redefined
  `jobIs`.

### The second tier

- **S1 (`c`'s source at #8), agreed, deferred to Q7.** `keyImageM` is now defined (above), with the
  records `r` as `specSnap`'s parameter and `c' := r.crev`. The KV model's compaction revision
  (`crevOf A`, the closer held at it in `run`'s state, `hcc` as `crevOf_mono`) depends on how Q7
  treats a compaction at `0`; not defined until then.
- **S2.1, fixed** (Q2 item 17's text): `store.Compact.spec`'s pre `mvcc.storeStop s γ ∗
  mvcc.compactRight γ c` becomes `mvcc.compactRightR s γ c` (and the three post disjuncts'
  `compactRight` → `compactRightR`); `updateCompactRev`/`compactLockfree` alike; `compactJobPre`'s
  `storeStop s γ ∗ schedLive γ.sch` becomes `∃ o, storeStopR s γ o`.
- **S2.2, fixed** (Q2 item 24): `mvcc_NewStore_backend_cmp`'s post `mvcc.compactRight γ (-1) ∗
  mvcc.storeStop s γ` becomes `mvcc.compactRightR s γ (-1)`; its docstring's route to the reader's
  token becomes the `fieldShare` quarter's own `curAt`.
- **S2.3, fixed**: the job contract (F2), Q2 item 19.
- **S2.4, agreed**: `store.Close.specM` drafted (`isStore s γ ∗ restoreRightPostM s γ c`; off law
  `Close.spec_of_specM` for a store that does not compact). Q3 does **not** dissolve: unreachable
  today (`run` never returns), and when a shutdown is modelled `Cleanup` closes with the closer by
  the mode. `watchableStore.Close.spec` follows (`wsCloser` → `wsCloserR … c` on). Q2 item 23.
- **S2.5 (the `rfl` break) and the logical mode, decided: a logical mode field.** `StoreNames` gains
  `cm : Bool` (set by `NewStore` to `decide (kbCmpM kb)`, kept by `withPhys`, tied to the backend
  by `physOk`'s `⌜kbCmpM γ.kb ↔ γ.cm = true⌝`); the logical gated predicates read it
  (`wsFrozenM`, `crevRightM`, `restoreRightM`, `restoreRightPostM`, `envAgree`'s clause
  `E.γ.cm = E.cmp`); the backend-keyed ones stay on `kb` (`physCmp`, `nJobRd`, `kbSRM`,
  `kbWTSupplyM`, `compactJobResM`: they describe the backend's budgets). Reasons: every `withPhys`
  law stays `rfl` (`isWatchableStore_withPhys`, so D22's two walk sites need nothing); the mode then
  never moves on restore by construction, which ends the churn class the round names (S5' for good:
  one reading); `d'.cm = d.cm` is needed only where `Restore` re-ties `physOk`. Cost: one field and
  one `physOk` conjunct (internal), the `StoreNames` constructors (`NewStore`, the Drafts). Not
  written in Lean (the Drafts read `γ.kb`, equal under `Restore.specM`'s `d'.cm = d.cm`); a switch
  item (Q2 item 26). `notes/decisions.md` entry to add at the switch.
- **S2.6, fixed**: `compactRight_of_wsCloser` dropped from step 1's Draft and from item 6;
  docstrings point to `wsCloserR_of_wsCloser`.
- **S3, the corner: Q7** (and the issue file).
- **S4, fixed by construction** (`214ba8a864`): `storeStopR s γ o` holds the eighth at **fixed**
  objects `o` (`compactRightR := crevUB ∗ queue ∗ ∃ o, storeCloserR s γ o ∗ storeStopR s γ o`;
  `compactJobPre` carries `∃ o, storeStopR s γ o`). While the eighth is in the invariant no one can
  write the fields, and `Restore` reclaims it only after `Stop`, then moves to fresh names; so every
  read by a job is at the same `o`, as today's discarded `curAt` gives it. `fieldShare_reclaim` no
  longer needs `curAt_agree`. The remaining risk of re-proving `scheduleCompaction` over it is the
  per-read invariant opening (an atomic load each, the job holding the run token): mechanical.
- **S5, agreed and fixed.** `srvWTPoolR` changes the off server's statements too: all eight take
  sites need `£ 1` (item 21 now says so: "not read as today"). The compaction arm's law drafted and
  proved: `kbWTSupplyM_of_poolR : srvWTPoolR E γp -∗ srvBeOwn s E -∗ £ 1 ={⊤}=∗ srvBeOwn s E ∗
  mvcc.kbWTSupplyM E.γ.kb` (etcdserver Draft); item 14's source.
- **S6, fixed in the Drafts**: `wsFrozenM`'s docstring (the mode by `d'.cm = d.cm`, the logical
  field at the switch), `crevRightM`'s and `New.specD`'s references, the etcdserver Draft's header,
  `store.Compact.specD`'s supply paragraph (now `kbWTSupplyM_of_poolR`). Left for the switch (an
  edit to `InvStore.lean`'s docstrings rebuilds its importers): `writerOwn`/`writerOwn_off`'s "never
  in compaction mode", `kbCmpM`'s and `KBReal.cm`'s "no restore in compaction mode", `physCmp`'s "a
  compacting store is never restored", `compactRight_of_closer`'s and `storeStop`'s "never
  restored", `store__restore.lean`'s "trust boundary" header.
- **S7, fixed**: `restorePre_of_applyM` uses the law `mvcc.isWatchableStore_frozen` (new, today's
  predicate; `isWatchableStoreD_frozen` at the switch) in place of the unfold; `storeStopR`,
  `storeCloserR`, `compactRightR`, `wsCloserR` sealed (`@[no_expose]`; the server uses only
  `wsCloserR_split/_join`, `restoreRightM_on/_off`, `restoreRightPostM_on/_off`); `mvcc.imageAt`
  renamed `bucketThinnedAt`.

### Statements for the user's approval (Q2), complete after round 3

Each: the statement; the drafted text (module, or here); step; D22's (the collaborator's) or not;
axiom-backed or not. "mvcc D" = `mvcc/M2StorageDraft.lean`, "Supply" = `mvcc/M2StorageDraftSupply.lean`,
"mvcc R" = `mvcc/M2StorageDraftRestore.lean`, "srv R" = `etcdserver/M2StorageDraftRestore.lean`,
"sched" = `pkg/v3/schedule/M2StorageDraft.lean`. None is axiom-backed unless said.

1. `mvcc.New.spec` (linked): `New.specD`, mvcc D. Step 1. Not D22.
2. `mvcc.newWatchableStore.spec`: `newWatchableStore.specD`, mvcc D. Step 1.
3. `mvcc.NewStore.spec`: `NewStore.specD`, Supply. Step 1.
4. `mvcc.store.Compact.spec` / export `mvcc_store_Compact`: `store.Compact.specD`, Supply (step 1:
   the supply line), with item 17's change (step 2).
5. Exports `mvcc_NewStore_backend`, `mvcc_NewStore_backend_cmp` (pre): Supply. Step 1.
6. mvcc in place: `isWatchableStore` (`wsFrozenM`, at the switch over the logical mode, item 26),
   `watchStoreInv` (`wsWatchFrozen`), `storeWatchParams` (`T` with `noCompactor`); new exported names
   `noCompactor` (sealed) and its laws, `wsFrozenM`, `crevRightM`, `noCompactor_of_new`,
   `isWatchableStore_frozen`. mvcc D. Step 1. (`compactRight_of_wsCloser` dropped.)
7. v3rpc in place: `upOk`/`watchUp` create arm; laws `isWatchServer_noCompactor(_env)`,
   `isWatchServer_link`. `api/v3rpc/M2StorageDraft.lean`. Step 1.
8. client in place: `watchMemberFacts`, `watchAddrFacts` (`noCompactor` appended), `watchConnFacts`.
   `client/v3/M2StorageDraft.lean`. Step 1.
9. `apply.AEnv`: field `cmp`. etcdserver `M2StorageDraft.lean`. Step 1.
10. `envAgree`: `envAgreeD` (the mode clause; at the switch `E.γ.cm = E.cmp`, item 26). Step 1.
11. `NewServer.spec`/`specM` (`E₀.cmp = false →`), `specCompact` (`E₀.cmp = true →`; trusted until
    proved: its proof is `sorry`). Text in "Step 1 on the merged lean". Step 1.
12. examples/common `env₀`, `memberBoot` (`cmp`), `newServer.specCompact`,
    `StartCompactingServer.spec`, `memberBootOn`: `examples/common/M2StorageDraft.lean`. Step 1.
13. `etcd_cache_served` (exported), watchkv's `wk_served`, linkv3p's `memberWatch`/`memberAt`:
    their Drafts. Step 1.
14. The supply's server source: `kbWTSupplyM_of_poolR`, srv R (over `srvWTPoolR`, D22's). Step 2.
15. `mvcc.store.Restore.spec`: `store.Restore.specM`, mvcc R. Step 2. **D22's.** Rests on
    `store.restore` (proved), `Stop` (proved).
16. `mvcc.watchableStore.Restore.spec`: `watchableStore.Restore.specM`, mvcc R. Step 2. **D22's.**
17. `mvcc.store.Compact.spec` / `mvcc_store_Compact`: pre `storeStop s γ ∗ compactRight γ c` →
    `compactRightR s γ c`, post's `compactRight` → `compactRightR` (text above, S2.1); internal
    `updateCompactRev`, `compactLockfree`, `compactJobPre`, `compactBarrier`. Step 2. Not D22.
18. `mvcc.store.restore.spec` (internal, proved; not the trust boundary): `store.restore.specR`, mvcc
    R; the switch-internal `keyReadLocked`/`keyCleanRead` (`r`), `UnsafeRead…Compact`, and the
    backend's `fkOpenD`/strict `fkPut`/`fkOk` (backend's, proved over bbolt's existing axioms). Step
    2. Not D22.
19. `schedule`: `SchedNames.pay`, `jobDoSpec`/`jobIs`/`jobFnSpec`, `NewJob.spec`,
    `Scheduler.Schedule.spec`, `NewFIFOScheduler.spec`, `Scheduler.Stop.spec`: sched (all proved
    today, linked; not axiom-backed). Knock-on: `run`'s two proofs, mvcc's `NewStore`, `Restore`,
    `Close`, the compaction chain; exported `etcdserver.scheduler_fifo` (text unchanged). Step 2.
20. Step 1's drafts revised: `compactRight_of_wsCloser` → `wsCloserR_of_wsCloser` (mvcc R). Step 2.
21. **D22's** (the collaborator's; items 1-9 of "D22's statements that change", with):
    `applySnapshot.specSnap`'s parameters `(c : Int) (r : mvcc.CmpRecs)`, `hcc : c ≤ r.crev`,
    `hkI : mvcc.keyImageM d.cm ([[], []] ++ R) r D` (mvcc R); the walk builds `restoreImageM` from
    `hkI`, `fkCl` and the backend's `fkOpenD`, the clean read at `kbRecs … r`, and `resumeCsM` from
    the server's hook contract; `srvWTPoolR` changes the off server's statements (each take law and
    its eight sites need `£ 1`: not read as today). Step 2.
22. `NewServer.spec`/`specCompact`: post's `srvKVCloser` → `srvKVCloserM s E (-1)` (srv R). Step 2.
    D22's predicate (S-g).
23. `mvcc.store.Close.spec`: `store.Close.specM`, mvcc R; `watchableStore.Close.spec` alike. Step 2.
    Not D22.
24. Export `mvcc_NewStore_backend_cmp`'s post: `compactRightR s γ (-1)` (S2.2). Step 2.
25. `mvcc.isWatchableStore_withPhys` (D22's, `RestorePre.lean:101`): stays `rfl` with item 26 (no
    change); without item 26 it would need `kbCmpM p.kb ↔ kbCmpM γ.st.kb`. Step 2. **D22's.**
26. `mvcc.StoreNames`: the logical mode field `cm` (internal definition; `withPhys` keeps it;
    `physOk`'s tie). Step 2. Read by D22's `withPhys` laws.

26 items; D22's: 15, 16, 21, 22, 25 (and 14 over D22's pool). Axiom-backed: none (18's backend part
would be, if its re-proof needed a new bbolt fact).

### Questions for the user

- **Q7, Q5 (a) in the `Compact(0)` corner** (found by the round's S3, reproduced): with `c'` what
  `restore()` computes, `c ≤ c'` is false when a member applied a client's `Compact(0)` and the image
  it installs holds that compaction scheduled but unfinished (`c = 0`, `c' = -1`); after the install
  Go's revision is `-1`. Options:
  - (a) **keep Q5 (a), exclude the corner by a premise of M2's scope**: the apply's compaction arm
    assumes `rev ≠ 0` (M2's compactor, `v3compactor`, never issues `0`: `revision.go:82` skips
    `rev <= 0`, the periodic one takes `≥ 1`); a client's `Compact(0)` RPC is then out of scope (a
    stated limit, as P4 was). Cheapest; the issue file records why.
  - (b) **keep Q5 (a), identify `0` with `-1` in the model**: the KV model's and the store's
    compaction revision count a compaction at `0` as none (they delete nothing; reads at `≤ 0` mean
    "current"); the store's tie becomes `compactMainRev ∈ {c} ∪ {0 | c = -1}`, and `store.Compact`'s
    spec at `rev = 0` allows both answers (`ErrCompacted` or success). Exact, but changes the store's
    invariant and an exported spec.
  - (c) **Q5 (b) after all**: the compaction revision physical (`IdxNames.crev` into `PhysNames`),
    a fresh authority at `r.crev` on restore, no premise; the spec then says nothing of the revision
    across an install.
  - (d) fix etcd (the issue's fix: resume a *found* scheduled record past the finished one) and bump
    the pin; then Q5 (a) holds as drafted.

  Recommended: (a) now (M2's programs never compact at `0`), (d) as the upstream report.

### Checked

- `etc/lean-check.py -a` on every changed Draft (`schedule`, mvcc's three, etcdserver's two).
- Targeted `lake build` of the twelve Draft modules (7145 jobs, no error), then of the two Restore
  Drafts after S4 (4342 jobs, no error).
- `#print axioms` of `kbWTSupplyM_of_poolR`, both `Restore.spec_of_specM`, `Close.spec_of_specM`,
  `kbRecs_MW`, `jobIsD_of`, `jobFnSpecD_of`, `schedPay_elim`, `restorePre_of_applyM`: no `sorryAx`.
- Full `lake build` of `214ba8a864` passed (11209 jobs, no error).
- Go: `issues/etcd-restore-scheduled-compact-zero/repro_test.go` fails at the pin as the issue says.

**The user's answers after round 3's repair (2026-10-30).**
- **Q7 (a):** keep Q5 (a) (`c ≤ c'` across a restore) and make "no compaction at revision 0" a stated
  scope limit of M2 (M2's auto-compactor never issues 0; a client's `Compact(0)` RPC is out of scope).
  `issues/etcd-restore-scheduled-compact-zero.md` goes upstream separately. To draft: where the premise
  sits (the compaction arm's request, or the apply model) and how #8 discharges `c ≤ c'` from it.
- **The snapshot track's statements** (Q2 items 15, 16, 21, 22, 25) stay drafts: the collaborator
  switches them, ideally when proving SNAPSHOT-SORRY #8. Everything else M2 switches itself once approved.

## After review round 4 (2026-10-30)

The report: `notes/spec-first-study/m2-storage-review-4.md` (on `f3282099c3`; A1, A2, S1-S6),
committed on its own (`f4194ecc72`). This is step 2's second repair; the next review is its third
and last round. Per the plan's Review step, this repair settles A1/A2 by evidence (proofs and
counterexamples in Lean), not prose. Commits: `f4194ecc72` (the report), `6e162e38f7` (the index,
pure), `e39f87edb6` (the records vocabulary, the nil-hook arm, `specR`), `2070c2b8f0` (Q7's vehicle,
the chain, the leftovers), and this notes commit. Nothing exported, trusted or D22's switched; no
`axiom`, no `sorry`; no Perennial change; no generated file edited. New Draft modules:
`mvcc/M2StorageDraftIndex.lean` (pure), `mvcc/M2StorageDraftChain.lean`,
`etcdserver/M2StorageDraftScope.lean`.

### A1: what was proved, what is missing

**(a) The records, read: proved composable.** The backend vocabulary takes the records `r`
(mvcc R, "The backend vocabulary with the records"): `metaReadSpecR` (at no record *equal* to
today's `metaReadSpec rt true`), `keyReadLockedR`, `keyReadSnapR`, `keyReadSnapCR`, `keyCleanReadR`,
`isKeyBackendGR`, `storeBackendTR`, `restoreViewR` (over the image's bucket `m`), each with its
`_empty` law, an equation with today's. `restore()`'s two reads over it are **proved**
(`UnsafeReadFinishedCompact.wp_proofR`, `UnsafeReadScheduledCompact.wp_proofR`: the record, exactly).
`Restore.specM` (both) now take `storeBackendTR … r` and `keyCleanReadR … (kbRecs … r) r`; the
off-mode laws are re-proved over them.
**Missing:** `keyCleanRead_of_backendC` (stated as `mvcc.keyCleanRead_of_backendC_stmt`, the bridge
law the walk needs: over `storeDlReg` instead of `dlNoDel`, at the records the client's flag stands
at since the open). Its proof needs one backend fact, backend-internal: `fkOk`'s clause
`f = n → the state's compaction keys are v` (the merged ghost `fkVD γ w n v`, drafted), set at the
open from bbolt's data `D` as `fkCl` already is, kept by every operation but a compaction-key put
(which raises the flag). Expected over the backend's existing bbolt axioms; if the re-proof needs a
new bbolt fact, that fact is an axiom: the `axiom` skill before Freeze.

**(b) The index over a compacted bucket: today's invariant is false there; repaired, and its pure
theorem stated.** Evidence, proved in `M2StorageDraftIndex.lean`:
- **`idxCRep_restore_counterexample`**: log `[[], [], [put a], [del a]]`, compaction at `3`; the
  bucket keeps only the tombstone; `restoreTombstone` builds `{created 0, ver 1, [3]}`, while every
  compaction of the log's key index at a level the lock's invariant allows keeps the put or the
  header `created 2`. So `IdxCRep` (the `RWMutex` resource's `HL`) **cannot hold** after `restore()`
  over a compacted image, and `idx_publish` (which takes `IdxCRep (-1)`) cannot be used there.
- **The repair (a modelling choice, internal to mvcc):** compare key indexes up to the header of a
  generation that is not the last and has one revision (`kiNorm`, `IdxCRepN`), which nothing reads:
  **`kiGet_kiNorm`** (proved: `kiGet (kiNorm ki) a = kiGet ki a`, the scan never stops at such a
  generation); `IdxCRepN_of` (today's gives it), `cx_idxCRepN` (it holds in the counterexample).
- **`bucketThinnedAt_counterexample`**: round 3's shape (any deletable subset missing) admits a
  bucket (revision 3 of three puts gone, revision 2 kept) whose rebuilt index answers a read *at the
  compaction revision* with version 2 where the log's says 3. Replaced by **`entsCutAt`**: per key, a
  prefix of its entries deletable at `c` removed (the job deletes from revision 0 up; `KeyDel` is
  monotone in `c`, so a finished earlier compaction's deletions are of the same shape).
- **`cx3_not_compacted`**: a job's batch boundary between two changes of one key in one revision
  leaves an index no level gives, even up to headers: the premise **`KeyOnceAt`** (each key changed
  once per revision up to `c`; etcd's `checkIntervals`). A new apply-side premise, like
  `irrNoDelPut`: in `keyImageM`, from the request shape.
- **`idxRestore_cutStmt`** (drafted, **not proved**): over `entsCutAt`, `KeyOnceAt`, the rebuilt index
  is `IdxCRepN c`. Its route is in the docstring (per key, the first surviving entry is `restore`d
  with the generation's create revision and version: `KvMatch`; compaction commutes with the later
  events: `kiCompact_kiPut`, `kiCompactO_step`; `kiNorm` too). Pure, no trust base. The whole-bucket
  case is proved (`idxRestore_full_N`).

**(c) Two further facts the evidence found (not in the report).**
- **Receipts.** `idxWriter` holds a time receipt per change (`⧗ (logCh ilog)`, D19b), which today's
  restore refills from the rebuild (one step per change: the whole bucket has one entry per change).
  Over a compacted image the rebuild takes one step per *surviving* entry (`revProt`'s
  `⧗ ents.length`), so the restored writer's receipts cannot be had. Drafted: `restoreBoundM`
  (on: `logCh L' < receiptBound`, a premise of `Restore.specM` from the apply side), `specR`'s
  disjunctive premise (the whole bucket or the bound), and `restoreDone`'s `⧗ ents.length`. The
  writer's handle then counts receipts from the last restore (internal). **Q8 below.**
- **The view.** `restore_finish` gives the store's writer `bucketView … (bucketMap L')` (the log's
  bucket: the job's deletions leave the view, only reads miss them). The image's backend view is
  `bucketOfEnts ents`. Needed: a backend law at the open widening the view over keys the
  registration (`storeDlReg`) marks deletable (`kbView_widen`; backend-internal, ghost; not drafted).

**(d) `store.restore.specR`: redrafted; the off-mode law proved; the WP proof not.**
`specR` takes the records vocabulary, the image's entries (`entsCutAt`, `KeyOnceAt`), the index's
lower bound `crevLb γ.idx r.crev`, the receipts' disjunction; its post goes through `resumeK` to
`restoreDone` (a receipt per entry). **`spec_of_specR`** (proved): at no record and the whole
bucket it gives today's `store.restore.spec`. **`wp_proofR` is not proved**: the proof is today's
(`store__restore.lean`, 774 lines) with the reads above (proved) and the found branch's lock round;
what blocks it is the index: `idx_publish` takes `IdxCRep (-1)`, so the proof needs the switch of
`idxLockInv`'s `HL` to `IdxCRepN` (internal; every reader's use of `HL` goes through
`IdxCRep.kiAt`/`rangeAt`, to be re-proved over `kiGet_kiNorm`) and the pure `idxRestore_cutStmt`.
Neither is a backend or bbolt fact; nothing here touches the trust base.

**(e) `Restore.specM`'s premises in the records form, as the walk can build them:** the image by
`restoreImageM` (the entries of the job's shape, `kbRecs`, `fkVM`, `recsOk`, `recsPos`, `entsCutAt`,
`NoDelPutAt`, `KeyOnceAt`) from `keyImageM` (the apply side's) and the backend's `fkOpenD`; the
contract and clean read at the records from the bridge (`storeBackendT_of_backendC` at `r`,
`keyCleanRead_of_backendC`); the unset hook (A2); `restoreBoundM` (Q8).

### A2: the resumed compaction runs no hook

- `resumeCsM`/`resumePostM` are gone. **`resumeHookM d' r`**: on and resuming, the new backend's
  unset hook (`kbHookNil`: the client's half `plHook γB func.nil`, which the walk holds as `HnH`
  until `hSTP`, `SnapApplyWalk.lean:428`), lent and given back. `Restore.specM` lost `f Pre Q Post`.
- **The store-level nil-hook law:** `lockNilSpec` (the clause `batchTxSpecG` gains at the switch:
  `LockInsideApply` with the unset hook gives the lock, `W` and the batch lock's invariant `P`
  itself). **`bt_lockInNil` (proved)** from the backend spec's nil arm, as `bt_lockIn` from the hook
  arm; the bridge passes it through at the switch. At the chain: `lockCtxM`/`lockBackM` (the
  critical section by the hook's state) in `updateCompactRev.specR`/`compactLockfree.specR`.
- **The batch-lock invariant survives** (checked): the server's `P` is `batchLockInv γ TM`; with no
  hook, `LockInsideApply` hands it to the critical section unchanged (`Q := Pk ∗ Pre`), the resumed
  `UnsafeSetScheduledCompact` writes a compaction key (not one `metaTM` tracks), and `Unlock` takes
  `P` back: no update, so no `Pre`/`Q` from the walk. In Go the skipped hook only would have raised
  `consistentIndex` to the applying index; `SetBackend` reset it to `0` and
  `UnsafeUpdateConsistentIndex` skips `0` (`cindex.go:123-129`, `schema/cindex.go:69-73`), so the
  stored index is untouched, as the model's pass-through says.

### Round 3's leftovers and round 4's second tier

- **S2.1 (`isFifo` pins `pay`)**: required at the switch, stated in the schedule Draft
  (`SchedNamesD`'s and `Stop.specD`'s docstrings: as drafted over the extension, `Stop.specD` is
  unprovable; with `pay` a field of `SchedNames`, `fifoCtxDesc` is over the same names). No Lean
  pin is expressible before the field moves. Item 19 says "required".
- **S2.2 (`γx`'s home)**: `PhysNames` gains `sx` (fresh per scheduler), `physOk`'s conjunct
  `stopPayAt p.sx γ.sch o`; **`stopPayAt_done` (proved)**: with the scheduler's payload, a job learns
  the stop channel of *its* objects is closed.
- **S3 (round 3's S2.1/S2.2 as Lean)**: `M2StorageDraftChain.lean`: `compactJobPreR`,
  `store.Compact.specR` (item 17), `updateCompactRev.specR`, `compactLockfree.specR`, and
  **`mvcc_NewStore_backend_cmpR` (proved over `NewStore.specD`, item 24)**. The chain's re-proof over
  `storeStopR` is the switch's (the per-read invariant opening; mechanical).
- **S2.5 (`StoreNames.cm`)**: `StoreNamesD` with `withPhysD` (keeps `cm`, `rfl`), `cmTie`,
  `cmTie_withPhysD`, `restoreRightMC_eq` (proved).
- **S1 (Q7 drafted)**: below. `crevOf` (the KV model's compaction revision) is the apply side's and
  not defined here; named in item 21.
- **S4 (clarity)**: `r.crev < L.length` dropped (`recsOk_crev_lt`, proved); `fkV`/`fkOpenD` merged
  into one ghost at one type (`fkVD`, `fkVM`, `fkOpenD`); `restoreRightPostM` renamed `storeCloserM`
  (also in the etcdserver Draft).

### Q7's premise: where it sits (drafted, `etcdserver/M2StorageDraftScope.lean`)

- **How `kvRaftOf` models proposals**: a fold of the committed raft entries (`kvRaftSt`,
  `KVModelDefs.lean:372`), each decoded and dispatched; a compaction entry adds no revision. The
  apply side's invariant of the committed entries in compaction mode is `plainLogC` (every plain
  entry a plain request or `compactPropOk`, `CompactMode.lean`): the vehicle.
- **The request**: `EtcdServer.Compact.specD` = today's with `1 ≤ r`, marked as M2's scope
  restriction; **`compactableOk_serverD` (proved)**: the compactor's permits carry `0 < r`
  (`revPermit`, `perPermit`), so its statement is `compactableOk_server`'s, unchanged.
- **The log**: `compactPropOkD` (`1 ≤ r`) in `plainEntryCD`/`plainLogCD`;
  `compactPropOkD_irrCompaction` (Compact's proposal makes it); **`plainLogCD_compaction_pos`
  (proved)**: every committed compaction is at `≥ 1`.
- **The storage side**: `recsPos` in `keyImageM`/`restoreImageM`; **`recsPos_crev` (proved)**: the
  restored revision is `-1` or `≥ 1`, so #8's `c ≤ r.crev` is `crevOf_mono` without a corner. Not in
  `store.Compact.spec`, not in `Restore.specM`.

### Statements for the user's approval (Q2), complete after round 4

Each: the statement; the drafted text; step; D22's (snapshot track: the collaborator switches it) or
not; axiom-backed or not. **[now]**: the user can approve it now; **[waits]**: on what. "mvcc R" =
`mvcc/M2StorageDraftRestore.lean`, "Index" = `mvcc/M2StorageDraftIndex.lean`, "Chain" =
`mvcc/M2StorageDraftChain.lean`, "Scope" = `etcdserver/M2StorageDraftScope.lean`; the others as in
round 3's list. None is axiom-backed unless said.

1-3, 5-14: unchanged from round 3's list (step 1; converged in round 3). **[now]**
4. `mvcc.store.Compact.spec` / `mvcc_store_Compact`: the step-2 text is Chain's `store.Compact.specR`
   (Supply's supply line and item 17's right). **[now]** (text; the chain's re-proof at the switch).
15. `mvcc.store.Restore.spec`: mvcc R's `store.Restore.specM` (records vocabulary, `resumeHookM`,
    `restoreBoundM`). Step 2. **D22's.** **[waits]** on 32 (the index), Q8 (receipts), 37 (the view).
16. `mvcc.watchableStore.Restore.spec`: `watchableStore.Restore.specM`. **D22's.** **[waits]** as 15.
17. The compaction chain: Chain's `updateCompactRev.specR`, `compactLockfree.specR`, `compactJobPreR`
    (internal), with item 4. Not D22. **[now]**
18. `mvcc.store.restore.spec` (internal, proved today): mvcc R's `store.restore.specR`
    (`spec_of_specR` proved). Not D22. **[waits]** on 32.
19. `schedule` (round 3's list), with `pay` a field of `SchedNames` **required** (S2.1). **[now]**
20. `wsCloserR_of_wsCloser` (mvcc R). **[now]**
21. **D22's** (round 3's items 1-9), with round 4's changes: `specSnap`'s `hkI : keyImageM` (now
    `recsPos`, `entsCutAt`, `KeyOnceAt`), its `restoreBoundM` premise (Q8), `c` the closer's
    revision `crevOf A` (S1: the KV model's compaction revision, the apply side's, not defined); the
    walk builds `restoreImageM` from `hkI`, `fkCl`, `fkOpenD`, the contract and clean read at the
    records from `storeBackendT_of_backendC`/`keyCleanRead_of_backendC`, and lends `HnH` as
    `resumeHookM` (no server contract). **[waits]** with 15.
22. `NewServer.spec`/`specCompact`'s `srvKVCloserM s E (-1)`. D22's predicate. **[now]**
23. `mvcc.store.Close.spec`: `store.Close.specM` over `storeCloserM`. **[now]**
24. Export `mvcc_NewStore_backend_cmp`'s post: Chain's `mvcc_NewStore_backend_cmpR` (proved). **[now]**
25. `mvcc.isWatchableStore_withPhys` (D22's): no change with 26. **D22's.** **[now]**
26. `mvcc.StoreNames.cm`: mvcc R's `StoreNamesD`, `cmTie` (internal). **[now]**
27. **The backend vocabulary with the records** (round 4's S6.1; used by D22's `Restore.specM` and
    walk, so not switch-internal): `metaReadSpecR`, `keyReadLockedR`, `keyReadSnapR`, `keyReadSnapCR`,
    `keyCleanReadR`, `isKeyBackendGR`, `storeBackendTR`, `restoreViewR` (mvcc R; each `_empty` =
    today's). Step 2. Snapshot track uses it. **[now]**
28. `UnsafeReadFinishedCompact.spec`/`UnsafeReadScheduledCompact.spec` over the records (`specR`,
    proved; internal). **[now]**
29. The records: `CmpRecs` (`crev`, `resumes`), `kbRecs`, `recsOk`, `recsPos`, and the backend's merged
    ghost `fkVD`/`fkVM`/`fkOpenD` with `fkOk`'s records clause (the backend's, proved over bbolt's data
    as `fkCl`). **[now]** for the vocabulary; axiom-backed only if the backend's re-proof needs a new
    bbolt fact (then the `axiom` skill).
30. **`keyCleanRead_of_backendC`** (new exported bridge law; mvcc R's `_stmt`). Snapshot track uses it.
    **[waits]** on 29's backend clause.
31. **The nil-hook law**: `lockNilSpec` as `batchTxSpecG`'s clause, `kbHookNil`, `resumeHookM`,
    `lockCtxM`/`lockBackM` (mvcc R, Chain); `bt_lockInNil` proved from the backend's existing spec.
    Not axiom-backed. **[now]**
32. **The index over a compacted bucket** (internal): `idxLockInv`'s `HL` over `IdxCRepN`/`kiNorm`
    (Index), `entsCutAt` in place of `bucketThinnedAt`, `idx_publish` at `r.crev`. **[waits]** on
    `idxRestore_cutStmt`'s proof (pure, no trust base).
33. `KeyOnceAt` (Index): a new premise of the image, the apply side's (from the request shape, as
    `irrNoDelPut`). Snapshot track's `specSnap`. **[now]** (the premise; its source is the apply side's)
34. `γx`'s home: `PhysNames.sx`, `physOk`'s `stopPayAt` (mvcc R; internal). **[now]**
35. **The Q7 premise** (Scope): `EtcdServer.Compact.spec`'s `1 ≤ r`, `compactPropOkD` in `plainLogC`,
    `recsPos` in `keyImageM`. M2's scope restriction (`issues/etcd-restore-scheduled-compact-zero.md`).
    **[now]**
36. `restoreBoundM` (mvcc R): **[waits]** on Q8.
37. `kbView_widen` (backend, at the open): not drafted. **[waits]**

37 items; D22's: 15, 16, 21, 22, 25 (and 27, 30, 33 used by them). Approvable now: 1-14, 17, 19, 20,
22-29, 31, 33-35. Waiting: 15, 16, 18, 21, 30, 32, 36, 37.

### Questions for the user

- **Q8, receipts for a compacted image** (found by drafting `specR`): the index writer's receipt per
  change cannot be refilled when `restore()` rebuilds from fewer entries than the log has changes.
  (a) **the bound from the apply side**: `logCh L' < receiptBound` a premise of `specSnap` (the
  committed log's changes below the bound: an invariant of the KV model, or a scope premise as the
  `2^48` bound is), and the writer's handle counts receipts from the last restore (internal to mvcc;
  recommended); (b) a configuration bound only (the server's total changes below `receiptBound`, a
  scope premise of M2 stated at `NewServer`); (c) drop the receipt device for the index writer in
  favour of a pure bound carried in `IdxWf` (D19b reversed; larger).

### Checked

- `etc/lean-check.py -a` on every changed or new Draft.
- Targeted `lake build` of the 15 Draft modules (7148 jobs, no error).
- No `axiom`, no `sorry` in any Draft (grep).
- Full `lake build` of `40cfa3ae75` passed (11212 jobs, no error).

**The user's answer on Q8 (2026-10-30): (a)**, the receipt bound for a restored compacted image is
`Restore`'s premise `restoreBoundM`, supplied by the apply side; the index writer counts receipts from
its last restore. No configuration premise.

## After review round 5: the user's decisions (2026-10-30)

Round 5 (`notes/spec-first-study/m2-storage-review-5.md`) was step 2's third and last review round.
- **Q2: the 28 approvable items approved** (1-14, 17, 19, 20, 22-29, 31, 34, 35), with round 5's text
  fixes (S1, S4, S5). To switch on `m2-storage`, except the snapshot track's (22, 25: drafts for the
  collaborator). The 9 waiting items (15, 16, 18, 21, 30, 32, 33, 36, 37) stay drafts.
- **B1: the index invariant's compaction level becomes a full revision** (main and sub), removing
  `KeyOnceAt` (item 33) and its apply-side obligation (`issues/etcd-txn-check-intervals-sibling.md`
  shows it is no etcd guarantee).
- **B2: Q8 becomes (b)**, a configuration bound: a stated premise at `NewServer` that a log's changes
  stay below the receipt bound, covering every restored image (supersedes Q8 (a)). A new trusted
  premise, approved in principle; its exact text comes with the restore chain.
- No more review rounds for step 2's waiting items: they are settled by proofs and glue against the
  real callers (the index rebuild theorem, the backend's records clause, the view widening).

## The switch of the approved items (2026-10-30)

The user approved 28 items after round 5 (all but the snapshot track's 22 and 25 to switch here),
with round 5's S1, S4, S5. Done on `m2-storage`: the drafted texts redefined in place (`…D` → the real
names), every affected proof re-proved, the Draft copies that became real deleted, the rest of the
Drafts kept building against the switched statements. No `axiom`, no `sorry`, no Perennial change,
no generated file edited.

### Switched

- **Items 1-3, 5** (`New.spec`, `newWatchableStore.spec`, `NewStore.spec`, the exports
  `mvcc_NewStore_backend(_cmp)`'s pre): the pre loses `kbWTSupplyM kb` (Q1 (a)); `New`/
  `newWatchableStore` give `crevRightM γ.st` beside the closer (P3, `crevRight_split` in
  `newWatchableStore`'s proof). With item 26 the three creation posts also state the logical mode,
  `γ.cm = decide (kbCmpM kb)` (appended to the pure facts: the tie is in `physOk`, under the fields'
  shares, so a client reads the mode off the post).
- **Item 4, its step-1 text** (`store.Compact.spec`, `mvcc_store_Compact`, internal
  `updateCompactRev`/`compactLockfree`): the pre's supply line `kbWTSupplyM γ.kb`; `physCmp` loses the
  supply, `compactJobPre` carries it. The step-2 text (`compactRightR`) stops with item 17, below.
- **Item 6** (mvcc in place): `isWatchableStore`'s `Hfrz` is `wsFrozenM γ.st`; the lock's body gains
  `wsWatchFrozen γ σ` (a conjunct of `watchStoreBody`, `watchStoreInv`'s: every step that changes the
  watchers re-establishes it, `watch` from the create token, `syncWatchers`' non-empty branch reads it,
  `wsWatchFrozen_of_Wu`); `storeWatchParams`' `T := watchTok γ ∗ noCompactor γ.st`; new names
  `wsFrozenM`, `crevRightM`, `noCompactor` (sealed) and laws `noCompactor_frozen/_of_frozen`,
  `isWatchableStore_frozen/_isStore/_readView/_noCompactor`, `noCompactor_of_new`, `crevRight_split`.
- **Items 7, 8** (v3rpc, client): `upOk`/`watchUp`'s create arm `watchTok γ ∗ noCompactor γ.st`;
  `isWatchServer_link`, `isWatchServer_noCompactor(_env)`; `watchMemberFacts`/`watchAddrFacts` gain
  `noCompactor V.R.γ.st` (appended), projections `watchMemberFacts_noCompactor/_kv/_st`,
  `watchUp_create`; the client's sites destructure one more conjunct.
- **Items 9-12**: `apply.AEnv.cmp : Bool := false`; `envAgree`'s clause `E.cmp = E'.cmp ∧ E.γ.cm =
  E.cmp` (item 26's reading; laws `envAgree_mode/_off/_on`); `NewServer.spec`/`specM` take
  `E₀.cmp = false`, `specCompact` `E₀.cmp = true`; examples/common `env₀ … (cmp := false)`,
  `memberBoot … (cmp := false)` with `E₀.cmp = cmp` (`memberBoot_cmp`), `memberBootOn` alike,
  `alloc1 … (cmp := false)`, `newServer.specCompact`/`StartCompactingServer.spec` at
  `memberBoot … true` (putgetc's `Main` allocates at `cmp := true`).
- **Item 13**: `etcd_cache_served`, watchkv's `wk_served` take `(hoff : V.R.E.γ.cm = false)` (item
  26's reading of the drafted `¬ kbCmpM V.R.E.γ.kb`); linkv3p's `memberWatch`/`memberAt` append
  `E.γ.cm = false`. Each `Main` reads `E₀.cmp = false` off its boot bundle and `envAgree_off` gives
  the rest.
- **Item 19** (`schedule`): `SchedNames.pay`; `schedPayIs`, `schedPay`, `schedPay_of/_true/_elim`,
  `schedDone`, `schedDone_excl`; `jobDoSpec`/`jobFnSpec`'s `□ (cd.PDone -∗ schedPay γ)`;
  `NewFIFOScheduler.spec`'s `Pay`; `Scheduler.Stop.spec` takes `schedPay γ` and returns `schedDone γ`
  (internal: `fifoCtxDesc γ F`'s `PDone`, the cancel function's, `donecCarry` with the run token,
  `job.Do.spec`'s premise). The server's `run` makes its scheduler with `Pay = True`.
- **Item 26**: `StoreNames.cm` (logical) and `physOk`'s tie `kbCmpM γ.kb ↔ γ.cm = true`;
  `wsFrozenM`/`crevRightM` read `γ.cm`.
- **Item 34**: `StoreNames.sx`/`PhysNames.sx`, `stopPay`, `stopPayAt`, `physOk`'s `stopPayAt γ.sx γ.sch
  o`, `stopPay_of_done`, `stopPayAt_done`: `NewStore`/`store.Restore` make the scheduler with the
  payload "the stop channel is closed", `store.Close`/`store.Restore` present it to `Stop`.
- **Item 35** (with S4): `EtcdServer.Compact.spec`'s `1 ≤ r` (its docstring names the margin: it also
  excludes negative revisions, which Go handles harmlessly), `compactPropOk` with `1 ≤ r`,
  `plainLogC_compaction_pos`; `compactableOk_server` discharges it from the permit. `recsPos` is
  `CmpRecs.lean`'s; its use in `keyImageM` waits with item 21.
- **S5**: the issue file's "How the proof handles it" updated; item 19's approved text is the field
  `pay`, as switched.
- **Item 28, with S1** (one spec per function): `UnsafeReadFinishedCompact.spec`/
  `UnsafeReadScheduledCompact.spec` over an optional record set, `metaReadSpecR rt rs` (`none`:
  `metaReadSpec rt false`, `checkPrevCompactionCompleted`'s reader; `some r`: the records exactly,
  `some CmpRecs.empty` being `metaReadSpec rt true`, `store.restore`'s reader under `kbNoCmp`); the
  post `∀ r, rs = some r → the record` beside today's two facts. One proof each (the flag cases by
  the flag's proof, kept in the proof file as `wp_proofNC`; the record case the Draft's `wp_proofR`).
- **Item 29, the pure vocabulary**: `CmpRecs` (`empty`, `finRev`, `schedRev`, `resumes`, `crev`,
  `at`), `recsOk`, `recsPos` and their lemmas, in `mvcc/CmpRecs.lean` (new, beside `metaReadSpecR`).

### Stopped (for the user)

(Item 17 and its dependents but item 31: switched with the lease, "Item 17 switched: the jobs'
share leased", the last section.)

- **Item 17, the compaction chain over the restorable right, is not provable as drafted.** Its
  `compactJobPreR` gives the job `storeStopR s γ o := inv (fieldShareAt s γ q8 o ∨ schedDone γ.sch)`,
  to read `s.b`, `s.kvindex`, `s.stopc` (`scheduleCompaction`: six loads, `compactBarrier`: one)
  "per read, the invariant opened around an atomic load". Perennial's loads are not atomic: `GoLoad`
  reduces to `Read` = `StartRead` then `FinishRead` (`Perennial/GooseLang/Lang.lean`,
  `Golang/Defn/PostLang.lean`'s `load_primitive`), and the only load spec
  (`IntoValTyped.wp_load`) needs the points-to across the whole call; an invariant can be opened
  only around one atomic step. Leasing the eighth for the job's run (swap the run token's ghost part
  `schedDone` into the invariant, take the eighth out, swap back at the end) is unsound locally: the
  closer's own eighth (`storeCloserR`) can be swapped in while the job runs and the run token taken,
  and then the job cannot return `schedRunning`. Repairs (internal to mvcc: `storeStopR`,
  `compactRightR`'s body; no client text changes): (a) carry the eighth along the tracked jobs'
  baton (`compactQueue`'s `Q`/`R`; under the approved design every barrier is tracked, so each job
  holds it for its run, and `Stop` returns the last job's `Post` with it); (b) a third state of the
  invariant, "leased", whose lease token the running job keeps. `notes/decisions.md`, "M2's storage
  side: the compaction chain over the restorable right is not provable as drafted".
  With it stay Drafts: item 4's step-2 text (`compactRightR` in `store.Compact.spec`), item 20
  (`wsCloserR_of_wsCloser`), item 23 (`store.Close.specM`, whose on mode is `compactRightR`), item
  24 (`mvcc_NewStore_backend_cmp`'s post `compactRightR s γ (-1)`; S5: with item 29's backend merge
  its pre's `fkV` is the merged ghost's `fkVM`), and item 31 (`lockNilSpec`, `kbHookNil`,
  `lockCtxM`/`lockBackM`: its only users are item 17's `updateCompactRev.specR`/
  `compactLockfree.specR` and item 15's `resumeHookM`; switching the clause alone would change the
  backend contract `batchTxSpecG` with no consumer).
- **Item 14** (`kbWTSupplyM_of_poolR`) stays a Draft: it is stated over D22's `srvWTPoolR`, item 21's.
- **Item 27** (the records threaded through `keyReadLocked`, `keyReadSnap(C)`, `keyCleanRead`,
  `isKeyBackendG`, `storeBackendTR`, `restoreViewR`) and **item 29's backend part** (the merged
  compaction-key ghost `fkVD`/`fkVM`/`fkOpenD`, `kbRecs`, `recBytes`) stay Drafts: their only users
  are the waiting restore chain (items 15, 18, 21, 30); `kbRecs` needs the merged ghost, which changes
  the backend's constructor (`fkCl` at the open's records) and every `fkV` site. Not a proof problem:
  switched with item 30.

### The Drafts now

`mvcc/M2StorageDraftRestore.lean` (the restorable right, `restoreRightM`/`storeCloserM`, the records
vocabulary's backend part, `keyImageM`/`restoreImageM`, `Restore.specM`, `store.restore.specR`,
`Close.specM`, `wsCloserR`), `mvcc/M2StorageDraftChain.lean` (item 17), `mvcc/M2StorageDraftIndex.lean`
(items 32, 33), `etcdserver/M2StorageDraft.lean` (`server_kv_watchable_ofD`, the glue for
`specCompact`), `etcdserver/M2StorageDraftRestore.lean` (D22's). Deleted: the step-1 Drafts (mvcc,
v3rpc, client, examples' three, cache), `M2StorageDraftSupply`, `schedule/M2StorageDraft`,
`etcdserver/M2StorageDraftScope`.

### Checked

- `etc/lean-check.py` on each changed file during the work; targeted `lake build`s.
- Full `lake build` (`--packages` at Perennial `ad74ee4`): passed, 11203 jobs, no error.
- `etc/tcb-report.py --check`: the trust base matches `etc/tcb-baseline.txt` (766 axioms, 18
  sorries: no new axiom, no new `sorry`); every `etc/tcb-collections/*.txt` `--check` matches.

## Item 17 switched: the jobs' share leased (2026-10-30)

The coordinating agent chose repair (b) of the stop above (an internal predicate design, no
client-facing text changed; `notes/decisions.md`, "M2's storage side: the jobs' share of the
fields, leased"). Done on `m2-storage`; no `axiom`, no `sorry`, no Perennial change, no generated
file edited.

### The lease as built (`InvCompact.lean`)

- `jobFieldsInv s γ o gl`: free (`fieldShareAt s γ q8 o ∗` the lease token `dghostVar gl 1 ()`),
  leased (`dghostVar γ.sch.run ½ ()`, half the run token), reclaimed (`schedDone γ.sch`).
- `storeStopR s γ o` (persistent, sealed): `(∃ gl, inv jobFieldsN (jobFieldsInv s γ o gl)) ∗
  isStopChan o.sstop` (the stop channel added: `scheduleCompaction`'s loop receives from it).
- `jobLease s γ o`: the lease token, half the run token, the worker's thread token.
- Laws: `storeStopR_alloc`, `storeStopR_stopChan`, `storeStopR_lease` (run token and `£ 1` in, the
  eighth and the lease out), `jobLease_return` (the eighth, the lease and `£ 1` in, the run token
  out), `storeStopR_reclaim` (with `schedDone`, after `Stop`), `fieldShare_reclaim`.
- `storeCloserR`, `compactRightR` (sealed; `compactRightR_iff`, `compactRightR_take` lending the
  closer's eighth and the queue, `compactRightR_crev` lending the authority's half),
  `compactRightR_of_closer`, `storeCloserM` (by `kbCmpM γ.kb`, as drafted) with `storeCloserM_off/on`
  and `storeCloserM_close` (what `Close` uses, either mode), `fieldShareAt_acc` (the four points-to
  and `physOk` of a share, and the share back).
- `compactJobPre` redefined in place to the drafted `compactJobPreR` (`∃ o, storeStopR s γ o` in
  place of `storeStop s γ ∗ schedLive γ.sch`); `storeStopped γ` names the stop by the payload's name
  `γ.sx` (no field `↦□` any more), `compactDone`'s body follows (text unchanged).

### Switched

- **Item 17**: `store.Compact.spec` (export `mvcc_store_Compact`) over `compactRightR s γ c` (with
  item 4's step-2 text, the drafted `store.Compact.specR` exactly); internal `updateCompactRev.spec`,
  `compactLockfree.spec` over `compactRightR` at the hook set (`hookIs ∗ csContract`, `lockCtxM`'s
  `some f` arm), with the `ErrCompacted` barrier tracked on the right's queue; `compact.spec`,
  `checkPrevCompactionCompleted.spec` read through a share at `o` (the right's closer's eighth,
  given back); `scheduleCompaction.spec`, `compactBarrier.spec` through the job's leased share
  (`compactBarrier` takes `□ (cd.PDone -∗ schedPay γ.sch)`: its re-scheduling branch is dead,
  `stopPayAt_done`). Each job closure (`compact`'s, the barrier's) leases at its start and returns
  at its end (`wp_fupd`, two later credits).
- **Item 20**: `wsCloserR`, `wsCloserR_iff`, `wsCloserR_of_wsCloser` (`WsCloserR.lean`, new).
- **Item 23**: `store.Close.spec` over `storeCloserM s γ c`; `watchableStore.Close.spec` "alike" over
  `wsCloserM s st γ.st c` (off `wsCloser`, on `wsCloserR`; drafted here, the approved list names it
  without a text); `NewServer`'s two error-path closes at `wsCloserM_off` (`¬ kbCmpM γw.st.kb`).
- **Item 24**: `mvcc_NewStore_backend_cmp`'s post `compactRightR s γ (-1)` (the drafted
  `mvcc_NewStore_backend_cmpR`, proved by `compactRightR_of_closer`).
- Deleted from `InvStore.lean`: step 1's `storeStop`, `storeStop_open`, `compactRight`,
  `compactRight_of_closer`. From the Drafts: everything above (`M2StorageDraftRestore.lean` keeps
  `restoreRightM`, `wsCloserR_split/join` over `wsCloserR_iff`, the restore chain;
  `M2StorageDraftChain.lean` keeps only item 31's part).

### Stopped (for the user)

- **Item 31** (`lockNilSpec` as `batchTxSpecG`'s clause, `kbHookNil`, `lockCtxM`/`lockBackM`, and the
  chain's internal specs generalized by the hook's state) stays a Draft: the `none` arm (the
  resumed compaction inside `Restore`, the new backend's hook unset) runs `SetScheduledCompact`,
  whose spec takes the hook's triple (`HF f`); proving the arm needs `SetScheduledCompact.spec`
  generalized by the hook's state too (one spec per function), which no approved text states. Its
  only consumer is the waiting restore chain (items 15, 18).

### Checked

- `etc/lean-check.py` on each changed file during the work.
- Full `lake build` (`--packages` at Perennial `ad74ee4`): passed, 11204 jobs, no error.
- `etc/tcb-report.py --check`: matches `etc/tcb-baseline.txt` (766 axioms, 18 sorries); all 43
  `etc/tcb-collections/*.txt` `--check` match.

**The user approved `watchableStore.Close.spec`'s text (2026-10-30)**, written at the switch (item 23's
"alike"): `∀ … (c : Int)`, pre `mvcc.wsCloserM s st γ.st c` in place of `mvcc.wsCloser s st γ.st`.

## The index at a full revision (branch m2-index)

The user's decision B1 after round 5 (2026-10-30): the index invariant's compaction level is a full
revision (main and sub), removing `KeyOnceAt` (item 33) and its apply-side obligation. Done on branch
`m2-index` (off `m2-storage` at `938b3fa371`), in the index's files only (`InvIndex*.lean`, new
`InvIndexCut.lean`/`InvIndexRestore.lean`, `M2StorageDraftIndex.lean`), the index's method proofs
and their pure users, plus a minimal edit of `mvcc/M2StorageDraftRestore.lean` (the `KeyOnceAt`
conjuncts and premise removed). `notes/decisions.md`, "M2's storage side: the index invariant at a
full revision".

### The new `IdxCRepN` (`mvcc/InvIndexCut.lean`)

- **The cut**: `kiCutAt gi j ki` drops the generations before `gi` and the first `j` revisions of
  generation `gi` (headers kept): the key index from its revision at position `(gi, j)` on, a full
  revision of the key. `kiCutO` is `none` when nothing is left.
- **The level**: `CutLe c ki gi j`, the position at or before the one compaction at `c` cuts at
  (`compactGenIdx`, `cmpRevIdx`). A compaction is the cut at its own position (`kiCompact_eq_cutAt`).
- **The invariant**: `IdxCRepN cmax evs idx := idx sorted ∧ ∀ k, ∃ c ∈ [-1, cmax], ∃ gi j, CutLe (W64 c)
  (kiOfKey evs k) gi j ∧ (idxGet idx k).map kiNorm = (kiCutO gi j (kiOfKey evs k)).map kiNorm`
  (`kiNorm`: the unread header of a tombstone-only generation that is not the last, round 4's).

### Proved (pure; no backend or bbolt fact needed)

- The cut's laws: compaction at `c' ≥ c` erases it (`kiCompact_cutAt`), a reader at or above `c`
  cannot tell (`kiGet_cutAt`), nor can `doCompact`'s and `keep`'s choices (`kiAvail_cutAt`,
  `kiKeep_cutAt`), the writer's event commutes with it (`kiCutO_step`, `CutLe.kiApply`), and the
  same up to `kiNorm` (`kiGet_kiNorm`, `kiAvail_kiNorm`, `kiKeep_kiNorm`, `kiNorm_kiPut`,
  `kiNorm_kiTombstone`, `kiNorm_kiCompact`, `stepO_norm`).
- S2's list for `IdxCRepN`: `IdxCRepN_of` (from `IdxCRep`), `nil`, `mono`, `step` (the writer's
  event), `kiAt`, `rangeAt`, `compactAt`, `gensOk`, `avail_some`/`avail_none`, `keep_some`/
  `keep_none`, `avail_inj`, and `get_facts`/`lastEmpty_none` (what `Put`/`Tombstone` read of a key's
  tree index: not empty, `modified`, the last generation's emptiness).
- **`idxRestore_cut`** (`mvcc/InvIndexRestore.lean`; replaces the Draft's `idxRestore_cutStmt`):
  `LogWf' L → LogB L → -1 ≤ c → c < L.length → entsCutAt L c ents → IdxCRepN c (evsOf L)
  (idxRestore ents)`, with no premise on how often a revision changes a key. `entsCutAt` and
  `entsCutAt_full` moved there from the Draft.
- The counterexamples gone (`M2StorageDraftIndex.lean`, now evidence only): the reviewer's round-5
  log (`[[], [], [put a], [put a, del a]]`, the batch ending after revision `2`) checked:
  `cxr_not_compacted` (no main-revision level gives the rebuilt key index) and `cxr_idxCRepN` (it is
  related at `IdxCRepN 3`, cut at `⟨3, 0⟩`); likewise `cx3_idxCRepN` for round 4's `cx3Log`, and
  `cx_idxCRepN` for the tombstone-only case.

### Item 32 switched (internal)

`idxLockInv`'s `HL` is `IdxCRepN cmax … ∧ -1 ≤ cmax`. Re-proved over it: `reader_answerC`,
`rangeAnswers_entriesC` (`InvIndex.lean`), `entries_not_emptyC` (`ReadLemmas.lean`), `keepFold_spec`,
`keepAt_keys` (`CompactMaps.lean`), `treeIndex.Put`/`Tombstone`/`Keep`/`Compact`'s proofs;
`idx_publish` keeps its premise `IdxCRep (-1)` (the private index, compaction-free) and converts it
(`IdxCRepN_of`). No exported statement changed; `treeIndex__Compact`'s spec changed only in its
docstring. `IdxCRep` and its lemmas stay (the private index's, `RestoreChunks`, `Results.lean`'s
prints).

### Not done (the restore chain's)

- `store.restore.specR`'s proof still needs `idx_publish` at the restored level (`crevLb γ.idx
  r.crev` and `IdxCRepN r.crev` in place of `-1`): a variant of `idx_publish`, with
  `idxRestore_cut` as its pure input, when the chain is switched.
- Q8/B2's receipt bound, item 37's view widening, item 30's backend clause: unchanged.

### Checked

- `etc/lean-check.py -a` on every changed or new file; targeted `lake build` of the index modules and
  both restore Drafts (3657 jobs, no error).
- Full `lake build` (`--packages` at Perennial `ad74ee4`): passed, 11205 jobs, no error.
- `etc/tcb-report.py --check`: the trust base matches `etc/tcb-baseline.txt` (766 axioms, 18
  sorries): no new axiom, no new `sorry`. No Perennial change, no generated file edited.
- `notes/STATUS.md` not edited on this branch (to keep the merge with `m2-storage` trivial): at the
  merge, item 32 moves to switched and item 33 to dropped.

## The restore chain, mvcc part (2026-10-30)

On `m2-storage` after the merge of `m2-index` (`3fb21d0515`), in parallel with `m2-backend` (the
backend package, `BackendBridge.lean`, `StoreBackend.lean`, the records clause, the view widening),
whose files were not touched. No `axiom`, no `sorry`, no Perennial change, no generated file edited
(`Link.lean`'s `store.restore` line follows `etc/link-lean-first-mvcc.txt`; `etc/gen-link.py --mvcc`
gives the same file but for the two `raftAsm` variable lines `b1542227ac` added by hand).
`notes/decisions.md`: "`store.restore` over a compacted image, switched", "`SetScheduledCompact` by
the hook's state", "B2, the receipt bound as a premise of `NewServer.specCompact`".

### Item 18 proved and switched (internal)

- **`store.restore.spec` is the drafted `specR`** (`Spec/.../mvcc/store__restore.lean`), proved
  (`store__restore.lean`, 840 lines: the found record's lock round with `compactMainRev` written whole,
  the scheduled record, the chunk loop over the image's entries, `currentRev` raised to the two records,
  the index published at the restored level, the resumed compaction through `resumeK`, the logging on
  either error). Changes from the draft (decisions entry): the records' resource is a parameter `NC`
  (`kbRecs` stays the backend's); the lock's ghost part at the level is `idxLockGAt γ n r.crev` in place
  of `idxLockG ∗ crevLb`; `∀ x, r.fin = some x → dqc • dql = DFrac.own 1`. New callees: `zap.String`,
  `zap.Error`, `zap.Logger.Warn`.
- **Pure** (`RestoreCut.lean`): `bucketOfEnts` (moved) and its lookup over a sublist of the log's
  entries, the range from a revision (`bucketRange_fromE`), the next chunk (`entsFromE_next`),
  `restoreOk_sublist`, and **`restoreCur_cut`**: the rebuild's answer raised to the finished, then
  the scheduled record is the log's last revision (the last revision's entries survive, or they were
  deleted and the restored revision, a record, is at it). `CmpRecs.crev_ge`.
- **The index** (`IdxPriv.lean`): `idxLockGAt`, `idxLockG_at`, `idxCmpOwn_nil`, **`idx_publishAt`**
  (over `idxRestore_cut`).
- **Item 27's vocabulary** (`RestoreRecs.lean`, moved from the Draft): beside today's, not in its place
  (the bridge's vocabulary is the backend side's); `restoreViewR` over `NC`; `revFinW`,
  `restoreDone` (over `NC`), `resumeK`.
- **Today's users unchanged**: `store.restore.specNC` (`RestoreNC.lean`) is the old text,
  `specNC_of_spec` derives it; `NewStore` and `store.Restore` convert in one line.
- **Hypotheses from the backend side: none** for `store.restore` itself (it is generic over the
  backend contract `isKeyBackendGR … NC r` and the clean read `keyCleanReadR`). Its caller in
  compaction mode (`store.Restore.specM`, item 15) needs, as before: `keyCleanRead_of_backendC`
  (the records' clean read, `mvcc.keyCleanRead_of_backendC_stmt`, over the backend's records clause,
  item 29/30) and `kbView_widen` (item 37).

### Item 31: `SetScheduledCompact` switched; the store's chain waits on the bridge

- **`SetScheduledCompact.spec` by the hook's state** (`lockArmS`, `LockArm.lean`; `lockNilSpec` moved
  there), proved for both arms; `updateCompactRev` passes `some f`.
- **Not switched**: `lockCtxM`/`lockBackM`, `updateCompactRev.specR`/`compactLockfree.specR`,
  `resumeHookM` (Chain and Restore Drafts). The `none` arm needs `lockNilSpec` for the store's batch
  transaction, which only the backend contract can give: `batchTxSpecG`'s new clause `lockNilSpec bt RT
  WT W P (kbHookNil kb) Locked`, proved by the bridge (`isKeyBackendG_of_backendC`, `BackendBridge.lean`,
  `m2-backend`'s) with `bt_lockInNil` (proved, Draft). After it lands: add the clause, switch the chain
  (its proofs are today's at `some f`, plus the `none` arm through `SetScheduledCompact`'s).

### B2 drafted (`etcdserver/M2StorageDraftB2.lean`; for the user)

- **The premise** (of `NewServer.specCompact` only, beside `receiptBound GF ≤ 2 ^ 48`):

      srvChBound ρ.rd.raft ρ.rd.kv srvAuthSt0
      -- srvChBound γ γk st₀ := □ ∀ L, srvReqLogLb γ L -∗ ⌜logCh (kvModelOn γk st₀ L) < receiptBound GF⌝

  the KV model of every prefix of the cluster's log of requested entries has fewer changes than the
  receipts' bound. Off mode needs none (whole-bucket images; the rebuild refills the writer).
- **Glue (proved)**: `srvChBound_committed` (a committed log's model, through `srvReqLogLb_of_rlogLb`
  and `kvRaftOfOn_eqv`), `restoreBoundM_of_chBound` (what `restoreBoundM` gave `Restore.specM`, for the
  image of the snapshot's committed entries), `srvChBound_small` (`< receiptBound` and, with
  `receiptBound GF ≤ 2 ^ 48`, `< 2 ^ 48`: `soleWriter_small'`'s conclusion), and the mvcc side's
  `mvcc.idxWriterNR_seal` (a seal with the caller's bound in place of the writer's receipts: the sealed
  log is today's `idxSealed`, so `idxSealed_small` and `soleWriter_small'` are unchanged).
- **Open (for the user)**: the premise is an Iris fact about the cluster's future history; the closed
  theorems' hypotheses are pure, and `putgetc`'s `Main` (`specCompact`, one member) cannot establish
  it. Options: (i) a pure form, a bound on the cluster's committed history from a workload descriptor
  (each change of the KV log comes from a put of a request, `≤ MaxTxnOps` per entry, a delete
  deleting earlier puts' keys, so `logCh ≤ 2 · MaxTxnOps · |committed entries|`, with a bound on the
  committed entries as the configuration premise); (ii) a gate excluding it where no image is
  installed (a one-member cluster that never adds members); (iii) as drafted, the examples' top-level
  theorems taking it as a premise in Iris form (not possible with today's adequacy).
- `restoreBoundM` (item 36) stays in `Restore.specM`'s Draft until the user picks; with B2 its source
  is `restoreBoundM_of_chBound`.

### Not done

- Item 15/16 (`store.Restore.specM`, D22's): waits on 30 (the backend's records clause), 37 (the view
  widening), the chain's switch (item 31's rest), B2's source; the restored writer's handle in
  compaction mode (`idxWriterNR` with `idxWriterNR_seal`) is its part.

### Checked

- `etc/lean-check.py -a` on every changed or new file.
- Targeted `lake build` of mvcc's `Results`, the mvcc and etcdserver Drafts (4351 jobs, no error).
- Full `lake build` (`--packages` at Perennial `ad74ee4`): passed, 11211 jobs, no error.
- `etc/tcb-report.py --check`: matches `etc/tcb-baseline.txt` (766 axioms, 18 sorries); all 43
  `etc/tcb-collections/*.txt` `--check` match.
- `notes/STATUS.md` not edited on this branch (to keep the merge with `m2-backend` trivial).

## The restore chain, backend part (branch m2-backend)

Branch `m2-backend` (off `m2-storage` at `3fb21d0515`), in the backend package, `mvcc/BackendBridge.lean`
and new files, plus a minimal edit of `mvcc/Image.lean` (four `(fkCl_parts …).1` became `fkCl_parts …`,
the law now an entailment). Items 27/29 (backend part), 30 and 37 of the approval list. No `axiom`, no
`sorry`, no Perennial change, no generated file edited; no snapshot-track statement touched. No new
bbolt fact was needed. `notes/decisions.md`, "M2's restore chain, the backend part".

### Item 29's backend part: the merged ghost and the open's records clause (switched)

- **The merged ghost** (`InvBackend.lean`): `γ.fkv` holds `FkG = Bool × Nat × FkVals` (the bit, the
  flag's value at the open, the compaction keys' values at the open; `FkVals` = (finished,
  scheduled), `Model2.lean`). `fkVR γ g` is the ghost; `fkV γ w := ∃ n v, fkVR γ (w, n, v)` (today's
  bit, text and users unchanged); `fkOpen γ n v := ∃ w, fkVR γ (w, n, v)` (the Draft's `fkOpenD`;
  the Draft's `fkVD γ w n v` is `fkVR γ (w, n, v)` by definition).
- **The records clause** (`fkOkG`, `Model2.lean`): the batch lock's `fkHalf` and the readers' `fkRd`
  carry `fkOkG P f g st := fkOk P f g.1 st ∧ g.2.1 ≤ f ∧ (f = g.2.1 → fkValSt P g.2.2 st)` (readers:
  `f ≤ g.2.1 → fkValRv …`, the lower bound being at least the open's value when taken):
  while the flag is at its value at the open, the committed data and the writer's contents hold the
  open's values at the two keys and neither buffer has an entry there. Kept by every operation
  (`fkOkG_put`/`del`/`create`/`delBucket`/`wb`/`commit`/`setHw`, `FkLemmas.lean`); a put of a
  compaction key raises the flag by one (`fkHalf_raise`: `f + 1`, until now `max f 1`), past the
  open's value. Set at the open from bbolt's data `D` as `fkCl` was (`NewAlloc.lean`: the ghost
  allocated at `(fkWInit P D, fkInit D, fkVals D)`, `fkOkG_init`).
- **The read law** `fkRd_open` (`ReadLemmas.lean`): `fkOwn γ n ∗ fkOpen γ n v ∗ fkRd γ P rv ⊢ fkOwn γ n ∗
  ⌜fkValRv P v rv⌝`; `vOf_fkVal`: such a state reads `fkAt v k` at a compaction key.
- **The constructor's post**: `fkCl γ P D := fkOwn γ (fkInit D) ∗ fkVR γ (fkWInit P D, fkInit D,
  fkVals D)` (its body; `newPost`/`newPostK`'s text unchanged, so `OpenBackend`'s and
  `OpenSnapshotBackend`'s axiom texts are unchanged). Laws: `fkCl_parts` (now `⊢`: the flag and the
  bit, every existing use), `fkCl_open` (with `fkOpen γ (fkInit D) (fkVals D)`, what the walk takes
  for `kbRecs`), `fkOpen_fkV`. **For the user**: the axioms' posts now carry the open record through
  `fkCl`'s body; it is `backend.New`'s proved post (`New`'s proof computes it from `D`, as it does
  `fkInit`/`fkWInit`), the justification `notes/axiom-review/openbackend-post.md` gave for `fkCl`.
- **A gap the design missed, closed by two premises** (backend specs, internal): the clause is not
  kept by a delete of a compaction key or of the `meta` bucket, which the backend's specs allowed.
  `batchTxBuffered.UnsafeDelete.spec` takes `¬ fkKey bi.name kb`, `UnsafeDeleteBucket.spec` takes
  `∀ k, ¬ fkKey bi.name k` (only mvcc writes the keys and never deletes one; nothing deletes `meta`).
  Callers: the bridge's two deletes (`Lease`, `Key`: `lease_not_fk`, `key_not_fk`); nothing calls
  `UnsafeDeleteBucket`.

Item 27 (the records threaded through `keyReadLocked`, …, mvcc's vocabulary) stays the Draft's: its
definitions are mvcc's (`InvStore.lean`), the parallel branch's area, and its only users are the
waiting chain. The Draft's `kbRecs` reads, at the switch, `∃ n, fkOwn γB n ∗ fkOpen γB n (recsVals r)`
(`recsVals r` = the Draft's `(recBytes r.fin, recBytes r.sched)`).

### Item 30: the records' half proved; the drafted statement is not provable (two defects)

- **Proved** (`mvcc/BackendRecs.lean`, new): `rt_metaRecs`: the held shared read transaction's reads
  of `Meta`'s compaction keys, under `fkOwn γ n ∗ fkOpen γ n (recsVals r)` and the reader's `fkRd`,
  are `metaReadSpecR … (some r)` (the records exactly; at no record, today's `metaReadSpec … true`).
  This is `keyReadLockedR`'s meta clause from `kbRecs`'s resources: the part of the clean read the
  records add.
- **Defect D1 (exactness)**: `keyCleanReadR` promises reads *exactly* of the view's bucket `m`
  (`keyReadSnapCR` → `keyReadLockedR … m`). Over a registered backend (`storeDlReg`, no `dlNoDel`) a
  reader's state is only thin of the clients' view (`rtHeld_clean` gives `thinV`): a deleting session
  (`Unlock`'s first branch) may delete any key the registration makes deletable, without the clients'
  view (or its clean flag) changing. The statement is persistent and its premises (`isBackend`,
  `keySized`, `storeDlReg`) exclude no such session: the image can hold entries deletable at the old
  store's compaction level (`entsCutAt` removes *a* prefix, possibly none), the registration's
  `delKeyI γ.idx` makes them deletable, and after one is deleted the clean read's range at `m` claims it.
  In Go nothing deletes from the new backend before `restore()` reads; the proof world needs a
  resource saying so. **Repair (recommended, (a))**: `Restore` takes the new backend's registration
  *unfixed* (`dlInit`, as `NewStore` does) and fixes it (`storeDlReg`) after `restore()`'s reads; the
  clean read's exactness is then `dlInit_noDel` (existing) in place of `dlNoDel_noDel`
  (`bridge_rt_clean`'s proof otherwise unchanged), the clean read lending `dlInit` in its pre, and the
  contract `storeBackendTR` given as a wand from `storeDlReg`. (b) An exclusive "no deletion yet"
  token from the constructor: changes `newPostK`, an axiom text; not recommended.
- **Defect D2 (records' sign)**: `metaReadSpecR … (some r)` states `0 ≤ sint.Z x` of each record;
  `kbRecs` gives only the open's values. The statement needs the records' sign as a premise
  (`rt_metaRecs`'s `hpos`; `Restore` has it from `restoreImageM`'s `recsOk`), or `fkV γB true` with
  `P.FV`'s `metaRevVal` and `revBytes_inj`.
- With D1's repair (a) and D2's premise the remaining proof is `bridge_rt_clean`'s with `rt_metaRecs`
  for the meta clause; not written here (the repair changes the chain's statements: the restore chain's
  call, not the backend's).

### Item 37: drafted; round 4's shape refutable; a lock-holding form drafted

`backend/M2BackendDraft.lean` (new Draft, imported by nothing):
- `viewWidenGhost_stmt` (round 4's "law at the open": `bView γ 1 vd ∗ thinV γ vd vd' ⊢ |={⊤}=> bView γ 1
  vd'`) is **refutable**: the view's other half is two quarters in the two locks' resources
  (`readTx.mu`'s `viewQ`, the batch lock's `batchViewQ`); after such an update the next put session's
  `Unlock`, which combines the three shares, derives `vd = vd'`. Only an operation holding both locks
  can widen.
- `batchTxBuffered.Unlock.specW`: `Unlock`'s put branch widened (the session gives `bView γ 1 vd` and
  `thinV γ vd vd'`, gets `bView γ 1 (relog P vd' st)`); `Unlock.spec_of_specW` (proved: `vd' = vd`).
  Not proved (today's `Unlock` proof with `thinV_trans` at the readers' and cached states).
- Neither serves `Restore` directly: `restore()` runs a put session only when it resumes a compaction.
  Options for the chain (mvcc's call): carry the pending widening in the writer until its first
  `Unlock` (with `specW`), or generalize mvcc's writer relation to "the backend's logical view is thin
  of the log's bucket" (no backend change; the backend's physical view already is thin of its logical
  one; that the store's put sessions keep it through `relog` is not checked).

### No new bbolt fact

The open record is computed by `New`'s proof from bbolt's data `D` (the same `D` `fkInit`/`fkWInit`
read); its preservation is the backend's own model. Nothing was asked of bbolt.

### Checked

- `etc/lean-check.py -a` on the new files; targeted `lake build`s of the backend (`Link`,
  `ClientLaws`) and of `mvcc/{Image,BackendBridge,StoreBackend}`.
- The Draft's `backend.fkOpenD γ n (recBytes r.fin, recBytes r.sched)` is `backend.fkOpen γ n
  (recsVals r)` by `rfl` (checked in a scratch module, not committed).
- Full `lake build` (`--packages` at Perennial `ad74ee4`): passed, 11208 jobs, no error.
- `etc/tcb-report.py --check`: matches `etc/tcb-baseline.txt` (766 axioms, 18 sorries).
- `notes/STATUS.md` not edited (updated at the merge).

**The user's answer on B2's form (2026-10-30): a pure bound on entries.** The premise is pure, on the
configuration or the run: the cluster commits at most N entries, with `2·MaxTxnOps·N` below the receipt
bound (`logCh ≤ 2·MaxTxnOps·|entries|`), so a closed theorem can take it like `receiptBound ≤ 2^48`;
the glue maps it to the drafted Iris form (`srvChBound`).

**Decided by the agent (coordinator), item 37:** the store writer's relation becomes "the backend's
view is a subset of the log's bucket, the missing keys deletable" (mvcc-internal, no backend change),
not a pending widening carried to the writer's first `Unlock` (the round-4 ghost form is refutable,
`backend/M2BackendDraft.lean`).
