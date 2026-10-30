# Plan: M2, the storage side (spec-first; branch `m2-storage`)

Status (2026-10-30): **Draft** written and checked (`fe466ad8d5`; full `lake build` passed, 10957 jobs, no error); internal repairs made; for the
user: the drafted statements below and the questions at the end. Q1 answered **(a)** and drafted
("Q1 (a), drafted", below; `mvcc/M2StorageDraftSupply.lean`); Q2 open. M2's plan is `notes/m2-plan.md` on
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
