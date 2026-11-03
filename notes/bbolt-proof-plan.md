# bbolt's proof: the plan of record

Started 2026-11-03 by U0a, from the reviewed invariant design (round 4, `design.md` of the
invariants stage, with its reviews `review-1..3.md`; kept outside the repository). This file
replaces it as the plan: its module plan, work units, schedule and risks are copied below (§4.1 to
§4.3, unchanged but for the U0a section), and every change U0a made to the design's text is logged
in "U0a: deviations". A unit that needs a frozen statement changed goes back through U0's owner and
records the change here.

## Status

- **U0a done** (2026-11-03): the pure models (`Proof/go_etcd_io/bbolt/Model/`) and the resource
  predicates (`Proof/go_etcd_io/bbolt/Inv/`) exist as definitions; every shared lemma is a
  `sorry`'d statement (inventory below); `Spec/go_etcd_io/bbolt/Api.lean`'s nine predicates are
  sealed (`@[no_expose] def`s over a non-public import of `Inv/FileHolds.lean`), each law proved by
  `exact` from its `…Def` statement in `Inv/`.
- **Next: U0b** (the internal function specs of §4.2's table, over these names).

## The modules (as built by U0a)

`Proof/go_etcd_io/bbolt/`, every module `@[expose] public section`, in namespace
`Perennial.EtcdGrove.bbolt`. None needs a package's `Assumptions` (the sealed predicates are in
`Api.lean`'s vocabulary section, which has none).

| module | what |
|---|---|
| `Model/Page` | byte encodings of `common.Page`/elements/`InBucket`; `pageHdr`, `pageId`…, `leafKey`…, `InodeM`, `pageBody`, `pageInodes` |
| `Model/Meta` | `Meta`'s encoding, `fnv64a`, `metaValid`, `metaPick`, `Pages`, `CommitSt`, `metaOk`, `CommitSt.publish` |
| `Model/Tree` | `leafWF`, `branchWF`, `treeWF`, `treeHas`, `ownHas`, `treePages`, `treeSlots`, `pagesStrict`, `pageHts`, `treeKeys`, `keyIn`, `entryBnd`, `treeStrict`, `rootShape`, `treeOK` |
| `Model/TreeData` | `treeLeaves`, `treeEntries`, `bktEntries`, `bktOfPage`, `treeData` |
| `Model/FL` | `Pending`, `FLPg` and its operations (`alloc`, `freePages`, `release`, `releaseRange`, `releasePending`, `rollback`, `reload`, `noSyncReload`, `ofInit`) |
| `Model/Mvcc` | `View`, `View.data`, `viewWF`, `RdInfo`, `pendSlots`, `mvccView`, `flBelow`, `pendingOnlyFromWriter`, `pagesAgree`, `flIds`, `flCurOK` |
| `Model/Store` | `MapSt`, `StoreSt`, `WSt`, `storeSlots`, `rq`, `wq`, `lent`, `storeOK`, the transitions, `storeOK_*` |
| `Model/Wtx` | `Src`, `WEntry`, `NRec`, `PageSt`, `BRec`, `WObj`, `WTx`, `WX` (all countable), `txClean`, `bktKeys`, `bktNested`, `txPg`, `wOK` |
| `Model/LTree` | `LTree`, `ltree`, `lleaves`, `lbktEnts`, `rootEnts`, `bktData`, `wtxData`, `wsPut`, `wsDel`, `leafFor` |
| `Model/Cursor` | `sPath`, `pathBnd`, `stackPos`, `stackAt`, `rStackAt`, `wStackAt`, `sRoutes`, `sFirst`, `sLast`, `sSucc`, `sPred`, `wCtx` |
| `Inv/Names` | `BNs`, `bnsOf`, `mkGs`, `pagesN`, `txsN`, `poolN`, `TxNames`, `PairSrc`, `TxReg` |
| `Inv/State` | `boltStateDef` and its laws, `st_update` |
| `Inv/Freelist` | `flRoOwn`, `flPgOwn` (the freelist object split by field), `hashOK` |
| `Inv/Locks` | `mapFields`, `metaCellsQ`, `metaOsBytes`, `fileOwn`, `metaR`, `flRoOpt`, `Pm`, `PmNoTok`, `Ps`, `rdPair`, `WDb`, `wdbOK`, `wdbCoreG`, `wdbOwn`, `wdbLive`, `wdbOpen`, `closedR`, `rwR` |
| `Inv/Store` | `slotsOf`, `viewCells`, `slotsOwn`, `storeCells`, `metaLend`, `pagesInv`, `store_*`, `meta_*` |
| `Inv/WtxHeap` | `txRoot`, `srcOwn`, `objOwn`, `txFields`, `rootFill`, `fills`, `wtxHeap`, `WX.rebase`, `derefOK` |
| `Inv/Shape` | `xHas`, `xPages`, `pgToks`, `nodeToks`, `bktToks`, `txShape` |
| `Inv/Txs` | `TxViewC`, `TxX`, `RHandle`, `reg`, `txExcl`, `txEntry`, `txsInv`, `txs_*` |
| `Inv/Bolt` | `dblAt`, `t0At`, `dbLogger`, `pageBuf`, `dbFixed`, `isBoltCoreP`, `isBoltCore`, `isBoltP`, `isBoltDef` |
| `Inv/Tx` | `viewOf`, `nodeLoc`, `handleFrag`, `rtxFrac`, `gensOK`, `wtxFrac`, `rdTx`, `boltTxDef`, `txDBDef`, `txDoneDef`, `boltBktDef`, `txBytesDef`, `boltCurDef` and their laws, `boltTx_rdTx` |
| `Inv/FileHolds` | `filePage`, `filePages`, `fileImage`, `flFileOK`, `fileOK`, `fileHoldsDef` |

## U0a: deviations from the brief (§4.4), and why

Each keeps the design's meaning; each is the smallest change that elaborated.

1. **The `Inv/` modules do not import `Api.lean`** (it imports them to seal its predicates; the
   other way is a cycle). They take a name's two parts, `B : BNs` (`bnsOf γ.gs`) and the namespace
   `N` (`γ.ns`), in place of `γ : BoltName`; `bns γ`/`mkBoltName` became `bnsOf gs`/`mkGs B` (a
   `BoltName` is `⟨mkGs B, N⟩`), and the namespaces take `N`.
2. **The sealed predicates' ambient instance arguments grow.** The `opaque`s took only
   `[GooseExts] [GooseSemantics] [GooseInterp] {GF} [HasExt osFsExt]`; their bodies need the heap,
   so `isBolt` & co. now also take `[GoGlobalContext] {hlc} [HeapGS hlc GF] [go.Semantics]`
   (`boltState` only `{hlc} [HeapGS hlc GF]`), and so do the laws stated over them. The explicit
   arguments and every statement's text are unchanged, and `etc/gen-interface.py`, which leaves
   ambient section variables out, shows no change. Every client has these instances in scope.
3. **Nothing takes a package's `Assumptions`** (`Api.lean`'s vocabulary section has none):
   `os.ownFile` (which `include`s `os.Assumptions`) is restated by its fields (`fileOwn`,
   `fileOwn_eq : fileOwn = os.ownFile` by `rfl`); the freelist is owned through field points-tos.
4. **`TxView` is not countable** (`gen` is a function), so `boltTx`'s agreed state holds a
   `TxViewC` (its fields, the generations as a finite map) with `T = TxView.ofC c`; a `T` whose
   generations are not finitely supported has no `boltTx`, which no spec produces.
5. **`boltTx`'s agreed state is split half/half** between the fractions (`q/2`) and the exclusive
   part (`txExcl`), so that the holder of the whole and of the exclusive part can update it; the
   private state is `TxX` (a reader's view, meta copy and registry key, or a writer's `WX`).
6. **`TxNames` gains `done`, `nl`, `pg`, `vw`**: the close flag the design's `txsInv` uses, the
   node registry (N3), the page tokens' name (`txShape`), and the views by base (`viewOf`, the
   persistent `ghostVar □` of the design, keyed by base since the writer's view is re-based by a
   remap).
7. **The store parks the writer's view across a remap** (`StoreSt.wlent`): `wreturn` sets
   `wlent := false` instead of `wv := none`, and `wborrow b` re-bases the parked view. Without it
   `store_wborrow` needed facts about the view that the writer cannot know (the store forgot it).
   The writer's part of the store's state is one ghost variable `B.wv : WSt` (view, `wtx`, `pub`,
   `wlent`), so that the writer knows `wtx`/`pub` across the window.
8. **`wdbCoreG`**: the writer side, parameterized by `db.rwtx`, the store's writer state and the
   mapping fields' share (½ idle, ¼ live: a live writer's fractions hold the other ¼, since
   `Tx.page` reads `db.data` at any fraction). `wdbLive` is the live writer's side (in `txExcl`);
   the writer's quarter of `st` is in `wdbOwn`/`wdbOpen` and, live, in `wtxFrac`.
9. **`rwR`, `wdbOwn` take `sp` and `t0`** (the spare pair's `statlock` and the receipts' base);
   `isBolt` pins `db` and `t0` by discarded ghost-map fragments (`dblAt`, `t0At`), not `ghostVar □`
   (Perennial's `ghostVar` has no discarded fraction).
10. **`Pages`, `CommitSt` are in `Model/Meta`**, since `CommitSt.metaOk` is (the brief had them in
    `Model/Tree`, after `Model/Meta`).
11. **The checksum is the uninterpreted `fnv64a : List w8 → w64`** (an `opaque`, not an axiom), not
    a parameter of `metaValid`: the parameter would thread through every predicate. §5 item 2's
    `hash/fnv` specs say `Sum64` computes it.
12. **`View` has the root page** (`View.data`, a reader's snapshot, needs it), and `viewWF` (a view
    is a `treeOK` committed state's) is in `Model/Mvcc`.
13. **`FLPg.free` is `FLPg.freePages`** (`free` is the field).
14. **`Inv/Freelist.lean` is new** (`flRoOwn`, `flPgOwn`, used by `metaR` and `rwR`; the brief
    leaves them to U2's split, but `Inv/Locks` needs them defined). U2 restates the old contract
    over them.
15. **`dbFixed` leaves out `freelistLoad`'s `sync.Once`**: Perennial's `isOnce` is stated for
    `HasLC.hasLC` only, and the sealed predicates are over any `hlc`. U11 decides how
    `loadFreelist`'s `Once.Do` is covered (an `hlc`-generic `Once` spec is a Perennial proposal, or
    `isBolt` records the `Once` as done by its field values).
16. **The lemma statements' shapes** (U0a chose them where the design gives only names):
    the `store_*`/`meta_*` updates take the caller's shares of the agreed ghost state and slots
    moving between the store and `W` with their cells and bytes (`slotsOwn`); the `wtxData_*`
    lemmas are over `WX.withWs` (a node's entries replaced) and, for `CreateBucket`/`DeleteBucket`
    and `rebalance`, over the buckets' logical entries; the cursor lemmas are over stack shapes
    (`sPath`) with the moves as index relations (`sRoutes`, `sFirst`, `sLast`, `sSucc`, `sPred`).
    A unit that finds one unprovable or unusable changes it through U0's owner, recording it here.
17. **Known gaps to close in the owning units** (the definitions are U0a's first cut):
    a bucket that is neither the root nor a handle has its `FillPercent` unowned; `wBytes` does
    not cover a partial last page of the file; reader handles' memory (`readerHandleMem`) is not
    in `boltBkt` (only the registry fragment); `txRoot tx` must be written `txRoot (GF := GF) tx`
    (its `go.Semantics` instance is stuck otherwise; the modules write `tx.[Tx, go!"root"]`).

## The `sorry` inventory (what later units prove)

102 `sorry`'d statements, all in `Model/` and `Inv/`; `Api.lean`'s laws have none of their own.

| module | statements | unit |
|---|---|---|
| `Model/Page` | `pageHdr_bytes`, `pageInodes_writeInodes` | U1 |
| `Model/Meta` | `metaPick_current`, `metaOk_parity_write` | U1, U10 |
| `Model/TreeData` | `bktEnts_treeEntries` | U6 |
| `Model/Mvcc` | `mvccView_release`, `_releaseRange`, `_free`, `_alloc` | U3 |
| `Model/Store` | `lent_lt_half`, `storeOK_register`, `_deregister`, `_wbegin`, `_wreturn`, `_wborrow`, `_wclose`, `_free`, `_alloc`, `_release`, `_publish`, `_rollback`, `_reload`, `_gather`, `_carve`, `_setFl` | U3 |
| `Model/LTree` | `wtxData_put`, `_del`, `_create`, `_drop` (U7); `wtxData_rebalance` (U8); `treeData_spill` (U9); `ltree_leaf_of_T` (U6) | |
| `Model/Cursor` | `rStackAt_seek`, `_first`, `_last`, `_next`, `_prev`; `wStackAt_seek`, `_first`, `_last`, `_next`, `_stable` | U6 |
| `Inv/State` | `boltStateDef_fractional`, `_agree`, `_valid`, `_agree_lib`, `st_update`, `boltState_read_au'`, `boltState_commit_au'` | U5, U12 |
| `Inv/Locks` | `Pm_fractional`, `Ps_fractional`, `wdbOK_partition` | U3, U5 |
| `Inv/Store` | `store_register`, `_deregister`, `_wbegin`, `_wreturn`, `_wborrow`, `_wclose`, `_free`, `_alloc`, `_release`, `_publish`, `_rollback`, `_reload`, `_gather`, `_carve`; `meta_borrow`, `_return`, `_take`, `_put` | U3 |
| `Inv/WtxHeap` | `wtxHeap_fractional`, `fills_fractional`, `wtxHeap_kill`, `wtxHeap_rebase` | U5, U8, U9, U4 |
| `Inv/Txs` | `txs_register`, `txExcl_take`, `txExcl_put`, `txs_close`, `txs_stats_atomic` | U5 |
| `Inv/Bolt` | `isBoltCoreP_persistent`, `isBoltCore_persistent`, `isBoltDef_persistent`, `isBolt_core`, `isBolt_db_agree`, `isBoltP_agree` | U5 |
| `Inv/Tx` | `boltTxDef_later`, `_fractional`, `_agree`, `_valid`, `_nonnull`, `_base`, `_fill`; `txDBDef_persistent`, `txDoneDef_persistent`, `boltBktDef_persistent`, `txBytesDef_persistent`, `boltCurDef_timeless`, `txBytesDef_acc`, `boltTx_rdTx` | U5, U6, U12 |
| `Inv/FileHolds` | `fileHoldsDef_timeless`, `fileHoldsDef_new`, `fileHolds_decode` | U11 |

---------------------------------------------------------------------------------------------

The rest is the design's §4.1 to §4.3 (round 4), the plan U0a started from. Where it names a
module or definition differently from "The modules" above, the table above is current.

## Module plan, work units, risks (design §4)

### 4.1 Layout (`Proof/go_etcd_io/bbolt/`, all modules, `@[expose] public section`)

```
Spec/go_etcd_io/bbolt/Api.lean               -- the frozen vocabulary; predicates @[no_expose],
                                             -- sealed over the Inv modules; the laws' proofs
Spec/go_etcd_io/bbolt/<T>__<M>.lean          -- frozen public triples + internal ones (spec-first)
Proof/go_etcd_io/bbolt/
  Model/Page.lean       Model/Meta.lean      Model/Inode.lean       -- byte layout (UM-based)
  Model/Tree.lean       Model/TreeOK.lean    Model/TreeData.lean    -- treeOK, treeData
  Model/FL.lean         Model/Mvcc.lean      Model/Store.lean       -- FLPg, mvccView…, StoreSt
  Model/Wtx.lean        Model/WtxData.lean   Model/LTree.lean       -- WX, wtxData, ltree
  Model/Cursor.lean                                                 -- stackAt, positions
  Inv/Names.lean        Inv/State.lean                              -- BNs, boltState + laws
  Inv/Locks.lean        (metaR, Pm, Ps, rwR, wdbOwn)
  Inv/Store.lean        Inv/StoreReg.lean    Inv/StoreFree.lean     -- pagesInv + lemmas (§3.6)
  Inv/StoreRelease.lean Inv/StorePublish.lean Inv/StoreRemap.lean   Inv/MetaLend.lean
  Inv/Txs.lean          Inv/Bolt.lean        Inv/Tx.lean            -- txsInv, isBolt, boltTx, …
  Inv/WtxHeap.lean      Inv/Shape.lean                              -- ported ownWriteTxG/txShape
  Inv/FileHolds.lean                                                -- fileHolds, fileHolds_new
  <T>__<M>.lean                                                     -- one proof per function
  Link.lean  Results.lean                                           -- etc/gen-link.py --bbolt
Proof/go_etcd_io/bbolt/internal/{common,freelist}/…                 -- ported
etc/api/bbolt.txt, etc/tcb-collections/bbolt.txt, interface/…
```

Every lemma module stays small (≤ ~400 lines), as the memory note on agent workflow asks.

### 4.2 Work units (the order, and what may run in parallel)

**U0. Foundation and design freeze.** Sequential, first, one agent.
- `Inv/Names`, `Model/*` definitions (no proofs beyond `proj_simps`);
- every `Inv/*` definition, and every `Inv/Store*` lemma *statement* with `sorry`;
- the internal specs of the shared callees: `beginTx`/`removeTx` (pool loan or spare),
  `freepages`, `db.mmap`/`mmapUnlocked`, `close_owned`, `loadFreelist_open`, `db.allocate`,
  `store_*`, the freelist interface split;
- `Api.lean`'s predicates as definitions.

**Round 2 (review 1, F5): the shared contracts are frozen here too**, as `sorry`'d statements in
`Model/*`, `Inv/*` and `Spec/go_etcd_io/bbolt/*`, so that no unit invents its own. A unit that
needs one of them changed goes back through U0's owner.
- **`wtxHeap tx dq X`** (§3.10): its shape over `WX`, and `wOK`.
- **The logical tree** `ltree X`, `wtxData`, `treeData`, `treeOK`, and **`stackAt`**: the
  cursor-stack relation for readers and writers, with its stability at a fixed `T` (R6).
- **`internal/common`'s accessor specs** (`Page`, elements, `Inode`, `Meta`, `ReadInodeFromPage`,
  `WriteInodeToPage`, `UsedSpaceInPage`, `InBucket`). U6, U7 and U9 call these; U1 proves them.
- **U6's search lemmas, which U7 uses:** `Cursor.seek`/`search`/`searchPage`/`searchNode`/
  `nsearch` over `stackAt` (the routing facts `kroute`/`routes` of `WriteTxShape`), and
  `Cursor.node`'s materialization post.
- **`rebalance`'s post, which is `spill`'s pre:**
  - `wOK X` with the keys' bounds of `txShapeR` (old `Rebalance*`);
  - no empty non-root node, every branch with ≥ 2 children, uniform leaf depth;
  - `wtxData X` unchanged;
  - `X.v` unchanged;
  - the frees as `store_free` steps.
- **`spill`'s post, which `Commit` consumes:**
  - `tx.pages` holds the written buffers at fresh W ids (`store_alloc`);
  - the new root, with `treeOK C'` for `C'` = base pages minus the freed ones, plus the written
    ones;
  - `treeData C' = T.cur`;
  - the frees in `pending[w]`;
  - `X.v` possibly re-based by remaps;
  - `allocate`'s failure: the mapping lost and an error.
- **`dereference`'s coverage contract** (round 3, A3: over the *live* objects of §3.13).
  - After `tx.root.dereference()`, no live object of `X` holds a `.view` slice.
  - The live objects are those the code reaches: `tx.root`, then `b.buckets` recursively, then
    each `b.rootNode.root()` through `children`.
  - The remap then moves every remaining `.view` holder live → dead: an unmaterialized inline
    child's `page`, already-spilled children, removed and stale nodes.
  - `mmap` (U4) assumes this contract; `spill` (U9) and `Bucket.dereference` prove it.

- **Round 3 (A2, A4, B1): every callee used across units**, with its users and its prover:

  | internal spec | used by | proved by |
  |---|---|---|
  | `Tx.page` (general, over the mapping and `tx.pages`), `DB.page`, `DB.meta`, `DB.pageInBuffer` | U5 (`Tx.init`), U6, U7, U8, U9, U10, U11 (`hasSyncedFreelist`, `meta`, `page`) | U4 |
  | `rdTx` read specs: `Tx.page` (the `rdTx` corollary of U4's), `Bucket.pageNode`, `Bucket.Cursor`, `Cursor.first`/`next`/`seek`, `Bucket.Bucket` (reader), `Bucket.ForEachBucket`, `Tx.forEachPage` | U10 (`tx_check`), U11 (`loadFreelist`) | U6 |
  | writer read specs (round 4, N1): `Bucket.Bucket` (writer: caches the child in `b.buckets`, registers the handle; `CreateBucket*`, `DeleteBucket`), `Bucket.ForEachBucket` and `Cursor.first`/`next` (writer; under `treeOK` the callback never runs, and the spec says so), `Bucket.pageNode` (writer: the materialized node), `Bucket.Cursor` (writer) | U7 (`Put`, `Delete`, `CreateBucket*`, `DeleteBucket`, `Bucket.free`), U9 (`Bucket.spill`'s `b.Cursor(); c.seek; c.node().put`) | U6 |
  | `Bucket.write` (with `node.write`, `node.size`) | U7 (`CreateBucket`: `bucket.write()`) | U9b |
  | `node.size` | U8 (`node.rebalance`: `n.size() > threshold`) | U9a |
  | reader `Tx.Rollback`/`Tx.close` over `rdTx` (the source given back) | U10, U11, U5 (public `Rollback`) | U5 |
  | `node.put`, `node.del`, `node.read`, `Bucket.node`, `Cursor.node` | U8, U9 (`parent.put`) | U7 |
  | `node.childAt`, `numChildren`, `nextSibling`, `prevSibling`, `removeChild`, `childIndex`, `node.root` | U8, U9 | U8 |
  | `node.free`, `Bucket.free`, `Bucket.forEachPageNode`/`_forEachPageNode` | U7 (`DeleteBucket`), U8, U9 | U8 (`node.free`), U7 (`Bucket.free`, `forEachPageNode`) |
  | `Tx.allocate` (adds to `tx.pages`; `store_alloc`; may remap), `DB.allocate`, `DB.mmap` | U9, U10 | U4 |
  | `DB.grow`, `fdatasync` | U10 | U4 |
  | writer `Tx.close`: before the publish, after it (`pub`), and with `ms = none` after a failed remap | U10, U5 (public `Rollback`) | U5 |
  | internal `DB.Begin.spec'`, `Tx.Commit.spec'`: the frozen posts plus `fmtErrorOk err` on errors (B1) | U11; U12 derives the public specs | U5, U10 |
  | `Bucket.dereference`, `node.dereference` (the coverage contract) | U4 | U9 |
  | `Bucket.rebalance` (post = spill's pre), `Bucket.spill` (post below) | U10 | U8, U9 |

- **Spill's post, made precise (round 3, B6.2–3).** On success:
  - `treeSlots C ∖ treeSlots C' ⊆ pendSlots fl'[w]`: every base page dropped from the tree was
    freed, and readers may still hold it;
  - `treeSlots C' ⊆ treeSlots C ∪ allocated(w)`;
  - the allocated slots are written in `tx.pages`;
  - `treeOK C'` and `treeData C' = T.cur`.

  On error, a disjunction:
  - the mapping intact (`fileSize`, `mmapSize`, `ErrMaxSizeReached` and `munlock` fail before
    `munmap`), with the store changed only by `store_free`/`store_alloc` steps;
  - or the mapping lost (`ms = none`, `wv = none`, a possible `junk` mapping).

  `rollback`'s `Reload`/`NoSyncReload` runs only in the first case.
- **Rebalance's post** keeps uniform leaf depth; it does not establish it (B6.4). `treeOK`
  supplies it at `Begin`, and `wOK` carries it.

It ports the pure parts of `PageModel`, `TreeStrict`, `TreeKeys`, `DBModel` and `TxModel`. It
leaves the internal API reviewable before the units below start. U0 is larger than in round 1;
budget it as two sub-steps:
- U0a: the models and the predicates;
- U0b: the frozen internal specs listed above.

The review of the design reviews U0's output, not this file.

**U1. `internal/common`.** Parallel after U0.
- Accessors and page/inode/meta functions: port the 117 old results, rebased on `UM/`
  (`Page__*`, `leafPageElement__*`, `readInodeFromPage`, `writeInodeToPage`, `Meta__*`).
- Needs §5's `hash/fnv` spec for `Meta.Sum64`/`Validate`.

**U2. `internal/freelist`.** Parallel.
- Port the 44 results (array, hashMap, shared).
- Split `Iface` into `flRoOwn` and `flPgOwn`.
- Restate the contract per part.

**U3. The store.** Parallel; the MVCC core; ghost and pure only.
- Prove every `Inv/Store*` lemma of §3.6 and `MetaLend`.
- Reuses: the old `mvccView`/`flBelow`/`flCurOK`/`ReleaseLemmas`/`DBRelease`/`DBFree`/
  `DBRollback` logic (pure); `MB/MapInv`, `MB/MapLoan`, `MB/MapCells` (gather, carve, lending).

**U4. The mapping and the file.** After U3's statements.
- `DB.page`, `meta`, `pageInBuffer`, `mmapSize`, `fileSize`, `grow`, `munmap`, `mmap`
  (open-time and remap), `allocate`, `Tx.allocate`, `Tx.page`.
- Ports: `DB__*` (logic), `DBAlloc`, `DBRemap`, `DBLost`.
- Templates: `MB/DB__mmap`, `DB__munmap`.

**U5. Lifecycle and locks.** After U0, using U3's statements.
- `beginTx`, `beginRWTx`, `removeTx`, `Begin`, `Tx.init`;
- `Tx.close`, `Rollback`, `nonPhysicalRollback`;
- `DB.Close`, `close`, `Stats`, `Info`, `Tx.Size`, `DB`, `Stats`;
- `isBolt`/`boltTx` laws.
- Ports: `DB__beginTx`, `DB__beginRWTx`, `DB__removeTx`, `Tx__close*`, `DBBegin`, `DBEnd`.
- Templates: `MB/DB`, `MB/DB__Close`, `MB/testMiniboltConcurrent`.

**U6. The read path.** Parallel after U0 (against U0's accessor specs; U1 proves them).
- `Cursor.*` (seek, search, searchPage, searchNode, nsearch, first, last, next, prev,
  `keyValue`, `goToFirstElementOnTheStack`), `Bucket.Get`, `Bucket.Cursor`, `Tx.Bucket`
  (reader and writer lookups), `Bucket.Bucket` (reader and writer), `openBucket`, `pageNode`,
  `ForEachBucket`, `Tx.forEachPage`, and the `rdTx` corollary of `Tx.page` (round 4, N1).
- Includes the functional content: `bktEnts`, `seekIdx`, `curAt`, `stackAt` stability.
- Ports: `Cursor*`, `CursorModel`, `CursorSearch*`, `BucketRead`, `BucketOpen`.

**U7. Writer mutations.** After U0; uses U6's search lemmas.
- `node.put`/`del`/`read`, `Cursor.node`, `Bucket.node`, `Put`, `Delete`, `CreateBucket*`,
  `DeleteBucket` (`Bucket.free`, `forEachPage*`), and `Tx`'s wrappers.
- Includes the `wtxData` lemmas.
- Ports: `Bucket__Put*`, `Delete*`, `CreateBucket*`, `WriteTx*`, `Shape*`, `Write*`.

**U8. Rebalance.** Parallel with U7, after U0.
- `node.rebalance`, `Bucket.rebalance`, `removeChild`, siblings, `node.free`.
- Data preservation, and the strengthened post (no empty non-root page, branches ≥ 2; uniform
  leaf depth kept).
- Ports: `Rebalance*`, `node__rebalance_s`.

**U9. Spill.** Parallel with U7 and U8, after U0. The largest unit; split it further by file:
- `node.split`/`splitTwo`/`splitIndex`/`write`/`size`/`spill`;
- `Bucket.spill`/`write`/`inlineable`/`dereference`.
- Includes: the data lemma for the spill, the `treeOK` clauses of §3.12, and the remap
  interaction (`allocate` through U4's spec).
- Ports: `Spill*` (25k lines, never built: check them first, in small modules).

**U10. The database side of Commit.** After U3, U4 and U5.
- `commitFreelist`, `Tx.write`, `writeMeta` (D22, the AU, `store_publish`, receipts),
  `rollback` (`Reload`/`NoSyncReload`), `freepages` with `tx_check.go`'s
  `recursivelyCheckBucket`/`recursivelyCheckPage`/`recursivelyCheckBucketInPage` (new),
  `Commit`.
- Ports: `CommitFL`, `Tx__commitFreelist`, `Tx__write`, `Tx__writeMeta`, `Tx__rollback_w`,
  `DBRollback`.
- Template: `MB/DB__commit`.

**U11. Open.** After U4 and U5; the internal Commit needs U10's spec only.
- `Open`, `init`, `metasZero`, `getPageSize*` (D18), `loadFreelist`, `hasSyncedFreelist`,
  `flock`/`funlock`/`fdatasync`, the options and logger calls;
- `fileHolds` and `fileHolds_new`.
- Ports: `DBOpen`, `DBOpenInit`, `MetaInj`, `FLPage`.
- Templates: `MB/Open`, `MB/OpenLemmas`, `MB/DB__init`.

**U12. Closing.**
- `Api.lean`'s laws under the D-A to D-D decisions;
- `Link.lean`/`Results.lean`;
- `etc/api/bbolt.txt` and its interface;
- the TCB collection;
- `verified-code`.

The backend's repair (the `_kv` restatements) is a separate stage after it, per the "raft first,
repair clients after" practice.

**Parallel schedule** (round 2: consistent with the dependencies above). Every unit after U0
works only against U0's frozen statements, never against another unit's proofs. At most 4
worktrees run at once.

| wave | units | needs |
|---|---|---|
| 0 | U0a, U0b | — |
| 1 | U1, U2, U3, U6 | U0 |
| 2 | U4, U5, U8, U9a (`split`/`splitTwo`/`splitIndex`/`write`/`size`) | U0 (U4 and U5 use U3's statements, not its proofs) |
| 3 | U7, U9b (`node.spill`, `Bucket.spill`/`write`/`inlineable`/`dereference`) | U0; U9b calls `allocate` through U4's frozen spec |
| 4 | U10, U11 | U0 (U11's internal `Commit` through the frozen spec) |
| 5 | U12 | all |

Each wave fits in four worktrees. Only U12 requires every earlier unit to be finished. Waves are
ordered only to keep the number of worktrees at four; a unit may start early if one is free.

Round 3 (A4) re-check. Every "used by → proved by" arrow in U0b's table that crosses waves goes
through a frozen statement:
- U6 (wave 1) uses U4's `Tx.page`/`DB.page`/`DB.meta`;
- U8 (wave 2) uses U7's `node.put`/`del`/`Bucket.node`;
- U9 uses U4's `Tx.allocate` and U7's `node.put`;
- U10 and U11 use U5's `Tx.close` and U6's `rdTx` specs.

No unit waits on another's proof. U10 also waits for §5's item 0 (`WriteAt` at any length).

Round 4 (N1): the new rows also cross only through frozen statements:
- U7 uses U9b's `Bucket.write` and U6's writer read specs;
- U8 uses U9a's `node.size`.

Nothing in the schedule needs another change.

### 4.3 Risks (hardest first)

- **R1. Spill and data preservation (U9).** The largest proof. Its 25k old lines were never
  built, and the data abstraction and new `treeOK` clauses are new.
  - Map iteration order in `Bucket.spill` (children) and `rebalance` (nodes) is
    nondeterministic, so every loop invariant must be order-independent.
  - Remaps in the middle of the spill invalidate view-backed slices. `dereference` must cover
    every one: `node.key`, inode keys and values. It does not cover `Bucket.page` (inline):
    show it is never read after a remap (only `rootNode == nil` children are skipped).
- **R2. Rebalance (U8).** Merges, removals and root collapse under the logical tree. The
  reviewer of the spec could not confirm map-order independence.
- **R3. Commit's error paths (U10).** Round 3: A1's `WriteAt` generalization (§5, item 0) lands
  first, since `tx.write`'s chunks reach `0x7FFFFFFE` bytes (a leaf of four maximal entries, or
  a large synced freelist page). Round 2: the goroutine and channel parts are covered:
  `wp_fork_tok` gives the child its token, and `SyncSpsc.wp_sspsc_close` returns the child's read
  transaction at `close(ech)` (review 1, F6). What remains:
  - `NoSyncReload(freepages())` needs `tx_check`'s recursive checks proved panic-free and
    report-free on `treeOK` trees (new code; needs a `bytes.Compare` spec and closure reasoning
    for `ForEachBucket`).
  - `Reload`'s `flCurOK` across releases and allocations of the failed transaction.
- **R4. The store under concurrency (U3).**
  - The lending arithmetic over Qp (old `slotsOK` pains), done once, generically:
    `lend_borrow_all`/`lend_return_all` over a view list.
  - `store_release` against `readonlyTXIDs` with the deregister-before-`RemoveReadonly` window
    (the `fltx` fragments).
- **R5. Remap and `Close` (U4/U5).** Gathering every cell of the mapping from four owners:
  store, `W`, metas from `rwR`, and metas from the lend. The meta lending protocol is copied
  from minibolt, where it is proved.
- **R6. Functional cursors in writers (U6).** Stale stacks at an unchanged `T`; empty leaves
  (`next`/`Last` skip them; `Prev` is excluded by D14); `Last`'s hang in an all-empty writer
  bucket is fine (the WP is partial).
- **R7. Rebasing old proofs on the byte model and module system.** `FfiSyntax` to `GooseExts`,
  `leAt` to `ByteEncoding`, old `bytesPointsto` to `BytesView`. Mechanical but wide (every
  ported file); budget it per unit.
- **R8. Spec decisions D-A to D-D:** decided in round 2 (fix 2 for D-C), and being landed. The
  fork change of `fork-open.diff` must land on `goose-lean-v2` and the pin move (`etc/goose.py`,
  `examples/go.mod`) before U11.
- **R9. Build budget.** Large proof terms (`Spill*`, `Commit`): use `etc/lean-check.py --split`
  and small modules; check `etc/importers.py --count` before editing `Inv/*` statements, which
  every proof imports.

