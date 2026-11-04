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
- **U0b done** (2026-11-03): every internal function spec one unit uses and another proves is
  stated (`sorry` proof stubs), over three new modules (`Model/PageAt`, `Model/WOps`, `Inv/Ctx`);
  the cross-unit table, per unit, is "U0b: the internal specs" below.
- **Next: wave 1** (U1, U2, U3, U6; U8's and U9a's local specs need nothing else either), then the
  schedule of §4.2. The open-time specs wait for the fork commit `fork-open.diff`.

## U0b: the internal specs (the frozen cross-unit contracts)

Every spec is one file `Spec/go_etcd_io/bbolt/<T>__<M>.lean` (the main package; a variant's suffix:
`_r` reader, `_w` writer, `_i` any transaction, `_s` the spare reader pair, `_err` the internal
`Begin`/`Commit`), `Spec/go_etcd_io/bbolt/internal/{common,freelist}/<T>__<M>.lean`, with its stub
`Proof/…/<same>.lean` (`theorem <T>.<M>.wp_proof : <T>.<M>.spec := by sorry`; the proving unit adds
its callees' specs as hypotheses). A unit **proves** the specs listed for it and **may assume**
every other spec below (and U0a's `sorry`'d lemmas of other units), never another unit's proof.

### The contexts (`Inv/Ctx.lean`; pure relations in `Model/WOps.lean`, `Model/PageAt.lean`)

- `BC` (a database's parameters: names, namespace, location, path, stats pointer, receipts' base),
  `BC.core`/`BC.full` (`isBoltCoreP`/`isBoltP`).
- `statsTok r m q` (the statistics' token: `ex` at `q`, or with `m = false` the exclusive part's
  `done` half, inside `Commit`/`Rollback`/`DeleteBucket` once `txExcl` is out).
- **`wtxW K tx r m X`**: the writer's working state (`wtxFrac` at 1 without its facts and the
  data's quarter, plus the core and the stats token): what every writer internal spec runs over,
  through `rebalance` and `spill`. `wtxLost` after a failed remap. `boltTxDef_wtxW` opens a whole
  writer's `boltTx` into it (U5).
- **`wdbW K tx v w`**: the writer's database side in its exclusive part (`wdbLive` on the view `v`
  of `w.C`, with `wdbOK`); `wdbLost` after a failed remap. **`wtxEnd`**: a writer ready to close.
- **`rdTxK K tx src q T v`**: a reader with its view exposed (`rdTx_rdTxK`, U6); `rBkt v tx b dq bv`
  a reader's bucket (the root's at `rootVal v`, `rdTxK_root`); `pairBack` what its close gives back.
- Relations: `nodeAdded`/`matGrow` (materialization), `matReady` (a page position can be
  materialized), `lPath`/`lRoutes`/`lLeaf`/`bktLocalOK` (the writer's search, any bucket of `X`,
  the root included), `bktOpened`, `nodeRootIn`, `wsIdx`/`wsPutAt`/`wsDelAt`/`pageWsAs`/`insSize`,
  `positions`/`extents`/`bktFreed`/`FLPg.freeAll` (frees), `rebalOK` (rebalance's post) and
  `spillPre` (spill's pre), `spillC`/`spillOK` (spill's post), `FLStep`/`applySteps` (a failed
  spill's freelist), `allocRes` (allocation), `derefRel`/`liveReach`/`liveFresh` (the coverage
  contract), `wdbRemap`, `wdbGrown`, `bktNames`/`bktEntry`/`pageWalk`/`freeIdsOf` (readers),
  `pageInodesAt`/`pageReadable` (`ReadInodeFromPage`).
- Lemma statements (`sorry`): `ltree_nodeAdded`, `wtxData_matGrow`, `wOK_nodeAdded` (U7);
  `lRoutes_found`, `lRoutes_leafFor` (U6, the search lemmas); `viewCells_page_acc`,
  `viewCells_loc_acc`, `viewCells_slices_acc`, `rdTx_rdTxK`, `rdTxK_root`, `rdTxK_view` (U6);
  `wtxHeap_node_acc`, `wtxHeap_bkt_acc`, `boltTxDef_wtxW` (U5).

### Per unit: the specs it proves (it may assume all the others)

| unit | proves | its users |
|---|---|---|
| U1 | `internal/common/*` (81 specs: `Page`, `leafPageElement`, `branchPageElement`, `Inode`, `InBucket`, `Meta` accessors and setters, `Meta.{Validate,Copy,Write,Sum64}`, `ReadInodeFromPage`, `WriteInodeToPage`, `Unsafe*`, `Assert`, `NewInBucket`, `Pgids.Merge`) | U2, U4–U11 |
| U2 | `internal/freelist/Interface__{Free,Allocate,Rollback,ReleasePendingPages,AddReadonlyTXID,RemoveReadonlyTXID,FreeCount,PendingCount,EstimatedWritePageSize,Write,Reload,NoSyncReload,Init,Read}`, `newFreelist` | U4, U5, U7–U11 |
| U3 | (no function spec: `Inv/Store`'s and `Model/Store`'s lemmas, U0a) | U4, U5, U10, U11 |
| U4 | `Tx__page`, `DB__page`, `DB__pageInBuffer`, `DB__meta`, `DB__hasSyncedFreelist`, `Tx__allocate`, `DB__grow`, `fdatasync` | U5–U11 |
| U5 | `TxStats__{Inc*,GetRebalance}` (13), `DB__beginTx_s`, `Tx__Rollback_r`, `Tx__close_r`, `Tx__close_w`, `DB__Begin_err`; lemmas `wtxHeap_node_acc`, `wtxHeap_bkt_acc`, `boltTxDef_wtxW` | U4, U6–U11 |
| U6 | `Tx__page_r`, `Bucket__Cursor_i`, `Cursor__seek_w`, `Bucket__pageNode_w`, `Bucket__Bucket_w`, `Bucket__ForEachBucket_w`, `Bucket__Bucket_r`, `Bucket__ForEachBucket_r`, `Tx__forEachPage_r`; lemmas `lRoutes_found`, `lRoutes_leafFor`, `viewCells_*_acc`, `rdTx_rdTxK`, `rdTxK_root`, `rdTxK_view` | U7, U9, U10, U11 |
| U7 | `node__put`, `node__del`, `node__read`, `Bucket__node`, `Cursor__node`, `Bucket__free`; lemmas `ltree_nodeAdded`, `wtxData_matGrow`, `wOK_nodeAdded` | U8, U9 |
| U8 | `node__childAt`, `node__childIndex`, `node__numChildren`, `node__removeChild`, `node__root`, `node__nextSibling`, `node__prevSibling`, `node__free`, `Bucket__rebalance` | U7, U9, U10 |
| U9a | `node__size`, `node__write` | U8, U9b |
| U9b | `Bucket__write`, `Bucket__dereference`, `Bucket__spill` | U4, U7, U10 |
| U10 | `DB__freepages`, `Tx__Commit_err` | U11 |
| U11 | (the open-time specs, once the fork lands: below) | — |

Unit-internal functions (`Cursor.search`/`searchPage`/`searchNode`/`nsearch`/`first`/`next`/
`keyValue`, the reader's `pageNode`/`seek`, `Bucket.openBucket`, `_forEachPageNode`,
`node.dereference`, `node.split*`/`spill`, `DB.allocate`, `DB.mmap`'s remap, `beginRWTx`,
`removeTx`, `commitFreelist`, `Tx.write`/`writeMeta`/`rollback`, …) are each unit's own business:
it states and proves them in its own files.

**Waiting for the fork commit (`fork-open.diff`)**: `DB.mmapUnlocked`, `DB.close` on `Open`'s
error paths (`close_owned`), `loadFreelist` (its local freelist published under `metalock`),
`DB.mmap`'s open-time case, `Open`'s internal specs. Their callees above (`newFreelist`,
`Interface.Read`/`Init`, `DB.freepages`, `DB.hasSyncedFreelist`, `DB.meta`, `DB.page`) are stated.

### U0b: deviations and findings

1. **U0a fixes** (minimal, the definitions made a contract unstatable):
   - `objOwn`'s bucket `tx` field is persistent (`↦□`) but the root bucket's: `boltBktDef` holds a
     handle's `b.tx ↦□ tx`, while the heap held it at `dq`; `Tx.close` writes the root bucket
     whole, so the root's stays owned.
   - `rtxFrac` pins the reader's root bucket (`tx.root`: its header a persistent copy of the
     view's root, no caches, no page, no root node) and its nil page cache: every read starts
     there, and the existential `t` left it unknown.
2. **Reader handles** (U0a's gap 17): the reader internal specs carry a reader bucket as `rBkt`
   (fields at a fraction, persistent for an opened one); `boltBktDef`'s reader branch does not hold
   it yet (U6 adds it: `rBkt … DFrac.discard`).
3. **Specs over local resources where the caller's state varies**: `node.put`/`del`/`read`/
   `size`/`write`/`childIndex`/`numChildren`/`removeChild`, `Bucket.write`, `Tx.page`, `DB.page`,
   `DB.meta` are stated over the points-tos they touch (and `viewCells` at any fraction to read view
   bytes), so that `Put`, `rebalance`, `spill` and `CreateBucket`'s stack-allocated bucket all use
   them; the heap-level ones over `wtxW`. `wtxHeap_node_acc`/`_bkt_acc` move between the two.
4. **The writer's search is over the logical tree of any bucket** (`lPath`/`lRoutes`), not over
   `wStackAt` (which is a named top-level bucket's): `Bucket.spill`, `CreateBucket` and
   `DeleteBucket` search the root bucket.
5. **Iris parsing**: a multi-field record update does not parse inside `iprop` (nor a `p ↦ {…}`);
   the posts use `NRec.withEnts`, `nodeAfterRead`, `hdrWritten`, `WDb.withFl`.
6. **Findings for the owning units**:
   - U1: `Meta.Validate`'s "not valid → non-nil error" needs `ErrInvalid`/`ErrVersionMismatch`/
     `ErrChecksum` non-nil in `PkgInit.lean`'s `bboltErrorsVars` (today only `∃ e, … ↦□ e`).
     `WriteInodeToPage`'s spec takes any bytes after the header (`node.write`'s zeros are a case).
     `Verify`/`getEnvVerify` stay unstated (§5 item 4).
   - U5: `txs_close` (U0a) takes `ghostVar r.n.ex 1` from the caller, which a holder of `txExcl` has
     given to the invariant; restate it when proving `Tx.close_w`.
   - U6: the reader's `boltBktDef` branch must carry `rBkt` (item 2).
   - The only cross-unit specs with a callback are `Bucket.ForEachBucket_r` and
     `Tx.forEachPage_r` (an invariant indexed by the iteration's position); the writer's
     `ForEachBucket_w` is stated where it never calls back (`rootShape`: no nested bucket below a
     top-level one).

## U3: findings (2026-11-04; the store's statements that are false or unprovable)

Proved: `Pm_fractional`, `Ps_fractional`, `wdbOK_partition`; `mvccView_release`, `_releaseRange`;
`lent_lt_half`; `storeOK_deregister`, `_wreturn`, `_gather`, `_carve`, `_setFl`, `_reload`;
`store_deregister`, `store_wreturn`, `store_wborrow`, `store_reload`, `meta_take`, `meta_put` (with
the cells' lending machinery, private in `Inv/Store.lean`: a page's cells as its slots', borrowing
and returning a view's fraction, `|R| · rfrac ≤ 1` from the deposits). The rest is false as
stated, or unprovable from what the statement gives; each needs a statement or invariant change
(design decisions, not made here):

1. **`storeOK` lacks the current tree's MVCC rule** (F1). Nothing in `storeOK` says that the current
   tree's slots are not free, that `allocs` of its pages are at most `C.txid`, or that they are not
   pending for a committed transaction (that is `wdbOK`'s B2, which the store cannot see). False:
   `storeOK_register`/`store_register`, `storeOK_wbegin`/`store_wbegin` (counterexample: no reader,
   no writer, `fl.free = [W64 2]` with slot 2 the root page: `storeOK` holds, the new view's
   `mvccView` fails); `storeOK_wclose`/`store_wclose` (`pub = true`, `wtx = some C.txid`, a tree slot
   pending for `C.txid`: allowed by the last clause, which fails once `wtx = none`). Fix: add
   `mvccView σ.fl (View.ofC b σ.C)` (base irrelevant) to `storeOK`; `store_publish` then needs the
   new tree's slots not pending and not free, its `allocs` at most `w`.
2. **`allocs` unbounded**: `storeOK_free`/`store_free` break `flBelow`'s `alloctx < t` when
   `allocs[id] ≥ w` (nothing bounds `allocs`; with `wv = none` no view constrains it). Fix: an
   `allocs` clause (values `≤ C.txid + 1`, or the F1 clause plus the writer's allocations).
3. **The mapping bound for slots entering the store** (`storeOK` clause `s < l / 4096`):
   `storeOK_free`/`store_free` (the freelist-page branch) and `storeOK_publish`/`store_publish`
   give no bound for the new store slots (counterexample: a new tree slot at `≥ l / 4096`).
   `store_publish` also gives no per-slot length 4096 of `bs`. Fix: hypotheses
   `∀ s ∈ S, s < l / 4096 ∧ (bs s).length = 4096` (the caller's `wdbOK` has them).
4. **`storeOK_publish` (pure)**: `hbytes` does not say a new page is either an old page (same id,
   same bytes) or wholly new; `pagesAgree C'.pages r.v.pages` fails for a page of `C'` starting
   inside an old extent. `store_publish`'s `hbytes` is the right form; restate the pure one so.
5. **`storeOK_rollback`/`store_rollback`**: after `store_free` of the old synced freelist page a
   reader older than `C.txid` may (by `storeOK`) cover it when its `alloctx` is 0 (unknown); the
   rollback then removes it from the store under that reader. Fix: a clause "before the publish, a
   slot pending only for the writer and not in the tree is covered by no view" (true: `store_free`
   adds such slots only from `W`).
6. **`storeOK_release`/`store_release`**: a reader of txid 0 makes `releasePending [0]` run
   `releaseRange 0 (2^64-1)`, freeing its pages (`0 - 1` wraps). Fix: readers' txids `≥ 1` (bbolt's
   first meta has txid 1), in `rOK` or as a hypothesis on `ro`.
7. **`storeOK_alloc`/`store_alloc`, `mvccView_alloc`**: with `n = 0`, `canAlloc r 0` holds for any
   `r` and `alloc` still records `allocs[r] := txid`, breaking a view whose page is `r`. Fix:
   `0 < n` in `canAlloc` (Allocate's post gives `r ≠ 0`, which implies it for the code).
8. **`mvccView_free`**: false for views covering slots `≥ 2^64` (`W64` wraps: a view page at
   `2^64 + 4` with overflow 1, freeing id 5 with `allocs[5] = 100 > v.txid`). Fix: hypothesis
   `∀ s, coversSlot v.pages s → s < 2^64` (store views satisfy it).
9. **`storeOK_wborrow`**: false when `σ.wv = none` (then `wlent := true` breaks `wv = none →
   wlent = false`); add `σ.wv ≠ none` (`store_wborrow` has it, and is proved).
10. **`metaLend`'s second case** (`out ½ true`) records nothing a reader could contradict:
    `meta_borrow` (a reader with `mlk` finds the cells out with the writer) and `meta_return` (case
    1 or 2: no `mlk`/`mtok` to give back) are unprovable; `store_gather` too (it does not take `out`).
    Fix: a token for the reader's loan (minibolt's `0 ↪[γl]{½}`), and `store_gather` taking the
    writer's `ghostVar B.out ½ false`.
11. **`store_carve`**: `bs` is unconstrained, but the store's cells must hold `σ.bytes` (the
    page cache, owned whole by the invariant, so the caller cannot read it). Fix: `store_gather`
    hands out a witness of the bytes (a ghost variable) that `store_carve` takes back.
## Shared-statement fixes (U6's findings, 2026-11-04; decided by the coordinator)

No frozen public statement (`Spec/go_etcd_io/bbolt/`'s public triples) changed.

1. **`rStackAt_next`/`wStackAt_next` were false** (`sSucc` said nothing of the old stack below
   the moving depth: a stack at index 0 of a 5-entry leaf moving at its parent lands at
   position 5, not `i + 1`; a stack past its leaf's end after `Seek`, or in an empty leaf,
   lands at its own position). `sSucc d els els'` now takes the depth and is `next`'s move
   literally (`els' = els.take d ++ e' :: R'`, `e'` one further than `els[d]`, `R'` first);
   the new `sEndBelow v es pids els d` is what `next`'s upward loop found (branch indices
   below `d` the last, leaf index `≤` its leaf's entries, the leaf's bounds ordered; the lower
   bound `count - 1` is not needed). Both lemmas take the old path `pids` and the new `pids'`
   explicitly, `hlen : d + 1 < els.length ↔ d + 1 < els'.length` (`goToFirstElementOnTheStack`
   descends iff `d` is a branch), and `sEndBelow` only when `d` is above the leaf; they give
   the new stack's `rStackAt`/`wStackAt` at `min (stackPos ...) es.length` and its position:
   `+ 1` at the leaf, `new + leafIdx els = old + |old leaf's entries|` above it. Proved
   (`stackPos_next`, public, from U6's `stackPos_succ_up`/`_leaf`, copied privately into
   `Model/Cursor`); `wStackAt_next` no longer takes `wCtx`, `rStackAt_next` no longer `viewWF`.

2. **`rdTxK_root` was unprovable** (its wand takes back any `rBkt`, whose header may be the
   view's bytes, while `rtxFrac` pinned a persistent heap header). `rtxFrac` now holds the root
   bucket's fields *as* `rBkt v tx (txRoot tx) (DFrac.own q) (rootVal v)` (plus its
   `FillPercent` at `q`), in place of `tx.root ↦ t.root'` and the header clause; `t.pages' = null`
   moved to the facts. `rdTxK_root` is proved (framing). `rBkt`, `locOwn`, `rootVal` moved from
   `Inv/Ctx` to `Inv/Tx` (same statements; `Inv/Ctx` re-exports them). `Tx.init` (U5) splits
   the struct points-to of `tx.root` into its fields (its header a persistent copy: `rBkt`'s
   left disjunct, `ib.root' = W64 v.root`; its `page` nil when `v.root ≠ 0`).
3. **`Tx.page_r` was not derivable from `rdTxK`** (the mapping was an existential `ms` in
   `PmNoTok`, with no bound for `Tx.page`'s `id·4096 < 0xFFFFFFFFFFFF`). `rtxFrac` now holds
   `PmNoTok`'s parts at the view's mapping, `∃ l, ghostVar B.map … (some (v.base, l)) ∗
   mapFields r.db … (some (v.base, l)) ∗ ⌜∀ id pg, v.pages !! id = some pg → (id+1)·4096 ≤ l⌝`
   (`Tx.begin`, U5, gets it from `storeOK`: `rOK`'s base, `viewInStore`, slots `< l/4096`). The
   length bound is where the mapping is made: **`mapFields`' mapped case carries `⌜len ≤
   0xFFFFFFFFFFFF⌝`** (`Inv/Locks`; `DB.mmap` maps `mmapSize`'s result, which caps it at
   `maxMapSize`; U4/U11 prove it when writing the fields), with a `DFractional` instance for pure
   facts so that `mapFields` stays `DFractional` (`Pm_fractional` unchanged). Fractions for
   `Tx.page` (one `dqt` for `tx.pages` and `tx.db`): `dqt = DFrac.own (QpMul q ½)`, from
   `tx.pages`' `q` (two halves) and `tx.db`'s `txDbQ q = QpMul q ½ + QpMul q ¼`.

4. **`boltBktDef`'s reader branch carries the bucket** (U0b item 2): with `r.rw = false`,
   `∃ v bv, viewOf r v ∗ rBkt v tx b DFrac.discard bv ∗ ⌜bktEntry v.pages (rootVal v) n bv⌝`
   (what `Bucket.Bucket_r` gives for a top-level bucket `n` of the reader's view; `viewOf`
   agrees with `rdTxK`'s view), so that the public reader `Get`/`Cursor` triples reach the
   bucket's fields. Still persistent (`boltBktDef_persistent`, a `sorry`). `Inv/Tx` imports
   `Model/WOps` (for `bktEntry`).

## Shared-statement fixes (U8's findings, 2026-11-04; decided by the coordinator)

No frozen public statement changed.

1. **`wtxHeap` holds `⌜objsDisj X.t⌝`** (a bucket's node is no bucket and no other bucket's node):
   `wtxHeap`'s pure part is now `heapOK tx X` (`X.rl = txRoot tx ∧ objsDisj X.t ∧ …`, items
   below). `objsDisj` moved from U8's `Rebalance/Objs.lean` to `Model/Wtx.lean` (U8's
   `objs_node`/`objs_bkt` unchanged); `Rebalance/Heap`'s `wtxHeap_objsDisj` is proved. Kept by
   every operation since `nodeAdded`/`bktOpened` add locations fresh in `X.t.objs`; with it
   `wtxHeap_bkt_acc` (U5) is provable (`objs_bkt`).

2. **Every bucket's `tx` field is the transaction**: `heapOK`'s `∀ bl B, X.t.bs !! bl = some B →
   B.bv.tx' = tx`, read by `wtxHeap_heapOK` (`node.free`, `node.rebalance`, `Bucket.node` read
   `n.bucket.tx`).

3. **The siblings' parent**: `node.nextSibling`/`prevSibling` take `rp.nv.bucket' = bl` of the
   parent's record (`n.parent.childAt` calls `n.parent.bucket.node`). `n.parent = n` is excluded
   in the heap: `heapOK`'s `∀ bl B n r, … B.ns !! n = some r → r.nv.parent' ≠ n` (kept: a node's
   parent is set to an existing node, `nodeAdded`, or by `rebalance`'s moves to another node).
4. **`node.free`'s pre** (with `pgid ≠ 0`): `X.t.mv.txid' = w.wtxid` (`Free` takes
   `tx.meta.Txid()`), and the page's `16 ≤ pg.length`, `pageId pg = pgid.toNat`, leaf or branch
   flags (`tx.page`'s `FastCheck`); the bucket's `tx` field from `heapOK` (item 2). Still open
   for its prover: `Tx.page`'s `id·4096 < 0xFFFFFFFFFFFF` (from `wtxW`'s `mapFields` bound and a
   view page inside the mapping, which `wtxW` does not hold yet: as `rtxFrac`, it could).

5. **`spill`'s pre after `rebalance`**: `rebalOK`'s post and `spillPre` hold the new `wOKR X`
   (`Model/Wtx`): `wOK` with `txPg` replaced by `txPgLeaf` (leaf entries of page id `0`: what
   `spill`'s `node.write` needs; a merged branch node's entries are no longer its page's);
   `wOK_wOKR`. `bktKeys` stays (the post). `bktLocalOK` (the searches `Bucket.spill` makes after
   its children's spill, `Cursor.seek_w`, `Cursor.node`, `Bucket.Bucket_w`, `ForEachBucket_w`,
   `Bucket.free`) holds `txPgLeaf` of its bucket instead of `txPg`: U6/U7 must not use a branch
   node's page equality there. `treeData_spill` takes `wOKR`. **`nlocOK`** (in `wOK`, so also
   for `DeleteBucket`'s post): every registered node is an object (a fresh location is
   unregistered), and only a *live* registered node is a node of its bucket at its page id (the
   nodes `rebalance` and `DeleteBucket` remove are dead, their entries kept).
6. **`wtxData_rebalance`** (`Model/LTree`) is U8's `wtxData_rebalance'` (adds
   `X'.v.pages = X.v.pages`; `rebalOK` gives `X'.v = X.v`), proved; U8's `Rebalance/Data.lean`
   can go.
7. **The root collapse** (U8's finding): the collapsed child's `inodes`/`children` become the
   root's, so the child cannot keep them. A **dead node now owns only its struct** (`objOwn`'s
   `false, .node` case; `objOwn_weaken` drops the rest, `objOwn_node_ptr_acc` reads the struct
   either way): the child goes to `dead` with its struct (rather than leaving `objs`, which would
   break `nlocOK`'s "registered ⇒ object", i.e. the freshness `nodeAdded`'s registry insert needs
   after the collapse, in `spill`'s materializations).

8. **`fills_fractional`** (`Inv/WtxHeap`) is proved (each handle's `FillPercent` points-to
   splits, and two halves agree on the value).

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

