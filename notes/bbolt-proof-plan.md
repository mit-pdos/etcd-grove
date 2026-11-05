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

## U3: the store (done 2026-11-04; findings and fixes)

Every U3 lemma is proved (`Model/Mvcc`, `Model/Store`, `Inv/Store`, `Inv/Locks`; no `sorry`,
`#print axioms` clean). The first round found 30 of the statements false or unprovable; the
coordinator approved the fixes, applied as follows (internal invariants and lemma statements; no
frozen public statement changed):

1. `storeOK` has the current tree's MVCC rule (`∀ b, mvccView σ.fl (View.ofC b σ.C)`), so a new
   view of it is safe (`register`, `wbegin`) and, after the publish, tree slots are not pending
   (`wclose`). `storeOK_publish` takes the new tree's slots not pending (`hnp`) and its new slots
   not free and at least 2.
2. `storeOK` bounds `allocs` (values at most `C.txid + 1`), for `free`'s `alloctx < t`.
3. `free`'s freelist-page branch and `publish` take the new slots' mapping bound and 4096-byte
   lengths; `storeOK` also bounds `C.hwm ≤ 2 ^ 62` (`Free`'s pending ids below `2 ^ 62`),
   `publish` takes `C'.hwm ≤ 2 ^ 62`, `free`'s freelist-page branch `id + n ≤ C.hwm` and (Iris)
   that the page is no tree slot; `free`'s tree branch (pure) keeps the page's bytes.
4. The pure `storeOK_publish`'s `hbytes` has `store_publish`'s form (an old page, or wholly new).
5. `storeOK`: before the publish, a slot pending only for the writer and not in the tree is
   covered by no reader (`rollback`).
6. `metaR` keeps `1 ≤ C.txid` (while open) and the readers' txids `F` in `[1, C.txid]`;
   `store_release` takes that (`releaseRange(minid, t - 1)` wraps at `t = 0`, and `t + 1` must not
   wrap). **Open gap for U11:** `fileHolds`' `metaOk` allows a current meta of txid 0 (meta 1
   invalid), which bbolt then serves to readers; this is a real (edge) bbolt behavior,
   `nonissues/bbolt-txid0-reader-release.md`. U11 must establish `1 ≤ C.txid` at `Open`: it needs
   a premise (a frozen statement) or a code fix. Reported, not decided here.
7. `0 < n` on `alloc` (as a hypothesis of `mvccView_alloc`/`storeOK_alloc`/`store_alloc`, not in
   `canAlloc`: `Interface__Allocate`'s spec is frozen; `allocRes` and `Tx.allocate` give it).
8. `mvccView_free` takes the view's slots below `2 ^ 64` and the freelist's entry lengths.
9. `storeOK_wborrow` takes `σ.wv ≠ none`.
10. The meta lend has a loan token (`BNs.mln`): home and the writer's case hold it, the reader
    borrowing the cells holds it (`meta_borrow` returns it, `meta_return` takes it); `meta_take`
    deposits `mlk` until `meta_put` (bbolt's `writeMeta` holds `metalock` throughout);
    `store_gather` takes the writer's `out ½ false`; `store_publish` takes `out ½ true` (the metas
    are out at the commit point, so the lend never holds the old metas).
11. The store slots' bytes have a ghost witness (`BNs.byt`, `bytesWit`): half in `pagesInv`, the
    other half there too while mapped; `store_gather` hands it out, `store_carve` takes it back
    (so the new mapping's cells hold the store's bytes). `store_free`'s freelist-page branch and
    `store_publish` take `ms ≠ none` (they update the witness with both halves).

`BNs` gained `mln` and `byt` (`Inv/Names.lean`; `bnsOf`/`mkGs` positions 16 and 17): U11 allocates
them at `Open`. The maintainer's freelist fix (9ec32691bc: `releaseRangeOne` in Go's order,
`rollback` a no-op without an entry) was ported into the U3 proofs.

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

9. **The writer's view inside its mapping** (follow-up to item 4): `wtxW`'s and `wtxFrac`'s
   mapping part is `∃ l, mapFields r.db … (some (X.v.base, l)) ∗ ⌜∀ id pg, X.v.pages !! id =
   some pg → (id+1)·4096 ≤ l⌝`, as the reader's `rtxFrac`; with `mapFields`' `l ≤ maxMapSize`,
   `pageIdx_lt_maxMap` (`Inv/Tx`) gives `Tx.page`'s `id·4096 < 0xFFFFFFFFFFFF` for a view page
   (`node.free`, `Bucket.node`'s reads, `pageNode_w`). Established at `beginRWTx` (U5) from
   `storeOK` (the writer's view is in the store, `StoreSt.wOK`'s `viewInStore`, store slots
   `< l/4096`); kept by a remap (U4: `DB.mmap`'s new mapping covers every store slot,
   `store_carve`'s `hl`, and the view's pages are kept, re-based); allocation does not touch it:
   an allocated page (past the old mapping or not) is in `tx.pages`, and `Tx.page` of a page of
   `tx.pages` (`pm !! id = some p`) needs no bound; only a view page (`pm !! id = none`) does.

## Shared-statement fixes (U2's findings, 2026-11-04; decided by the coordinator)

No frozen public statement changed.

1. **The 14 `Interface__*` specs** (`Spec/go_etcd_io/bbolt/internal/freelist/`) are U2's corrected
   ones: stated over `ifaceCall fli m` (moved from U2's `Lemmas/IfaceCall.lean` to
   `Inv/Freelist.lean`), what Go's `fl.M(args)` steps to (`methods Interface.ty m` has no
   semantics). Each proof file's `wp_proof'` is its `wp_proof` (callee specs as hypotheses); the
   `sorry`'d duplicates are gone. All 14 are proved.
2. **`NoSyncReload`**: `PgidsIncr ids`, ids `≥ 2`, `ids.length + fl.pendingIds.length < 2^63`,
   `(fl.noSyncReload ids).free ≠ [] ∨ fl.free = []`.
3. **`Reload`**: `(flIds pg).Nodup`, ids `≥ 2`, `(flIds pg).length + fl.pendingIds.length < 2^63`,
   `flIds pg ≠ [] ∨ fl.free = []`. The callers can supply 2 and 3 from what is maintained:
   `Reload(p)` (rollback, a synced freelist page): `wdbOK`'s `flCurOK` (`Nodup`, `≥ 2`, ids
   `< 2^62` or committed-pending, `fl.free ⊆ flIds pg`, so a non-empty `fl.free` gives a non-empty
   page); `NoSyncReload(freepages())` (rollback without a synced page): `freeIdsOf C` is sorted,
   `≥ 2`, below `hwm`, and contains every free id (`flBelow`, `wdbOK`'s B2); the length bound in
   both from `storeOK`'s `hwm ≤ 2^62` and `flBelow`'s pending ids `< 2^62` (distinct ids in
   `[2, 2^62)` number fewer than `2^62`). U10 needs the counting lemma (distinct ids in a range)
   and, for `NoSyncReload`, `fl.free ⊆ freeIdsOf C` (from `flBelow` and the free ids not being
   tree slots); `Open`'s `loadFreelist` uses `Init`, unaffected.
4. **`releaseRangeOne`** (`Model/FL`) keeps a touched entry's other pairs in the code's
   swap-removal order (`srLoop`, `srLoop_perm`, `mem_srLoop`, moved from U2's
   `Lemmas/ReleaseGo.lean`); `FLPg.releaseRange`/`releasePending` keep their names, and U2's
   `releaseRangeGo`/`releasePendingGo` equal them (`rfl`). U3's proofs adapted (only where they
   read the kept pairs): `Model/Mvcc`'s `mvccView_releaseRange` (a pair kept is one allocated
   outside the range, `mem_srLoop`), `Model/Store`'s private `rrOne_perm` (the ids, up to order)
   and `relOK_releaseRange` (the same membership). `storeOK_release` unchanged.
5. **`FLPg.rollback`** is the code's: nothing without a pending entry for `txid`, else the new
   `FLPg.rollbackEntry` (the old body). U2's `rollbackGo` equals it (`rfl`). `Model/Store`: the
   old proof is the private `storeOK_rollbackE` over the new `StoreSt.rollbackE`, and
   `storeOK_rollback` (same statement) splits on the pending entry; the private
   `rollback_allocs`/`rollback_pending`/`mvccView_rollback`/`pendSlots_rollback`/
   `pendingIds_rollback_perm` are over `rollbackEntry`. `Inv/Store`'s `store_rollback` unchanged.
6. **`flPgOwn`'s pending entries are non-nil**: its map of entries holds `⌜p ≠ null⌝ ∗ ownPending
   p pd` (every entry the code stores is a fresh allocation); U2's `ownPending_nonnull` (false as
   stated, the one `sorry` of U2's proofs) is deleted, `pds_to_pend`/`pend_to_pds` reworked.

U3's untracked work copies (`Proof/go_etcd_io/bbolt/Store/Wip*.lean`) repeat the old proofs of
items 4 and 5 and need the same edits.

## Shared-statement fixes (U6's and U9a's findings, batch 4/5, 2026-11-04)

1. **`mapFields`' mapped case** carries `⌜len ≤ 0xFFFFFFFFFFFF ∧ base ≠ null⌝` (one pure
   conjunct, so the destructuring patterns of its users are unchanged; `DB.mmap`'s writer of the
   fields states the base, U4). `Read/Base`'s `mapFields_base_nonnull` is proved: the read path's
   `Tx.page` calls rest on no `sorry` for it.
2. **`Bucket.pageNode_w`** takes `∀ c l, B.nm !! c = some l → l ≠ null` (a cached node is not
   nil; `bktClean`'s `B.nm` clause, `bktLocalOK_nm_nonnull` for its callers); its branch `sorry`
   is gone.
3. **Split pieces need not own their inodes' capacity** (U9a): `NRec` gains `capOwn : Bool`
   (default `true`); `objOwn`'s live node owns `ownSliceCap Inode r.nv.inodes'` only if
   `r.capOwn` (`node.split`'s pieces but the last set it `false`: their capacity is the next
   pieces' inodes; `Spill/Split`'s post gives the pieces without capacity). Kept true where
   capacity is used: `nodeClean` (so `wOK`/`wOKR`, before the spill) and `nodeAdded` hold
   `r.capOwn = true`, and `node.put`/`node.del` take it as a premise (they append). Chosen over
   dropping split nodes from the heap because `tx.allocate`'s remap (`dereference`) walks the
   pieces, as the parent's children, before they are spilled.
4. `Inv/Ctx`'s `reg_persistent'` instance is public.

## Shared-statement fixes, batch 6 (2026-11-04; decided by the coordinator)

1. **`fileHolds`: the current meta's txid is at least 1** (`Inv/FileHolds`' `fileOK` and
   `fileHolds_decode`'s post: `1 ≤ C.txid`; the frozen `fileHolds` docstring in
   `Spec/go_etcd_io/bbolt/Api.lean`, docstring only). bbolt never leaves a current meta of txid 0
   after `init` (D22 excludes an in-process tear, the fork's `init` is crash-safe, `WriteTo`
   copies a database of txid at least 1). `fileHolds_new` is unaffected (a fresh file is the
   `size = 0` case). U11 gets `1 ≤ C.txid` for `metaR` (U3's fix 6) from `fileHolds_decode`;
   `nonissues/bbolt-txid0-reader-release.md` is now `blocks-proof: no`.
2. **`wdbOK_free`** (U8's `Rebalance/Free.lean`) is proved, over `Model/Store`'s new public
   `pendSlots_freePages`, `pendingIds_freePages_perm`, `freePages_pending_lookup`,
   `freePages_pending_mono`, `mem_pagesSlots_iff`, `runIds_mem_toNat`, `toNat_W64_of_lt` (public
   names for U3's private lemmas). It needs the writer's txid not to wrap (`C.txid + 1 < 2^64`:
   its pending entry is not `committedPending`) and `C.hwm < 2^64` (the synced freelist page's
   slots, as `w64`s): neither is anywhere in the writer's resources (`wdbW`, `wtxW`; only the
   store's `storeOK` and `metaR` hold them), so **`wdbOK` gains a last clause `w.C.txid + 1 <
   2^64 ∧ w.C.hwm < 2^64`** (maintained: `Open` from `fileHolds`' `txid < 2^62` and the current
   meta's `pgid`; `Commit` from the new state's `treeOK`/`metaOk`, U10/U11).
3. **For U11**: `BNs`' ghost names `mln` and `byt` (positions 16, 17) must be allocated at `Open`.

## Shared-statement fixes, batch 7 (U7's findings, 2026-11-04; decided by the coordinator)

1. **`node.read`** takes `pageElemsIn pg` (new, `Model/PageAt`: every element inside the page);
   `matReady` holds it (before the header id); `leafWF_elemsIn`/`branchWF_elemsIn` (`Model/WOps`)
   derive it for callers. U7's `wp_proof_in` is `node.read.wp_proof` (no `sorry`).
2. **`ltree_nodeAdded` was false**; the shared statement is U7's `Write.ltree_nodeAdded'`
   (`Write/Mat.lean`, proved) over `matFresh` (moved to `Model/WOps`: no cached node is the new
   one, an inline bucket had no root node; inline buckets at position 0 only). `matGrow`'s step
   carries `matPos X bl pgid parent` (new: the position is a root page without a root node, or a
   branch node's unmaterialized child, `wOK_nodeAdded`'s `hpos`).
3. **`wtxData_matGrow`** moved to `Write/Mat.lean`, with `wOK X`, proved by induction over
   `wOK_nodeAdded`, the new `wOK_matFresh`, `wOK_inlineLeaf` (`Model/WOps`, `sorry`, owner U7) and
   U7's `wtxData_nodeAdded'`.
4. **`wtxData_put`/`wtxData_del`** take `hinj : ∀ n', bktLoc X n' = some bl → n' = n` (the root
   bucket's cache injective: `gensOK_bktLoc_inj`, `Inv/Tx`, from `gensOK`'s second clause). The
   walk's termination: `wOK_leaves_fuel` (`Model/LTree`, `sorry`, owner U7): under `wOK` more fuel
   walks the same leaves (before `Commit` a branch node is its page, `txPg`, so the logical tree has
   the base tree's shape, whose depth the strict tree bounds by its page count, below `X.fuel`);
   `wOK` is what put/delete/materialization keep, and rebalance/spill run after it.
5. **`common.Verify`'s spec** is `Spec/go_etcd_io/bbolt/internal/common/Verify.lean` (U2's
   contract: `WP f {{ Q }} ∧ Q`), proof stub `Proof/.../internal/common/Verify.lean` (`sorry`:
   `getEnvVerify`'s `os.Getenv`); U2's `Callees.lean` copy is gone, its users take
   `bbolt.internal.common.Verify.spec`. **`wtxHeap_node_insert`** (`Inv/WtxHeap`, `sorry`, owner
   U7): a fresh node's object (`X.t.objs !! l = none`, its parent not itself) into its bucket's
   nodes, live (`WX.addNode`); the registry insert is `wtxCore`'s `ghostMapAuth r.n.nl` at the
   fresh key (`nlocOK`: a registered node is an object, so the key is fresh).

## Shared-statement fixes, batch 8 (U7's findings, 2026-11-04; decided by the coordinator)

1. **U7's proofs replace the shared `sorry`s**: `Write.wOK_matFresh` (`Write/WOk`),
   `Write.wOK_inlineLeaf` (with the premise `B.bv.rootNode' = null` the shared statement lacked:
   `inlineGood` is only for a bucket without a root node), `Write.wtxHeap_node_insert`
   (`Write/Heap`); `Model/WOps`' and `Inv/WtxHeap`'s statements are deleted (their only user,
   `Write/Mat`'s `wtxData_matGrow`, is U7's).
2. **"Every registered node is an object"** moved from `nlocOK` (`wOK`) to `heapOK` (its last
   clause, `∀ n y, X.nloc !! n = some y → (X.t.objs !! n).isSome`), so `Bucket.node` gets the
   registry's freshness of a new location from `wtxW`. Users adapted: `heapOK`'s parent clause is
   now `Hok.2.2.2.1` (U8's siblings, `node.free`, `Rebalance/Heap`, `Write/Heap`); the constructions
   in `Rebalance/Heap` (`wtxHeap_setNode`, two) and `Write/Heap` prove it (objects only grow,
   `isSome_insert_of`); U9b's `Spill/DerefHeap` and U4's `Mmap/Rebase` already had it.
3. **`wOK` and `wOKR` end with `viewWF X.v`** (the base view is a `treeOK` committed state's):
   non-empty keys and `pageReadable` (`treeStrict`'s page facts), and `rootShape`'s entries within
   `bboltEntryMax`. **`fileHolds` already had the bound** (`treeOK`'s `rootShape`: "every entry
   within `bboltEntryMax`" in the frozen docstring, clarified: every write goes through `Put`, whose
   spec takes it; `WriteTo` copies such a database; `issues/bbolt-max-value-size-unusable.md`);
   `fileHolds_new` is unaffected (empty); the backend's `snapshot.WriteTo` docstring notes it. It
   reaches the store and the views through `treeOK` (`storeOK`, `viewWF`). **`wOK_nodeAdded`** is
   then provable: the new node's entries are its page's (`pageWsAs`), a page of the bucket's base
   tree (`matPos`: the bucket's root page, from `bktNested`'s entry value, or a child of a branch
   page), so `rootShape` bounds them (`entriesBounded`); its `nodeClean`/`bktKeys`/`txPg` facts
   come from `viewWF`'s `treeStrict` (the page's keys, bounds and header id), the registry and
   live facts from the step.

## Shared-statement fixes, batch 9 (U4's findings, 2026-11-04; decided by the coordinator)

1. **Mapped addresses are positive**: `DB.page`'s and `Tx.page`'s premise `data ≠ null` is
   `0 < data.addr` (`arrayIndexRef_byte` needs it); `mapFields`' mapped case carries
   `⌜len ≤ 0xFFFFFFFFFFFF ∧ 0 < base.addr⌝` (`DB.mmap` proves it from `unix.Mmap`'s cells, U4);
   `Read/Base`'s `mapFields_base_nonnull` now gives `0 < b.addr` (its callers, `Tx.page_r`,
   `pageNode_w`, `node.free`, pass it to `Tx.page` unchanged). U4's `wp_proof'`s are the
   `wp_proof`s (`Tx.page.wp_proof` takes `Page.FastCheck`'s spec).
2. **`wtxHeap_rebase` was false** (a live bucket with `pst = .view`, `isrc = .own dq`: re-based it
   is `(stale, own)`, whose `pageOwn` needs bytes nobody has). Fixed by **`BRec.unview` making a
   view-backed page's source stale** (`isrc := .stale` when `pst = .view`): a page in the old
   mapping has no bytes after the remap whatever its source, and nothing new to maintain (the
   alternative, a `pageSrcOK` fact in `wtxHeap`/`wOK` and `Tx.allocate`'s premises, would be kept
   by every bucket operation). U4's `wtxHeap_rebase'` is the shared `wtxHeap_rebase`
   (`Mmap/Rebase.lean`, without `pageSrcOK`); `Inv/WtxHeap`'s `sorry` is gone.
3. **`wBytes` covers the partial last slot** of the file (`4096 · s < size < 4096 · (s + 1)`: its
   first `size - 4096 · s` bytes, `(wb s).take …`): a file truncated to `growSize + AllocSize`
   need not end on a page, so `DB.grow` can meet `wdbGrown`.

## Shared-statement fixes, batch 10 (U8b's finding, 2026-11-04; decided by the coordinator)

**The records agree with the writer's freelist**: `flView X fl` (`Model/WOps`): (a) every base
slot is covered by the logical tree iff not pending, `∀ s, coversSlot X.v.pages s → (lCovers X s ↔
s ∉ pendSlots fl)`; (b) `mvccView fl X.v`; (d) `fl.allIds.Nodup ∧ ∀ id ∈ fl.allIds, id.toNat <
2^62`; (c) `viewWF X.v` is `wOK`'s/`wOKR`'s (batch 8), not repeated. It lives where `X` and `w`
meet: **`txExcl`'s writer branch** holds `⌜ws.1 = some X.v ∧ flView X w.fl⌝` (`Inv/Txs`, which now
imports `Model/WOps`); `Bucket.rebalance` takes `flView X w.fl` and gives `flView X' fl'`.
`flView_cover` (proved) is `spillPre`'s coverage clause. Stubs (`sorry`), with owners:
`flView_canFree` (U8b: `node.free`'s `canFree` for a live node's base page), `flView_withWs` (U7:
`Put`/`Delete` on a leaf of a non-root bucket), `flView_nodeAdded` (U7), `flView_nodeFree` (U8b:
`node.free`'s step; `Bucket.free`'s frees by it, for `DeleteBucket`). Also to prove where they
arise: U5 at `beginRWTx` (no pending entry for the new txid, every base slot covered: the store's
`storeOK`), U7 for `CreateBucket`/`DeleteBucket` (root-bucket entries), U9b/U10 through spill and
`Commit` (`spillOK`, the new committed state's view).

## Shared-statement fixes, batch 11 (U5's findings, 2026-11-04; decided by the coordinator)

1. **Positive addresses**: `isBoltCoreP`'s pure part is `⌜t0 < 2^62 ∧ 0 < db.addr⌝` (`Open` from
   `&DB{}`); `rtxFrac`'s and `wtxFrac`'s facts end with `0 < tx.addr`, and `wtxCore`'s with it
   (`⌜r.db = K.db ∧ r.rw = true ∧ 0 < tx.addr⌝`, so `boltTxDef_wtxW` carries it; `beginTx`/
   `beginRWTx` from `&Tx{}`); `boltTxDef_nonnull` is proved. `txEntry`'s done branch is unchanged
   (`d = r.db ∨ d = null`): `Tx.close` sets `tx.db = nil`, so the done entry cannot keep `d =
   r.db`; `r.db = db` is `txDB`'s (`reg`), and `db`'s non-nullness is now `isBoltCoreP`'s.
   Adapted: `Tx.page_r` (U6) for `rtxFrac`'s new fact.
2. **`txs_register`, `txExcl_take`, `txs_close`** (`Inv/Txs`) are U5's corrected forms (moved from
   `Txn/Txs`, the false ones deleted): `txs_register` takes all of `tx.db` and leaves `ex` with the
   caller (returns `reg` and `tx.db` at `¾`); `txExcl_take` gives `▷ txExcl`; `txs_close` takes only
   the `done` half and returns it `true`. `Txn/StatSlot` uses the unprimed name.
3. **`wtxHeap_node_acc` deleted** (false: the new record's parent could be the node itself); its
   replacement is U8's `wtxHeap_setNode` (`Rebalance/Heap`, with `⌜r'.nv.parent' ≠ n⌝`), and
   `wtxHeap_live_node_acc` for out-and-back. **`wtxHeap_bkt_acc`** is U5's (`Txn/Heap`, with
   `⌜B'.bv.tx' = tx⌝`; `Inv/Ctx`'s deleted). Adapted: U9b's `Spill/DerefHeap` (`node_peek`,
   `bkt_peek`). U9b's untracked `Spill/NodeDeref.lean` still names `wtxHeap_node_acc`.
4. **`txBytesDef_acc` for a writer** is not threatened by a remap: `Tx.allocate` is called only by
   `node.spill` and `Tx.commitFreelist`, `DB.mmap` only by `Open` and `DB.allocate`, so a remap
   happens only inside `Commit`, whose caller has given up `boltTx` (the whole of it) and gets
   `txDone` back: no `txBytes` of the writer is used with a `boltTx` after a remap.
5. `notes/perennial-changes.md`: `|==>` binds tighter than `∗` in iris-lean; no other occurrence in
   bbolt's `Inv/`, `Model/`, `Spec/`.

## Shared-statement fixes, batch 12 (U9b's finding, 2026-11-04; decided by the coordinator)

`Bucket.dereference.spec` was not provable from `liveFresh X ∧ liveReach X` (a live node with an
empty-key entry panics at `Assert(len(inode.Key()) > 0)`; a non-nil zero-length key fails
`Assert(n.pgid == 0 || len(n.key) > 0)`; a live node's child, cached child bucket or root node
need not be an object of the heap; `null ∈ B.ns`; a dead object live).

1. **`derefPre X`** (U9b's, moved from `Spill/DerefModel` to `Model/WOps`, same statement) is a
   premise of `Bucket.dereference.spec` and of `Tx.allocate.spec` (its remap calls `dereference`),
   before `liveFresh`/`liveReach`. U9b's `wp_proof'` is the `wp_proof` (no `sorry`).
2. **Derived, not maintained**: `wOKR_derefPre`, `wOKR_liveFresh`, `wOK_derefPre`,
   `wOK_liveFresh` (`Model/WOps`, proved). For that:
   - **`liveOK`** (in `wOK`/`wOKR`) gains two clauses at its end: every node of a bucket of
     `X.t.bs` is live, and no dead object is live (`liveOK`'s third clause is now `.2.2.1`).
     `bktLocalOK` already assumed the first for its bucket. Kept by: U7 (materialization: the new
     node is live and fresh; `CreateBucket`/`DeleteBucket`), U8b (`rebalance`'s post `wOKR`: a
     removed node goes dead and leaves `live`), U5 (`beginRWTx`: no nodes, no dead objects).
   - **`liveFresh`** asks `ksrc ≠ stale` only of a node with a non-nil key (`objOwn` owns a nil
     key's nothing; `nodeClean` holds the key's source only for a non-nil key). U9b's
     `liveFresh_step` and `node.dereference`'s proof adapted (`Hrnf.2 Hif`).
3. **`derefRel` ends with `derefStep X X'`** (moved with `optRel`, `Src.heap`, `nodeDerefd`,
   `nodeStep`, `bktStep` from `Spill/DerefModel` to `Model/WOps`; their lemmas stay there): without
   it nothing after a remap says the records' structure (children, caches, root nodes, dead
   objects) is unchanged, so `spill`'s next `allocate` could not re-establish `derefPre` or
   `liveReach` (already a gap for `liveReach`). U9b's `derefRel_of_step` gives it.
4. **Stubs (`sorry`), owner U9c**: `allocRes_derefPre` (`Inv/Ctx`: a successful `allocate` keeps
   `derefPre ∧ liveFresh ∧ liveReach`, through `derefStep`, `WX.rebase` (after `derefOK` nothing
   live becomes stale) and `WX.addPage`) and `derefRel_rebase_derefPre` (the lost branch). Between
   its `allocate`s `spill` keeps `derefPre` through its own steps (split pieces, `node.write`,
   the parent's `put`: non-empty keys, the pieces live nodes of the bucket, the new root's
   children live): U9c's own lemmas.
5. **`Bucket.spill.spec`'s success post** adds `derefPre X' ∧ liveFresh X' ∧ liveReach X'`
   (`commitFreelist`'s `allocate`, U10). Its pre is unchanged (`spillPre`'s `wOKR` gives
   `derefPre` and `liveFresh`).

Adapted in others' working files (uncommitted, not committed by me): `node__rebalance.lean`,
`Bucket__rebalance.lean` (`liveOK`'s `.2.2` → `.2.2.1`).

## Shared-statement fixes, batch 13 (U7's finding, 2026-11-04; decided by the coordinator)

1. **`nodeAdded`** constrains the new node's inodes and key (`wOK_nodeAdded` was unprovable): after
   `r.ksrc ≠ Src.stale`, `r.ins.length = r.ws.length ∧ (r.nv.key' = slice.nil ↔ r.ws = [])`
   (`node.read`'s post: `pageInodesAt`, `keySliceAt` when the page has elements). The destructuring
   patterns in `Write/Mat` (2), `Write/FlView`, `Rebalance/RblMat` get `hrins, hrkn` (U8b's
   `matExtra` premise of `rbl_nodeAdded` can now come from them).
2. **`flView_withWs`/`flView_nodeAdded`**: `Model/WOps`' `sorry` stubs are deleted; the shared
   lemmas are U7's `Write.flView_withWs'` and `Write.flView_nodeAdded'` (`Write/FlView`, proved,
   same statements; names kept so U7's files are unchanged).

## Shared-statement fixes, batch 15 (U4's findings, 2026-11-04; decided by the coordinator)

1. **`dbFixed` pins `MmapFlags`**: `∃ x, db.MmapFlags ↦□ x ∗ ⌜x = W64 0 ∨ x = W64 0x8000⌝`
   (`OptsM.ok`'s restriction, carried in by `Open`, U11), so `mmapF`'s premise is derivable.
2. **`dbLogger lg` is `boltLogger lg`**: the discard case is the global's value, which is a
   `boltLogger` (`discardLogger_boltLogger`, `Inv/Bolt`, `sorry`, owner U11: bbolt's package facts
   must say what `discardLogger` holds, `&nopLogger{}` from the fork's `discardlogger.diff`; that is
   `etc/gen-init.py`'s `SPECIAL` entry for bbolt and its generated `Init.lean`; then the no-op
   methods meet `boltLogger`). `db.Logger()`'s nil test resolves (`boltLogger nil` is `False`).
3. **The mapping's length**: `mapFields`' mapped case carries `len % 4096 = 0 ∨ len =
   0xFFFFFFFFFFFF` (its pure part is now `len ≤ max ∧ 0 < base.addr ∧ (…)`, so `H.2` is `H.2.1`;
   `Read/Base`'s `mapFields_base_nonnull` adapted). U4's correction: `mmapSize` caps at
   `maxMapSize`, not a multiple of 4096. The partial last slot's cells (`[4096·(len/4096), len)`)
   are the writer side's: **`wCells`' mapped case** adds `∃ vf, cellsR base (4096 * (len / 4096))
   (len % 4096) vf` (empty for whole pages), so the remap's `munmap` gets every cell of `[0, len)`
   (store slots and metas from `store_gather`, `W` slots and the partial slot from `wCells`).
4. **`store_cells_agree`** (`Inv/Store`, `sorry`, owner: the maintainer): in one atomic step `e`
   (`Iris.ProgramLogic.Language.Atomic ↑s e`, `osN ⊆ E \ pagesN N`), with the new mapping `(b, l)`
   in the file's `OsMeta` and the store slots' new cells (any values), the cells hold the bytes the
   witness `W` records (the half `store_gather` gave), with the ghost state handed back; the
   continuation runs at `E \ pagesN N`. That is `store_carve`'s `hW` and cells. How it is proved:
   `wp_atomic` opens `pagesInv`, each store slot's `osSlot` is read against its cells with OsFs's
   `osCell_agree` byte by byte (the bboltfs example's `cellsR_agree`), `bytesWit` gives
   `σ.bytes s = W !! s`, and the invariant is closed in the postcondition, unchanged.

## Shared-statement fixes, batch 16 (U5b's findings, 2026-11-04; decided by the coordinator)

1. **Non-null, not positive, transaction and database locations**: `rtxFrac`'s, `wtxFrac`'s and
   `wtxCore`'s `0 < tx.addr` is `tx ≠ null` (`&Tx{}` gives `typedPointsto_not_null`; `Tx` has
   pointer fields, so `structFieldRef_plain` does not apply), and `isBoltCoreP`'s `0 < db.addr` is
   `db ≠ null` (no proof needs `db`'s address). `boltTxDef_nonnull` adapted.
2. **`managed` is false** (`Tx.Rollback`/`Tx.Commit` assert `!tx.managed`): `rtxFrac`'s facts end
   with `t.managed' = false`; `wtxCore`'s pure part is `r.db = K.db ∧ r.rw = true ∧ tx ≠ null ∧
   X.t.t.managed' = false` and `wtxFrac`'s facts end with `tx ≠ null ∧ X.t.t.managed' = false`
   (`boltTxDef_wtxW` carries it). Established at `beginTx`/`beginRWTx` (`Tx{}`), kept by every
   writer operation (none writes `X.t.t`).

## Shared-statement fixes, batch 17 (U5b's finding, 2026-11-04; decided by the coordinator)

**`txEntry`'s done branch holds no share of `tx.db`** (`Tx.close` ends with the plain store
`tx.db = nil`, not atomic, so the invariant cannot be opened around it): live = `tx.db ↦{¼} r.db ∗
done ½ false ∗ (∃ s, tx.stats ↦ s) ∗ (txExcl ∨ ex) ∗ readerHandles r` (the `d = r.db` existential
gone); done = `done ½ true ∗ ex 1 ∗ ∃ s, tx.stats ↦□ s`. **`txs_close`**: from `done ½ false` (the
`ex` token in the invariant), `|={E}=> tx.db ↦{¼} r.db ∗ (∃ s, tx.stats ↦□ s) ∗ done ½ true` (it
persists the statistics itself). `txs_register`'s freshness: a live entry's `¼` of `tx.db` against
the caller's whole one, a done entry's `tx.stats ↦□` against the caller's whole `tx.stats ↦`
(the new `txStats_own_discard_false`, through the `PageCount` field). `txDoneDef` unchanged.
`Inv/Txs`'s and `Txn/Txs`'s (U5) proofs adapted. `TxStats`' getters (`Txn/StatsAdd`) take any
fraction.

## Shared-statement fixes, batch 18 (U6b's finding, 2026-11-04)

Duplicate top-level names (a module importing both failed): `BC.core_persistent` and
`BC.full_persistent` (`Read/Base`, `Txn/Stats`) now in `Inv/Ctx`; `srcOwn_persistent`
(`Rebalance/Base`, `Spill/DerefCopy`) now in `Inv/WtxHeap`. A scan of the units' directories found
four more pairs of different statements under one name, renamed in the later file:
`Rebalance/RTreeX`'s `pht_chain` → `pht_chainR`, `Spill/DerefRel`'s `filterMap_wDat` →
`flatMap_filterMap_wDat`, `Write/Mat`'s `bktDataOf_eq` → `bktDataOf_eqM`, `Write/FlView`'s
`withWs_bs` → `withWs_bs_at`. Still mine: `viewCells_slices_acc` (`Inv/Ctx`, `sorry`; U8's
`srcOwn_acc` uses it).

## Shared-statement fixes, batch 19 (U5b's finding, 2026-11-04; decided by the coordinator)

**`txRoot tx ≠ null`** (`Tx.close`'s whole-struct store of `tx.root` needs `typedPointsto_combine`):
at the end of `rtxFrac`'s facts, `wtxFrac`'s facts and `wtxCore`'s pure part (after batch 16's
`managed` fact: `wtxCore`'s is `r.db = K.db ∧ r.rw = true ∧ tx ≠ null ∧ X.t.t.managed' = false ∧
txRoot tx ≠ null`). `Tx.init`'s post gives it (`typedPointsto_not_null`) at `beginTx`/`beginRWTx`.

## Shared-statement fixes, batch 20 (U8b's findings, 2026-11-04; decided by the coordinator)

1. **`flViewU X fl`** (`Model/WOps`) = `flView X fl ∧ covU X ∧ pagesExt X.v.pages ∧ pendAligned
   fl`: U8b's `CovW`/`coverW`/`covU` moved from `Rebalance/RblX` to `Model/WOps`; `pagesExt`
   (every view page's extent ends by `2^62`, item 3: a fact of the view, which does not change
   before `Commit`; `beginRWTx`, U5, from `storeOK`'s `hwm ≤ 2^62`) and `pendAligned` (item 4,
   `FLPg.WF`'s last clause) new. `flView` itself is unchanged, so U7's and U8b's lemmas over it
   stand; **`txExcl`'s writer branch** and **`Bucket.rebalance.spec`** (pre and post) hold
   `flViewU`. Kept by (owners): a leaf's new entries and a materialization (U7: `covU` through
   `withWs`/`nodeAdded`; `pagesExt`, `pendAligned` unchanged there), a free (U8b's
   `Rebalance/RblXSFl`; `DeleteBucket`'s, U7), `spill` (U9c).
2. **`nsLive X`** (U8b's, moved to `Model/Wtx`) is `liveOK`'s fourth clause (batch 12), so in
   `wOK`/`wOKR`: `wOK_nsLive`, `wOKR_nsLive`. (Not in `heapOK`: spill's spilled children stay in
   `B.ns` without being live.)
5. *(done with batch 14)* every bucket the root or a handle's, in `heapOK` (its last clause).
6. **`node.size.spec`** has no `insSize ins < 2^63` premise (the sum wraps the same on both
   sides); U9a's proof, `Bucket.write`'s and `node.rebalance`'s calls adapted.
7. **`nodeAdded`** adds `∀ w ∈ r.ws, isBktFlag w.flags → w.vs = Src.view ∨ w.vs = Src.own
   DFrac.discard` (after batch 13's two clauses; patterns get `hrvs`) and, in the child case,
   `rp'.capOwn = rp.capOwn` (after `rp'.ksrc = rp.ksrc`). `r.nv.key' ≠ nil` when `r.ws ≠ []` is
   batch 13's `↔`. `Bucket.node` (U7) establishes them from `node.read`'s `pageWsAs pg (posSrc B)`.
8. **`flView_canFree`/`flView_nodeFree`** (stubs, U8b) take `viewWF X.v` (and the latter `covU X`)
   in place of `wOK X`.
9. *(done)* the shared `matReady` lemma for a view page: `Inv/MatReady`'s `wtxW_matReady`.

U8b's `Bucket__rebalance.lean` (uncommitted) takes `flViewU` apart for its `rblX_init` (the
`covU`/extent/alignment `sorry`s gone, `nsLive` from `wOK`); its post must now give `flViewU X'`.

## Shared-statement fixes, batches 22-25 (2026-11-04; decided by the coordinator)

- **22** (U7b): `inlineBnd ipg` (`Model/Wtx`: every entry of an inline page within
  `bboltEntryMax`) in `bktClean`'s inline clause (`inlineGood B.ipg ∧ inlineBnd B.ipg`) and
  `bvalOK`'s (`inlineGood (inlinePage v) ∧ inlineBnd (inlinePage v)`). `Bucket.Bucket_w` (U6/U7)
  proves it on open (from `rootShape` for a view value, from `Put`'s premise for a written one).
  U7b's `Write.wOK_nodeAdded'` then discharges its three premises from `nodeAdded` (batch 20) and
  `bktClean`; moving it in as the shared `wOK_nodeAdded` (and `wtxData_matGrow` after it) waits for
  `Write/MatOK` to build.
- **23** (U7k): `Model/LTree`'s `wtxData_put`/`del`/`create`/`drop` stubs deleted; the shared
  lemmas are `Write.wtxData_put'`/`del'` (`Write/Data`) and `Write.wtxData_create'`/`drop'`
  (`Write/DataBkt`), proved (no callers of the stubs).
- **24** (U4b): `wdbOK`'s `w.m.size ≤ l` dropped (`DB.grow` can extend the file past the mapping);
  `wCells` holds only the `W` slots inside the mapping (`4096 · (s + 1) ≤ len`) and the partial
  slot; `dbFixed` pins `db.AllocSize ↦□ W64 0x1000000` (`DefaultAllocSize`, set by `Open`, U11).
- **25** (U7b): `bktLocalOK` ends with `viewWF X.v` (materialization's `Nodup` children and
  `posDisjoint` come from the view's uniqueness); callers building it from `wOK` take `wOK`'s.

## Shared-statement fixes, batches 26-28 (2026-11-04; decided by the coordinator)

- **26** (U4b): `store_gather`'s post adds `⌜C.metaOk ∧ ∀ s ∈ slotsOf C fl, 2 ≤ s ∧ s < l / 4096 ∧
  (bs s).length = 4096⌝` (after the witness fact; from `storeOK`'s `metaOk`, slot and mapping
  clauses). Proved.
- **27** (U9c): `Inv/Ctx`'s `allocRes_derefPre`/`derefRel_rebase_derefPre` stubs were false without
  `objsDisj X.t` (two buckets holding one node location); deleted, the shared lemmas are U9c's
  `allocRes_derefPre'`/`derefRel_rebase_derefPre'` (`Spill/AllocDeref`, proved, with `objsDisj`).
- **28** (U8b): `node.del.spec`'s found case gives the inodes exactly, `r.ins.eraseIdx (wsIdx r.ws
  kb)` (no existential). `node__del.lean`'s proof (U7c) breaks at line 187 (its `iexists` of the
  inodes): routed to U7c.
- Still open for me: `viewCells_slices_acc` (an empty slice of the view needs a positive address
  or an array points-to: `ownSlice_empty`; propose the premise `∀ x ∈ L, x.2 ≠ []` or `0 <
  v.base.addr`), `store_cells_agree`'s proof.

## Batch 21 and `viewCells_slices_acc` (2026-11-04)

- **21 = D-F (approved by the user, 2026-11-04; D-C precedent, U5b's finding after batch 17;
  applied in `feed4d07da`)**: `txDB tx γ
  db` (`Spec/go_etcd_io/bbolt/Api.lean`, `txDB_persistent`), `txDBDef B N tx db` (`Inv/Tx`, `B`/`N`
  the client's: `∃ r, isBoltDef B N db ∗ reg tx B r ∗ ⌜r.db = db⌝`); `DB.Begin`'s and
  `DB.Begin_err`'s posts, `Tx.DB`'s and `DB.Info`'s pres. `notes/decisions.md` (D-F) and
  `notes/bbolt-spec-decisions.md` (D-F, with the backend impact: `γ.db` beside every `txDB`).
  Stale interface files (regenerate with `etc/gen-interface.py etc/api/bbolt.txt` once every bbolt
  module builds): `interface/Spec/go_etcd_io/bbolt/Api.txt`,
  `interface/Proof/go_etcd_io/bbolt/{DB__Begin,DB__Begin_err,DB__Info,Tx__DB}.txt`.
- **`viewCells_slices_acc`** takes `0 < v.base.addr` (decided by the coordinator: `mapFields` gives
  it) and is proved (`addNQ`: `|L| + 1` equal shares). `Inv/Ctx` imports
  `internal/common/Lemmas/Bytes` (`bytesPointsto_ownSlice`). Its one caller, U8's `srcOwn_acc`
  (`Rebalance/Base`), needs the premise too (not a one-liner: routed).

## Batch 14 (kind-keyed heap objects, U7's finding): applied 2026-11-04 (maintainer 3)

The writer heap's single object map keyed by location could not show a fresh node location is no
bucket's (`structFieldRef` is abstract for non-plain structs; Perennial proposal in
`notes/perennial-changes.md`). Applied as designed:
- **`Model/Wtx`**: `WTx.dead : GMap Loc (Loc × NRec)` (dead nodes only, with their bucket's
  location) and a new `WTx.deadB : GMap Loc BRec := ∅` (dead buckets, `DeleteBucket`'s);
  `WTx.objs` folds only the buckets' nodes over `dead` (as `.node` objects); the new
  `WTx.bobjs := bs ∪ deadB` is the buckets. `WX` gains `liveB` (after `live`): bucket liveness.
  **`objsDisj`** is only "a node is in at most one bucket" (`∀ bl B, bs !! bl = some B → ∀ n,
  (B.ns !! n).isSome → ∀ bl' B', bs !! bl' = some B' → bl' ≠ bl → B'.ns !! n = none`; the
  conjunction with "no bucket at a node's location" is gone, so users take `hd … n hn bl' B' hb'
  hne` directly). `handlesOK` is over `bobjs`. `liveOK`'s root and `bs` clauses are over
  `liveB` (same shape: `X.rl ∈ X.liveB ∧ (live nodes are node objects) ∧ (bs ⊆ liveB) ∧ nsLive ∧
  (dead nodes not live)`).
- **`Model/WOps`**: `bktLocalOK`'s first clause, `bktOpened` (`(X.t.bobjs !! c).isNone`,
  `liveB := X.liveB.insert c ()`), `liveReach`'s bucket clause, `derefPre`'s bucket clauses are
  over `liveB`; `nodeAdded`'s freshness `(X.t.objs !! l).isNone` now means "no node object at
  `l`" (text unchanged). **`derefStep`** gains `X'.t.deadB = X.t.deadB ∧ X'.liveB = X.liveB`
  before its last (`bs`) clause (so the `bs` clause is `.2` ×12, `liveB` `.2` ×11 `.1`).
- **`Inv/WtxHeap`**: `wtxHeap` = `⌜heapOK⌝ ∗ txFields ∗ rootFill ∗ ([∗map] l ↦ o ∈ X.t.objs,
  objOwn … (l ∈ X.live) o) ∗ [∗map] bl ↦ B ∈ X.t.bobjs, objOwn … (bl ∈ X.liveB) (.bkt B)`;
  **`heapOK`** ends with batch 20 item 5: `∀ bl B, X.t.bs !! bl = some B → bl = X.rl ∨
  (X.handles !! bl).isSome` (every bucket the root or a handle's: its `FillPercent` is
  `rootFill`'s or `fills`'; the registry clause is now `.2.2.2.2.1`). `WX.rebase` re-bases
  `dead` (`NRec.unview`) and `deadB` (`BRec.unview`); `WEntry.unview`/`NRec.unview` moved here
  from U4's `Mmap/Rebase` (and U9c's duplicate in `Spill/AllocDeref` deleted).
- **Internal specs** (`bl ∈ X.live` of a bucket → `X.liveB`): `Bucket__free`, `Bucket__node`,
  `Bucket__pageNode_w`, `node__childAt`, `node__nextSibling`, `node__prevSibling`.
- **Heap lemmas** (unit files adapted mechanically, owners stopped): `Rebalance/Objs`
  (`objs_bkt` → `bobjs_bkt T bl B hb : T.bobjs !! bl = some B`, no `objsDisj`; `objs_node`;
  `objs_other` takes only `B.ns !! k = none` and gives `T.deadObjs !! k`; `objs_setNodeT` is now
  `T.objs.insert n (.node bl r')`, with `bobjs_setNodeT`), `Rebalance/Heap` (new
  `wtxHeap_bkt_obj_acc`, `heapOK_setNode`; `wtxHeap_setNode_bkt`/`wtxHeap_free_acc` give the
  bucket at `decide (bl ∈ X.liveB)`), `Rebalance/HeapRbl` (`wtxHeap_reshape` takes a node list
  and a bucket list; `heapOK_of` takes `X'.handles = X.handles`; `objs_agree` nodes only,
  `bobjs_agree` new; `wtxHeap_setBkt_acc`/`_live_acc`/`wtxHeap_setNode_acc` give the bucket at
  `liveB`), `Rebalance/HeapRblKill`, `RblXSObjs` (`objs_isSome` nodes only;
  `objs_isSome_mono` without the bucket hypothesis; `bobjs_isSome_mono` new), `RblXSKill`,
  `RblXSSim`, `RblXSMat` (WIP, not imported), `RblXSDefs` (`WX.kill`'s dead `(bl, rn)`), `BktRbl`,
  `Write/Heap` (`objs_isSome_bkt` gone; `objs_none` gives only the nodes' clause),
  `Write/{CurNode,CurNodeH,MatOK}`, `Txn/Heap` (`objs_setBkt` is now `= X.t.objs`;
  `bobjs_setBkt`; `wtxHeap_bkt_acc` takes `bl ∈ X.liveB`), `Mmap/{Rebase,AllocBase,TxAlloc}`
  (`wtxW_txFields_acc`'s premise ends `(T.dead, T.deadB) = (X.t.dead, X.t.deadB)`, so `⟨rfl, rfl,
  rfl⟩` still proves it), `Spill/{DerefModel,DerefRel,DerefWOK,DerefHeap,AllocDeref,
  BucketDeref,NodeDeref}` (`DerefHeap.wtxW_open`'s premise ends `(X'.nloc, X'.t.t) = (X.nloc,
  X.t.t)`, a pre-existing gap since batch 16's `managed` fact), `Bucket__dereference`,
  `Bucket__pageNode_w`, `Bucket__rebalance`, `node__rebalance`.
- **Batch 27's `AllocDeref` lemmas** rechecked against the new `objsDisj`: they hold
  unchanged (`liveFresh_rebase` uses `objs_node`, which needs only the new clause).
- **`Rebalance/Base.srcOwn_acc`** takes `(hb : 0 < v.base.addr)` (batch 21: it was the
  module that did not build since `feed4d07da`, blocking every importer). The breakage moves to
  its callers, the proofs `node__put` (line 59), `node__del` (48; also its batch-28 line 187),
  `node__childIndex` (74), whose internal specs give no positive base: they need
  `0 < v.base.addr` as a premise of `node.put`/`node.del`/`node.childIndex.spec` (their callers
  have it from `mapFields`), **open, for the coordinator**.

Still failing, not batch 14: `node__rebalance` (U8b's WIP: `wp_auto` at 369, batch 28's
`node.del` post at 467), `Rebalance/RblXSMat` (U8b's WIP, batch 20's `nodeAdded` clauses at 101).

## Batch 20 item 9: the shared `matReady` lemma (2026-11-04)

`Inv/MatReady.lean` (new): `viewWF_page_ready` (a view page's header id, non-empty, leaf or
branch, `pageReadable`, `pageElemsIn`, from `viewWF` through `treeHas_treeWF`), `matReady_view`
(pure: a bucket with a root page, a view page not in `pm`, its bytes in `(0, maxAddr]`),
`wtxW_page_bounds` and **`wtxW_matReady`** (`wtxW … X ⊢ ⌜matReady X B pgid⌝` for `B.ib.root' ≠ 0`,
`viewWF X.v`, `X.v.pages !! pgid.toNat = some pg`, `X.t.pm !! pgid = none`). U8b's
`Rebalance/NodeRblSteps.rblX_matReady` (a `sorry`) can use it.

## Shared-statement fixes, batch 29 (maintainer 3's queue, 2026-11-04; decided by the coordinator)

- **Batch 22's move**: the shared `wOK_nodeAdded` is `Write/MatGrow`'s `Write.wOK_nodeAdded`
  (proved: U7b's `wOK_nodeAdded'` with its three premises from `nodeAdded`'s `hrvs` and child-case
  `capOwn` clauses, batch 20, and `bktClean`'s `inlineBnd`, batch 22); `Model/WOps`' `sorry` is
  deleted. `wtxData_matGrow` moved from `Write/Mat` to `Write/MatGrow` after it; `Write/CurNode`
  imports `Write/MatGrow`.
- **`dbFixed`'s page pool** has `⌜f ≠ func.nil⌝` (`Open` sets `New`; U11 proves it):
  `Mmap/Infra`'s `pagePoolNew_holds` discharges U4c's `pagePoolNew`.
- **`Tx.allocate.spec` is U4c's `Tx.allocate.spec'`**: premises `X.t.mv.txid' = w.wtxid` and
  `X.t.mv.pgid'.toNat * 4096 ≤ mapLen w.ms` (the high-water mark's pages inside the mapping, as a
  premise); the success post keeps the bound (`X'.t.mv.pgid'.toNat * 4096 ≤ mapLen w'.ms`) and
  says `w' = w.withFl w'.fl ∨ wdbRemap w w'` (the false `X'.v = X.v → w' = w.withFl w'.fl` is
  gone). `Proof/Tx__allocate`'s `wp_proof` is U4c's `wp_proof'` (callee specs as hypotheses).
  **`Bucket.spill.spec`** takes the bound as a premise and gives it in its success post (for
  `commitFreelist`'s `allocate`); `X.t.mv.txid' = w.wtxid` is derivable inside spill (`txClean`'s
  `X.v.txid + 1 = X.t.mv.txid'.toNat`, `wdbW`'s `v = View.ofC _ w.C`, `wdbOK`'s
  `C.txid + 1 < 2^64`). **Open for U10**: `Commit` must give spill the bound at its start
  (`C.hwm * 4096 ≤ mapLen`); nothing holds it yet. Proposal: a `wdbOK` clause `∀ b l, w.ms =
  some (b, l) → w.C.hwm * 4096 ≤ l` (bbolt maps at least the file at `Open`, and `DB.allocate`
  remaps whenever the mark passes the mapping), maintained by `Open`, the publish (from spill's
  post), remaps; not applied (it touches U3/U4/U5's `wdbOK` constructions).
- **D (U6c)**: `Bucket.ForEachBucket_r.spec` and `Bucket.Bucket_r.spec` are over `rBktP v tx b dq
  bv ibp pp` (`Read/RCtx`; `ibp pp` universally quantified, the same in pre and post; the opened
  child of `Bucket_r` stays `rBkt`). `Proof/Bucket__ForEachBucket_r`'s `wp_proof` is U6c's
  `ForEachBucket_rP.wp_proof`; `Bucket__Bucket_r`'s proof adapted (no `rBkt_eq` unpacking).

## Shared-statement fixes, batch 30 (maintainer 4's queue, 2026-11-04; decided by the coordinator)

- **1. A positive view base for the three node specs**: `node.put.spec`, `node.del.spec`,
  `node.childIndex.spec` take `0 < v.base.addr` as their last premise (after the `Src.stale`
  ones): `Rebalance/Base.srcOwn_acc` needs it since `d77c9ad08a`. Callers get it from
  `mapFields`; for a writer, `Inv/WtxBase.wtxW_base_pos` (new module, so that `Inv/Ctx`'s
  importers do not rebuild): `wtxW … X ⊢ ⌜0 < X.v.base.addr⌝`. Proofs adapted mechanically:
  `node__put`, `node__del` (also batch 28's line 187: one existential, `List.eraseIdx_eq_take_drop_succ`),
  `node__childIndex`, `node__nextSibling`, `node__prevSibling` (all build). **Open for U8b**:
  `node__rebalance.lean:463`'s `wp_apply hDel …` needs the premise (`wtxW_base_pos`, or
  `mapFields_base_nonnull` of the opened `wtxW`), not edited (U8b's WIP).

- **2. The high-water mark inside the mapping** (batch 29's proposal, applied): `wdbOK` ends
  `… ∧ w.C.hwm < 2 ^ 64 ∧ (∀ b l, w.ms = some (b, l) → w.C.hwm * 4096 ≤ l) ∧ …` (items 2 and 4's
  three clauses at the end, so `obtain ⟨…, htx, hhwm⟩` still binds and `refine ⟨…, htx, hhwm⟩`
  passes them on). U10's `Commit` gives `Bucket.spill`'s premise `X.t.mv.pgid'.toNat * 4096 ≤
  mapLen w.ms` from it (`X.t.mv.pgid' = C.hwm` at the start). Establishing it: `wdbOK` lives in
  `rwR` (the invariant), so `beginRWTx` (U5) takes it from there; its producers are `Open` (U11:
  the mapping is at least the file, `hwm·4096 ≤ size`), the publish (U10: spill's post bound),
  `DB.mmap`'s remap (U4, a `sorry`: the new length is at least the file's size), `DB.grow` (ms and
  `C` unchanged), the freelist steps (`wdbOK_alloc`, `wdbOK_free`: adapted, `ms`/`C` unchanged).
- **4. C(4), for `DB.grow`**: `wdbOK` gains `(∀ b l, w.ms = some (b, l) → l ≤ 0x1000000 →
  w.m.size ≤ l)` (`growSize` truncates to the mapping's length when it is at most `AllocSize`,
  `dbFixed`'s `0x1000000`; `Truncate`'s spec needs `m.size ≤ sz`: every mapping is at least the
  file when made, and a grow past it happens only above `AllocSize`; stated over `ms = some` as an
  unmapped writer has `mapLen = 0`) and `(∀ s, s ∈ treeSlots w.C ∨ s ∈ pendSlots w.fl → s <
  w.C.hwm)` (with `hwm·4096 ≤ size` and `W`'s characterization, every slot from the file's end on is
  a `W` slot, so `Truncate`'s `mcellsAny` of `[size, len)` comes from `wCells`: no store lemma
  needed; `wdbOK_free` proves it for the freed run from `treeSlots`). **`wdbGrown`** keeps `wb s` only
  for `4096 · (s + 1) ≤ w.m.size` (`Truncate` zeroes the partial slot's tail): `∀ s ∈ w.W, s ∈ w'.W
  ∧ (4096 * (s + 1) ≤ w.m.size → w'.wb s = w.wb s)`. Its only user is `DB.grow.spec` (proof a
  `sorry`, U4) and its caller `Commit` (U10). Built: `Rebalance/Free`, `Mmap/AllocBase`,
  `node__free`, `Mmap/Alloc`. **Producers to prove** (all `sorry`s today): `Open` (U11), the
  publish in `Commit` (U10: spill's pending frees are of committed pages, `< hwm`), `DB.mmap`
  (U4), `beginRWTx`'s release of pending pages (U5: free/pending ids are below `hwm` by `flBelow`).

- **3. C(1), bbolt's error variables' package facts**: `PkgInit`'s `bboltErrorsVars` is over the
  new `bboltErrVar a` (`∃ e : GoInterfaceOk, a ↦□ GoInterface.ok e ∗ ⌜IsPointerError e⌝ ∗
  fmtErrorOk (.ok e)`, a `def` with its own `Persistent` instance: the instance search through
  nineteen inline clauses exceeds its size), one per variable but `ErrBucketNotFound` (unchanged).
  `errorString_fmtErrorOk` moved from `Mmap/MmapSize` to the new `Proof/errors/ErrorStringOk`
  (namespace `EtcdGrove`, over `errors.Assumptions`), which `etc/gen-init.py`'s `errors` entry
  imports; the generated `errors/Init.lean` and root `Init.lean` regenerated (their patterns and
  unfolds updated in the script). `Meta__Validate`'s pattern adapted (the `≠ nil` facts by `nofun`).
  New in `Mmap/Infra`: **`errMaxSizeOk_holds`** (U4c's `errMaxSizeOk` discharged),
  `bboltErrVar_fmtErrorOk`, and **`beginErrs_fmtErrorOk`** (`isPkgInit errors ∗ (ErrDatabaseNotOpen
  ↦□ err ∨ ErrInvalidMapping ↦□ err ∨ ErrDatabaseReadOnly ↦□ err) ⊢ fmtErrorOk err`): **for U5**,
  `Txn/Begin.beginErr_fmtErrorOk`'s `sorry` is `beginErrs_fmtErrorOk` after dropping `beginErr`'s
  `⌜err ≠ nil⌝` (not edited: U5 is editing `Txn/Begin`). Built: both `Init`s, `Mmap/{Infra,
  MmapSize,Alloc}`, `Meta__Validate`, `Txn/Begin`.

- **5. E: `store_cells_agree` proved** (`Inv/Store`): `wp_atomic` opens `pagesN N` around `e`;
  the halves of `cur`, `fl`, `byt` agree (`σ.C = C`, `σ.fl = fl`, `W` the store's witness, whose
  facts give `bs := σ.bytes`); each store slot's cells are read against its `osSlot` bytes
  (private `cellsR_agree_bytes`: `osCell_agree` byte by byte, as the bboltfs example's
  `cellsR_agree`, giving `bytesPointsto` at a half; `slots_agree_bytes` over the slots, of `4096`
  bytes by `storeOK`, inside the mapping by `hl`); the user's WP runs at `E \ pagesN N` and the
  invariant closes, unchanged, in its postcondition (`wp_wand`). The helpers are `private` (no new
  public declarations: `Inv/Store`'s importers do not rebuild).

- **7. (U8c) `leafInl` below `Rebalance/RblMat`**: `Write/MatOK`'s pure `bound` section
  (`leafBnd`, `bvBnd`, `nestBnd`, `topPg`, `nestPg`, `topPg_of`, `nestPg_of`, `leaf_ne_branch`,
  `treeHas_leafBnd`, `viewWF_leafBnd`, `leafInl`, `treeHas_leafInl`, `viewWF_leafInl`) moved
  unchanged (namespace `Write`) to the new `Write/Bound` (imports `Model/Wtx`, `Model/Mvcc` only);
  `Write/MatOK` imports it publicly (a pure move: every name as before). `RblMat.lean:416`'s
  `sorry` closes with `hinl := Write.viewWF_leafInl X.v hv _ pg hpg` once `RblMat` imports
  `Write/Bound` (U8c's).

- **6. Interfaces: not regenerated.** `etc/gen-interface.py` needs every bbolt module built; failing
  (owners' WIP, not batch 30's): `node__rebalance` (U8d), `DB__Begin` (U5), `Cursor__seek_w` (U6d),
  `Tx__forEachPage_r`, earlier `DB__beginRWTx`/`Mmap/RemapBody` (U5c/U4d). Stale interface files:
  `interface/Spec/go_etcd_io/bbolt/Api.txt` and `interface/Proof/go_etcd_io/bbolt/{DB__Begin,
  DB__Begin_err,DB__Info,Tx__DB}.txt` (batch 21), `{Tx__allocate,Bucket__spill,Bucket__Bucket_r,
  Bucket__ForEachBucket_r}.txt` (batch 29), `{DB__grow,Bucket__spill,Bucket__write,Bucket__node,
  node__write,node__put,node__del,node__childIndex,node__childAt,node__nextSibling,
  node__prevSibling}.txt` (batches 30-31), `internal/common/WriteInodeToPage.txt` (batch 30).

## Shared-statement fixes, batches 30 (U9d's part), 31, 32 (maintainer 4, 2026-11-04; decided by the coordinator)

- **30.1 `txClean`'s second clause is `(X.t.pm = ∅ ∧ X.t.bufs = ∅ ∧ leafShape X)`** (no buffers
  before spill allocates; `WX.bufPages` reads all of `bufs`). Nested beside `pm` so that the
  six-clause patterns of `txClean` stand (a user of `pm = ∅` takes `.1`).
- **30.2 `leafShape X`** (`Model/Wtx`, in `txClean`, so in `wOK` and `wOKR`): every leaf node's
  entries are bucket entries (`isBktFlag`) iff its bucket is the root bucket (nesting depth 2).
  Kept: by dereferencing (`Spill/DerefWOK.leafShape_step`, proved; `txClean_step` adapted), by a
  materialization (`Write/MatOK.leafShape_matX`, proved, over a new premise `hshape` of
  `wOK_matX`: the new node's entries; **its two callers in `wOK_nodeAdded'` pass `sorry`, owner
  U7d**: from the view page's `rootShape`), initially (`Txn/WInit`: no node). **Open, owner U8d**:
  `Rebalance/RblX.rebalOK_of_rbl` passes `sorry` for `bufs = ∅` and `leafShape` (`rblX` has to
  carry them; `rblRel` has `bufs` equal to the start's); `RblXSteps.rblX_init` takes `pm`'s `.1`.
  Still to prove by their owners: `Put` (plain entries in a non-root bucket), `CreateBucket` (a
  bucket entry in the root), `DeleteBucket`, `Delete`.
- **30.3 `Bucket.spill.spec`** takes `flViewU X w.fl` and its success post gives `flViewU X' w'.fl`.
- **30.4 Per-index fractions**: `WriteInodeToPage.spec`, `node.write.spec`, `Bucket.write.spec` read
  inode `k`'s key at `qk k` and value at `qv k` (`qk qv : Nat → DFrac`, an indexed `[∗list] k ↦
  it;m ∈ ins;ms`), as old `node.write.xspec`: a spilled node mixes view keys and persistent heap
  keys. Proofs adapted (U1's `WriteInodeToPage`, U9a's `node.write`, U9b's `Bucket.write`); no
  other callers yet.
- **31.1 `Bucket.node.spec`** is U7d's `spec'`: premise `B.nm !! pgid = none → B.ib.root' ≠ W64 0 →
  B.bv.page' = null` (`bktClean`'s); `Proof/Bucket__node`'s `wp_proof` is U7d's `wp_proof'` (callee
  specs as hypotheses), the `spec'`/stub gone. Cascade: **`node.childAt.spec`,
  `node.nextSibling.spec`, `node.prevSibling.spec`** take `B.ib.root' ≠ W64 0 → B.bv.page' = null`
  (their last premise); `node__childAt`, `node__nextSibling`, `node__prevSibling`, `Cursor__node`
  (both calls: `hcB.2.2.2.2.2.1`, the second through `curSt`'s `page'` equality) adapted. **Open,
  owner U8d**: `node__rebalance`'s calls of `hNode`, `hNext`, `hPrev` pass the premise (from
  `bktClean`).
- **31.2 `wOK_leaves_fuel`**: `Model/LTree`'s stub deleted; the shared lemma is `Write/Fuel`'s
  `Write.wOK_leaves_fuel'` (proved; `Write/Fuel` imports `Model/LTree`, so it cannot move there).
- **32 (U9e) `wdbOK` ends `… ∧ (∀ x ∈ w.fl.free, x.toNat < w.C.hwm)`** (`storeOK`'s `flBelow`;
  `node.spill`'s allocated pages below `tx.meta.Pgid()`). `wdbOK_free` (free unchanged) and
  `wdbOK_alloc` (a filter of the free ids) adapted; producers: `beginRWTx` (U5), `Rollback`'s
  (U5/U10), `DB.mmap` (U4, `sorry`).

## Shared-statement fixes, batch 33 (U6d's findings, maintainer 4, 2026-11-04; decided by the coordinator)

- **1. `Cursor.seek_w.spec`** is U6d's `spec'` but for `inlSrcOK` (item 2): premise `pmFresh X`, the
  returned slices' sources `leafSrc X bl w.ks`/`w.vs`. `pmFresh`, `inlSrcOK`, `leafSrc` moved from
  `Read/WPos` to `Model/WOps` (the spec's vocabulary). `Proof/Cursor__seek_w`'s `wp_proof` is
  U6d's `wp_proof'`, with `inlSrcOK` from `inlSrcOK_of_bktLocalOK`. **Callers that must supply
  `pmFresh X`** (none calls `seek_w` yet): U7e's writes (`Put`, `Delete`, `CreateBucket`,
  `DeleteBucket`), U9g's `Bucket.spill` (if it searches), `Bucket.Bucket_w`/`ForEachBucket_w`'s
  proofs (item 3); from `wOK`/`wOKR`'s `txClean` `pm = ∅` (`X.t.pm = ∅ → pmFresh X`: the lookup
  is `none`).
- **2. `bktClean`'s inline clause** is `(isrc = .view ∧ pst = .view) ∨ (isrc = .own discard ∧ pst =
  .none)` (as `bktOpened`), so `inlSrcOK X bl` follows from `bktLocalOK X bl`
  (`Model/WOps.inlSrcOK_of_bktLocalOK`, proved: `bktLocalOK`'s `bktClean`'s first clause) and is
  not a premise. Adapted: `Rebalance/RblFrame`'s `bktSim` gains `B'.pst = B.pst` (after `isrc`;
  `bktSim_set`, `bktSim_trans`, `pagePosAt_sim`, `bktClean_sim`, `rblAcyc_sim`, `rblHt_sim`, and
  `RblXSSim`'s projections shifted), `Spill/DerefWOK1.bktClean_step` (`bktStep_fields`' `pst`).
  Producers of `bktClean` for an inline bucket (`CreateBucket`, `Bucket.Bucket_w`'s open) give the
  pair.
- **3. `Bucket.Bucket_w.spec`, `Bucket.ForEachBucket_w.spec`** take `pmFresh X` (after
  `bktLocalOK`); their proofs are `sorry` stubs.
- **4. Shared stubs deleted, the lemmas are U6d's**: `ltree_leaf_of_T` (`Model/LTree`) is
  `Read/LeafOfT.ltree_leaf_of_T'` (premise: the leaf is one of the bucket's walk); `rStackAt_prev`
  (`Model/Cursor`) is `Read/Prev.rStackAt_prev'` (over `sPrev`/`sStartBelow`); `lRoutes_found`,
  `lRoutes_leafFor` (`Model/WOps`) are `Read/LRoutes.lRoutes_found'`, `Read/LeafFor.lRoutes_leafFor'`;
  `bktEnts_treeEntries` (`Model/TreeData`) is `Read/TreeEnts.bktEnts_treeEntries'`. All proved; the
  `Read/` modules import the `Model/` ones, so they stay there; no caller used the stubs.
- **5. Interfaces not regenerated**: not every bbolt module builds. Blockers (owners' WIP):
  `node__rebalance` (U8d), `DB__Begin_err` (U5), `Write/Walk` (untracked, U7e). Stale files as
  listed under batch 30 item 6, plus `Cursor__seek_w.txt`, `Bucket__Bucket_w.txt`,
  `Bucket__ForEachBucket_w.txt`.

## Shared-statement fixes, batches 34-36 (maintainer 5, 2026-11-04; decided by the coordinator)

- **34.1 `wtxEnd`** (`Inv/Ctx`) holds the writer side's half of the closed flag
  (`ghostVar K.B.cls ½ false`, after `rwlock`'s token: `rwR`'s idle branch takes it back) and its
  pure part is `wdbOK w ∧ X.t.t.writable' = true ∧ (X.t.bs !! X.rl).isSome` (`close` branches on
  `writable` and writes `tx.root` whole). **`Tx.close_w.spec`**'s premise on `ws` adds `wl = true →
  v = X.v` (`store_wclose` takes the lent view's cells, `wtxW`'s at `X.v`): the coordinator's
  `ws.1 = some X.v` weakened to the lent case, since after a failed remap (`wl = false`) the parked
  view need not be the re-based `X.v`. `Proof/Tx__close_w`'s `wp_proof` is U5c's (callee specs as
  hypotheses), `spec'` gone; `Tx__Rollback` adapted.
- **34.2 `txExcl`'s writer branch** (`Inv/Txs`) := `ownMutex rwlock ∗ cls ½ false ∗ ∃ w extra,
  wdbLive … (wLive X.v w.C) w ∗ txShape r.n.pg X extra ∗ ⌜wdbOK w ∧ w.ms = some (X.v.base, mapLen
  w.ms) ∧ X.v = View.ofC X.v.base w.C ∧ flViewU X w.fl⌝` (`wdbW`'s facts inline: `txExcl` takes
  `B p sp t0`, not a `BC`). `wLive` moved from `Inv/Ctx` to `Inv/Txs`. `Tx__Rollback`'s
  `txExclWGap_holds` is proved, so `Tx.Rollback.wp_proof` rests on no gap. `DB__beginRWTx` adapted
  (`rwR`'s `cls` half into `txExcl`; `wdb_release`'s `wdbOK`).
- **34.3 `store_release`**'s post ends `⌜∀ s ∈ S, (bs s).length = 4096⌝` (the released slots were
  store slots: `storeOK`'s slot clause). `Txn/WRelease.store_release_len` is `store_release`.
- **34.4 `lCovers`/`coverW .bkt`** (`Model/WOps`) cover overflow slots: the new `bucketCovers P v s
  := ∃ id pg, bucketHas P v id ∧ P !! id = some pg ∧ id ≤ s ∧ s < id + (1 + pageOverflow pg)` in
  place of `bucketHas X.v.pages v s` (same destructuring shape: the last component is now
  `bucketCovers`). Adapted: `Txn/WInit.covU_wx0` (two pages covering a slot are one, `pagesDisjoint`).
  `Rebalance/RblX*` and `Write/FlView` build unchanged. `Txn/WInit.flViewU_wx0`'s cover `sorry`
  (U5c's "false as stated") is now open, not false (owner U5d).
- **34.6 `wtxHeap_fractional`** (`Inv/WtxHeap`) proved: U5c's `Txn/Frac` instances moved in as
  private instances; `Txn/Frac` deleted (nothing imported it). `notes/perennial-changes.md`: `ownMap`
  has no `DFractional` instance.
- **35.1 `Bucket.free.spec`** is U7e's `spec'`: tree case premises `∀ pid ∈ X.positions bl,
  X.t.pm !! pid = none` (no `resolve` guard), `canFreeAll`, `rtOK X bl` and `X.t.mv.txid' =
  w.wtxid`. `rtOK` stays in U8's pure `Rebalance/RTreeX`, which the spec imports. No caller yet:
  `DeleteBucket` gets `rtOK` from `rtOK_init` (`wOK`, `viewWF`), `X.t.mv.txid' = w.wtxid` from
  `txClean`'s txid clause, `wdbW`'s view and `wdbOK`'s no-wrap (as batch 29 for spill), `pm = ∅`
  from `txClean`; `Bucket.spill`'s inlineable children: `rtOK` from rebalance's post (`rebalOK`
  gives `wOKR`, not `wOK`: `rtOK_init` takes `wOK`, so spill needs a `wOKR` form, owner U9),
  `pm` lookups are `none` only before spill allocates (a child freed after an earlier sibling's
  spill allocated a buffer: check, owner U9). U7f proves `wp_proof'` (one `sorry`, the callback);
  `Proof/Bucket__free`'s old `wp_proof` stub (now over the same statement) goes then.
- **35.2 `posShape X`** (`Model/Wtx`): every view leaf page under a bucket's page position
  (`posRoot B c`, `ownHas X.v.pages c p`) has `leafFlags pg i % 2 = bucketLeafFlag ↔ bl = X.rl`;
  the fourth component of `txClean`'s second clause (`⟨hpm, hbuf, hsh, hps⟩`). Kept by
  dereferencing (`Spill/DerefWOK.posShape_step`, proved via `posRoot_bktStep`). `sorry`s with owners:
  `Txn/WInit` (initial records, from `rootShape`: U5d), `Rebalance/RblX.rebalOK_of_rbl` (U8d, beside
  batch 30's two), `Write/MatOK.wOK_matX` (materialization: U7f; its two `hshape` `sorry`s in
  `wOK_nodeAdded'` then follow from `hps`). Still to prove by their owners: `Bucket.Bucket_w`'s
  open (U6e), spill (U9), `CreateBucket`/`DeleteBucket` (U7).

- **34.5 `lg != discardLogger`**: bbolt's root package facts (`PkgInit.bboltRootInit`, through
  `etc/gen-init.py`'s `SPECIAL['go_etcd_io.bbolt']` finish; `Init.lean` regenerated) add `∃ l,
  globalAddr discardLogger ↦□ interface.mkOk (*nopLogger) #l` (`bboltRootInit_discard`;
  `_goos`/`_goarch` adapted). `dbFixed` (`Inv/Bolt`) gains a **last** clause `∃ lg, db.logger ↦□ lg ∗
  ⌜logPtrTyped lg⌝` (a pointer-typed dynamic value is a location; last, so that the patterns ending
  in `-` stand; `dbFixed_logPtrTyped` reads it against the caller's logger field) in place of
  changing `dbLogger` (whose users pass it as a `boltLogger`). `DB__Begin_err.wp_logger_ne_discard`
  is proved (takes `logPtrTyped lg`). **Open for U11**: `Open` must establish `logPtrTyped` of the
  logger it stores; for the option's logger the frozen `Open` spec gives only `boltLogger
  o.logger`, which does not say a `*T`-typed value is a location (the model's interface values are
  untyped pairs): it needs a premise in `Open`'s public spec (user approval) or a Perennial typing
  fact for interface values. `discardLogger`'s own case follows from `bboltRootInit_discard`.
  `Open`'s own comparison, if any, uses the same lemma.
- **36.1 `os.File.ReadAt.specRacyLt`** (`Spec/os/File__ReadAt.lean`, proved in
  `Proof/os/File__ReadAt.lean` from the model, no trust change): `specRacy` with `io.EOF` only for
  `n < len(b)`, and the `*PathError` case `fmtErrorOk` (post: the exactness facts pure, then
  `⌜nil ∨ eof-case⌝ ∨ ∃ pe, ⌜err = *PathError pe⌝ ∗ fmtErrorOk err`). Not U11's
  `fmtErrorOkOrNil err` uniformly: `io.EOF`'s `fmtErrorOk` needs `io`'s package facts, which the spec
  does not take, and a disjunct `err = eof ∨ fmtErrorOkOrNil err` would not let a caller refute the
  `eof` case in the `*PathError` branch. `specRacy` is kept (bboltfs uses it) as a corollary
  (`wp_proofRacy` from `wp_proofRacyLt`); kept beside rather than strengthened in place so that
  bboltfs' proofs are unchanged. U11's `Open/ReadHeld` uses it: its own `specRacyLt` deleted,
  `wp_held` adapted (same statement).
- **36.2 `bboltErrVar`**'s pure part is `IsPointerError e ∧ e.ty = *errorString` (`errors/Init`
  regenerated, `gen-init.py`'s finish `⟨⟨_, _, rfl, rfl⟩, rfl⟩`); `Mmap/Infra.errMaxSizeOk_holds`
  adapted; **`Mmap/Infra.errInvalid_errorString`** is U11's `Open/PageSize.errInvalidStr` (same
  statement), proved: `DB.getPageSize.wp_proof_own`'s `hEI` can be discharged by it.

- **34.7 Interfaces: not regenerated.** Every tracked bbolt module builds (full build after
  batches 34-36) but `node__rebalance` (U8d's uncommitted WIP: errors only in its new lines
  1300-1492) and so `Bucket__rebalance`; `etc/gen-interface.py etc/api/bbolt.txt` needs them. Stale
  interface files: those of batches 21, 29-33 (above), plus `Tx__close_w.txt`, `Bucket__free.txt`,
  `DB__Begin_err.txt`, and `PkgInit`'s/`Inv/Bolt`'s consumers' (`dbFixed`, `bboltRootInit`).

## Shared-statement fixes, batches 37-38 (maintainer 6, 2026-11-04; decided by the coordinator)

Batch 37 (items 1-8, 11-13, 15-19 applied; 9, 10, 3, 14, 20 below):
- **1, 2, 5. `wdbOK` ends `… ∧ w.m.size < 2 ^ 63 ∧ (∀ b l, w.ms = some (b, l) → w.m.size ≤ l ∨
  w.m.size % 4096 = 0) ∧ (∀ s ∈ w.W, 4096 * (s + 1) ≤ w.m.size → (w.wb s).length = 4096)`**
  (`Inv/Locks`). Producers adapted: `wdbOK_free` (unchanged: passes the tail), `wdbOK_alloc`,
  `wdbOK_rolledBack`/`wdbOK_released` (take `hbs`, the joined slots' page lengths, in place of U5d's
  `hwb`, now derived: `Txn/WJoin.wb_header w hok`), `wdbOK_remap`, `wdbOK_lost`. U5d's two
  `fun f hf => sorry` (`DB__beginRWTx`, `Tx__Rollback`) are gone. `Mmap/RemapGaps`' gaps 1, 2
  (`wdbOK_size_lt`, `wdbOK_size_page`) are projections. **To prove**: `Open/CoreFacts.wdbOK_open`
  (U11), the publish (U10), `DB.grow` (U4: keeps the page clause by its new `sz % 4096` premise).
- **4. `isBoltCoreP`'s pure part is `t0 < 2 ^ 62 ∧ db ≠ null ∧ (↑N : CoPset) ## ↑osN`** (users'
  `.2` became `.2.1`). Gap 4 (`core_osN_disj`) proved. `Open/Core.open_core` must add it (U11).
- **6. `store_rollback`'s post ends `⌜∀ s ∈ S, (bs s).length = 4096⌝`**; `Txn/WRoll.store_rollback_len`
  deleted, `Tx__Rollback` uses `store_rollback`.
- **7. `wdbCoreG` pins `db.ops.writeAt`**: no `∃ wa`; its half is `methods (PointerType os.File.ty)
  "WriteAt" #w.f`. `%wa` binders removed (Bucket__free, node__free, Tx__close_w, Tx__Rollback,
  DB__beginRWTx, Mmap/*, Spill/NodeSpillPiecesFree); `wdbLost_intro`, `wdbW_remap_intro`,
  `remap_post` lost their `wa` argument.
- **8. `DB.grow.spec`** takes `sint.Z sz + 0x1000000 < 2 ^ 63` and `sint.Z sz % 4096 = 0` (the second
  for item 2: above `AllocSize` the file grows to `sz + AllocSize`, whole pages). Proof `sorry` (U4).
- **11. `bktClean` ends `… ∧ posNodeFree v B ∧ (∀ n c, B.bm !! n = some c → c ≠ null)`**;
  `Bucket.Bucket_w.spec` takes `X.t.t.writable' = true` (after `pmFresh X`); U6e's `wp_proof'` is the
  `wp_proof` (callee specs as hypotheses; the non-nil premise derived from `bktLocalOK`).
  `WOpen.bktClean_bm` takes the new map's non-nil fact, `wOK_XO`/`wOK_bktOpened` take `c ≠ null`.
- **12. `bvalOK`** gains `(inBucketRoot v ≠ 0 → ∀ pg, bktLeafPg pages v pg → ∀ j < pageCount pg,
  leafFlags pg j % 2 = 0 ∧ 0 < leafKsize pg j ∧ leafKsize pg j + leafVsize pg j ≤ bboltEntryMax)`
  (with batch 38's S1 bounds). `Bucket__Bucket_w` now uses it for the open's plainness (the
  `WOpen.leafBkt_nest_plain` call is gone; that `sorry` lemma is unused). **Open producers**
  (`sorry`, the view page's `rootShape` + `viewUnique`): `Write/MatOK` (U7, materialization),
  `Rebalance/RblMat` (U8), `Read/WOpenOK` (U6e, the open's page entry).
- **13. `rootNotInline X`** (`Model/Wtx`) is the 5th component of `txClean`'s second clause
  (`⟨pm, bufs, leafShape, posShape, rootNotInline⟩`). Producers: `Txn/WInit` (proved),
  `Write/MatOK.wOK_matX` (proved), `RblX.rebalOK_of_rbl` (proved; new premise `rootNotInline X0`),
  `WOpenWOK.wOK_XO` (proved). `Write/MatOK`'s `hnr` sorry closed by it. Spill's `DerefWOK`
  (`posShape_step` arguments) routed to the spill unit.
- **15. `Inv/Tx.boltTxDef_fractional` proved** (U5d's `Txn/TxFrac` moved in, helpers private; the
  module deleted).
- **16. `spillPre` and `rebalOK`** gain `(∀ bl, X.t.bs !! bl ≠ none → rtOK X bl)` (before the coverage
  clause / before the frees). `RTree`, its walks, `ltIs` and `rtOK` moved to the new `Model/RTree`
  (from `Rebalance/RTree`, `RTreeX`; same names). `rebalOK_of_rbl` gives it from `rblX`.
- **17. Entry bounds**: `entriesBounded` is `∀ w ∈ r.ws, 0 < w.key.length ∧ w.key.length +
  w.value.length ≤ bboltEntryMax` (every entry); `rootShape` (`Model/Tree`, `fileHolds`' clause,
  definition and docstring) bounds the root bucket's leaf entries (`… ∧ 0 < leafKsize ∧ leafKsize +
  leafVsize ≤ bboltEntryMax ∧ ∀ bpg …`). Open (`sorry`): `Write/MatOK.newNodeBnd` and
  `Rebalance/RblXSMat` (branch keys, root-bucket entries: from exact branch keys and `rootShape`,
  owners U7/U8); spill: `treeOK`'s new clause for the new tree, `DerefWOK.entriesBounded_step`.
- **18. `Spill/UTree.spG X txid ml fl`** (new freelist argument) ends with `(∀ id, (X.t.bufs !!
  id).isSome → id.toNat < X.t.mv.pgid'.toNat ∧ id ∉ fl.free ∧ X.v.pages !! id.toNat = none)`.
- **19. `metaSummed`** moved to `Model/Meta` with `metaSum_checksum`, `metaValid_with`,
  `metaValid_metaSummed` (stated over the field value: the kernel must not unfold `metaSum`).
- **20. `Bucket.free`'s premise stands** (`∀ pid ∈ X.positions bl, X.t.pm !! pid = none`: the child's
  positions only). An inlineable child's positions are view pages (or `0`); spill's buffers are no
  view pages (item 18's last conjunct), so spill discharges it after earlier siblings allocated.

Batch 38:
- **0.** the bktClean breakage fixed in RTreeX, WPos, LRoutes, DataBnd, DataReach, WOpenOK, RblMat,
  RblFrame, RblCol, RblRm, RblMg3. `Inv/Bolt.discardLogger_boltLogger` stub deleted (proved with the
  package's `Assumptions` as `Open/Logger.discardLogger_boltLogger'`). `Proof/os/WriteChunks`'
  `osBytes_split3` renamed `osBytes_split3_range` (clashed with `CrashOps`').
- **2. `node.put.spec`** takes `dqt` for `bl.[Bucket, "tx"]` and `dqm` for `tx.[Tx, "meta"]`/`mp`.
- **3 (S1). `posShape`**'s per-entry clause is `(… ↔ bl = X.rl) ∧ (bl ≠ X.rl → 0 < leafKsize pg i ∧
  leafKsize pg i + leafVsize pg i ≤ bboltEntryMax)`; users take `.1` (MatOK), `Txn/WInit` and
  `wOK_XO` prove it.
- **4 (S2). `Write/CurNode.curSt`** carries `bktLocalOK X bl → bktLocalOK Y bl` (3rd component), kept
  by `curSt_step` through `Write/MatOK.bktLocalOK_nodeAdded`; `Cursor.node.spec`'s post adds
  `bktLocalOK X' bl` (after `wOK X → wOK X'`).

### Maintainer 6's hand-off (2026-11-04): what is left of batches 37-42

Not done (in this order, the coordinator's):
- **37.9** `Spec/fmt/Errorf.lean`'s post: add `∗ ⌜_root_.Perennial.errors.IsPointerError err⌝` at the
  end (import `Perennial.Proof.errors.Base`); only bbolt binds the post's pure part (`%Hty`:
  `Mmap/Alloc` ×3, `Mmap/Munmap`; `⟨-, #HeS⟩`: `Mmap/FileSize` ×2, `Mmap/Map`), others use `-`/`%_`.
  Then `⌜err ≠ nil ∧ errPtrTyped err⌝` in the error posts of `DB.fileSize`, `DB.mmapSize`,
  `DB.munmap`, `mmapF` (a lemma `IsPointerError ii → errPtrTyped (.ok ii)` in `Mmap/Remap`;
  `errors.New`'s and `bboltErrVar`'s are pointers; `syscall.Errno` is no pointer type, so
  `errPtrTyped` holds vacuously), and `RemapBody`'s four `fmtErrorOk_errPtrTyped` uses replaced.
  Keep `RemapGaps.fmtErrorOk_errPtrTyped` until `Open/PageSize:419` (U11) stops using it.
- **37.10** `os.File.Close.spec`'s post `… ∗ fmtErrorOkOrNil err` (proof: `os.wp_wrapErrno_ok` in the
  errno branch), `os.OpenFile.spec`'s too (its error branch: `wp_errno` then `pathError_fmtErrorOk`
  and `errnoErr_fmtErrorOk`, as `wp_wrapErrno_ok`). Users to adapt: bboltfs `DB__close`,
  `DB__closeCrash` (`as %err2 Hf` becomes `⟨Hf, -⟩`), bboltfs `Open` (OpenFile), U11b's
  `Open/Close.os.File.Close.specE` goes.
- **37.3** `vwAuth r q v := ∃ V, ghostMapAuth r.n.vw q V ∗ ([∗map] k ↦ u ∈ V, k ↪[r.n.vw]□ u) ∗
  ⌜∀ k u, V !! k = some u → u = { v with base := k }⌝` (`Inv/Tx`), in `wtxFrac` (at `q`, after
  `viewOf`) and `wtxCore` (at `1`, last); `vwAuth r q v = vwAuth r q {v with base := b}` (the
  condition is base-free); `wr_names_alloc` (`Txn/WInitH`) must return the auth; then gap 3
  (`wtxCore_viewOf_rebase`: look up or insert `b`) is proved. Expect ~80 `wtxCore` pattern sites.
- **37.14** draft (untracked, not yet built): `Inv/ShapeOps.lean`: token lists `pgIds`, `entTokL`,
  `brTokL`, `nodeTokL`, `bktTokL`, `txTokL`; `bktToks_list` (resource = list of tokens); the general
  **`txShape_sub`** (`X'.v.pages = X.v.pages → (txTokL X').Subperm (txTokL X) → txShape γ X e ⊢
  txShape γ X' e`; its subperm step is a `sorry` to finish with `List.Sublist.exists_perm_append` and
  `bigSepL_submseteq`). Corollaries to state, with owners: `txTokL_setNode` (a node's tokens
  permuted), `nodeTokL_withEnts_leaf` (leaf entries whose token lists agree), the bucket insert and
  delete (proved structurally from `FiniteMap.toList_insert`/`toList_delete`); `txTokL_nodeAdded`
  (U7: a position's subtree is the page and its children's), `txTokL_bktOpened` (U6: a nested
  tree moves from the parent to the opened bucket), create/drop (U7), rebalance/spill (U8/U9:
  freed pages' tokens dropped, new pages are no view pages), `gensOK_setBkt` (trivial: `setBkt` keeps
  `gen`), `wOK_setNode_withEnts` (U7), and batch 38.5 (S3: `bktLocalOK` under a value replaced at an
  existing key of `B.bm`; the old value persistent first).
- **38.1** (user-approved 2026-11-04): `Spec/go_etcd_io/bbolt/Options.loggerPtrOk (.ok li) := ∃ t (l :
  Loc), li.ty = PointerType t ∧ li.v = #l`; the backend's own `OptsM.ok`
  (`backend/BboltOptsDefs`) gains the same logger condition (so `bbolt.Open_kv`'s premise carries
  it), `backend.newBoltLoggerZap.spec`'s post `boltLogger l ∗ ⌜…⌝`; `newBackend`'s `Hok` for the
  logger-updated options from the new post. Axioms whose statements change: `newBoltLoggerZap.wp_proof`,
  `bbolt.Open_kv.wp_proof` (through `OptsM.ok`). Record in `notes/bbolt-spec-decisions.md` and
  `notes/decisions.md`.
- **39** (Bucket.spill's buffer post, `wdbOK_publish`, the `wrSlots` carve lemma), **40** (`flCurOK`'s
  writer-pending case), **41** (Open's unsynced `loadFreelist`: readers empty), **42** (`rtxFrac`'s
  extent bound `id + (1 + pageOverflow pg) ≤ mv.pgid'.toNat`, `rdTxK_intro`, an accessor for U10e).
  For 41, the simplest candidate is (a): `DB.freepages`' post gives back the reader sets unchanged,
  which needs the sets observable to `Open`; with `metaR` inside `metalock` that means `Open` keeping
  a fraction of the readers' ghost authority until `loadFreelist`, which `beginTx_s` must then not
  need whole — not yet designed.

## Shared-statement fixes, batches 38.1-42 (maintainer 7, 2026-11-04; decided by the coordinator)

- **38.1 (user-approved 2026-11-04, D-G of `notes/bbolt-spec-decisions.md`)**: `loggerPtrOk (.ok
  li) := ∃ t (l : Loc), li.ty = PointerType t ∧ li.v = #l` (`Spec/go_etcd_io/bbolt/Options`; it
  and `OptsM.ok` now take `GoGlobalContext`). The backend's `OptsM.ok` (`backend/BboltOptsDefs`)
  gains a copy `backend.loggerPtrOk o.logger` (importing bbolt's `Options` there made `OptsM`
  ambiguous in `Open_kv.spec`, i.e. changed the axiom's elaboration: not done), with
  `OptsM.ok_withLogger`; `backend.newBoltLoggerZap.spec`'s post `boltLogger l ∗ ⌜∃ lc : Loc, l =
  interface.mkOk (PointerType zapBoltLogger.ty) #lc⌝`; `newBackend` adapted. New
  `Inv/LoggerOk`: `loggerPtrOk_logPtrTyped`, **`OptsM.ok_logPtrTyped`** (`o.ok → logPtrTyped
  o.logger`: Open's `dbFixed` clause, U11f). Axioms whose statements change (TCB update at the
  checkpoint): `backend.newBoltLoggerZap.wp_proof`, `bbolt.Open_kv.wp_proof`,
  `Options.String.wp_proof`, the backend's package-initialization axiom (`Init.lean`, through
  `boltOpenOptionsOk`'s `o.ok`).

- **39. `Bucket.spill.spec`'s success post ends `… ∧ flViewU X' w'.fl ∧ spillBufs X' w.C w'.fl`**
  (`spillBufs`, defined in the spec file so that only its importers rebuild: `pm`'s domain is
  `bufs`'s; each buffer `pageId pg = id`, `pg.length = 4096·(1+overflow)`, `2 ≤ id`, `id + (1 +
  overflow) ≤ X'.t.mv.pgid'`, and each extent slot `∉ treeSlots C` and `∉ pendSlots fl'`; with
  `pgid·4096 ≤ mapLen` and `wdbOK`'s `W` clause these are `W` slots). The spill unit proves it
  (`Bucket__spill.lean`'s `spillPost` copy must gain the conjunct). New **`Inv/Publish`**:
  `WDb.publish w C' S := {w with C := C', W := W.filter (∉ S)}` and **`wdbOK_publish`** (premises:
  `store_publish`'s `hdrop`, `hS`, `hnp`, its `hSb`'s "not free", the new synced freelist page's
  `flCurOK w.fl C' (extentBytes w.wb f)`, and the new state's bounds `C'.txid + 1 < 2^64`, `C'.hwm <
  2^64`, `w.C.hwm ≤ C'.hwm`, `C'.hwm·4096 ≤ w.m.size`, `≤ l` of the mapping, tree slots `< C'.hwm`;
  proved). The written bytes are the writer's before the publish: `tx.write`'s `wb'` goes into
  `w.wb` first (`wSlots_return`/`wbUpd`), then `publish`. New **`Inv/WSlots`** (proved):
  `wSlots_carve` (`wCells (some (b,len)) W ∗ wBytes p W wb size ⊢ wrSlots b p S wb ∗ wCells …
  (wMinus W S) ∗ wBytes p (wMinus W S) wb size`, for `S` nodup, `⊆ W`, whole inside mapping and
  file), `wSlots_return` (back as `S ++ W'`, bytes `wbUpd S wb' wb`; `S ++ wMinus W S` has `W`'s
  members, all `wdbOK` reads), `wrSlots_agree` (the list `cellsR_agree_bytes`: `wrSlots` of whole
  pages inside the mapping → `slotsOwn`, around a step).

- **42. `rtxFrac`'s pure facts end `… ∧ txRoot tx ≠ null ∧ (∀ id pg, v.pages !! id = some pg → id +
  (1 + pageOverflow pg) ≤ mv.pgid'.toNat)`** (`Inv/Tx`), established in `Txn/RdInit.rdTxK_intro`
  (`treeOK`'s extent bound, `isMeta`'s `pgid = hwm`). Shared accessor (new `Inv/RdMeta`, proved):
  **`rdTxK_meta_pgid_acc`** (`rdTxK K tx src q T v ⊢ ∃ m mv, tx.meta ↦{q} m ∗ m ↦{q} mv ∗
  ⌜mv.txid' = v.txid ∧ extent bound⌝ ∗ (… -∗ rdTxK …)`), for U10e's local one. `Tx__close_r:90`
  adapted (`Hf.2.2.2.2.2.2.1`).
- **40: not applied** (the analysis, for the coordinator): the weakened `flCurOK` slot clause (the
  synced page's slots pending only for the writer's own txid) is true from `Commit`'s free of the
  old freelist page on, but it breaks proved users wherever the freed page comes back: the
  rollback (`Txn/WRoll.wdbOK_rolledBack`, used by the proved `Tx.Rollback`; Commit's
  `RollbackFacts`) joins the page's slots back into `W` with the store's bytes `bs`
  (`store_rollback`), and `flCurOK` of the reloaded page needs `bs = w.wb` on them, which nothing
  states (`store_free`'s freelist-page branch takes the slots' `slotsOwn … pg` but `store_rollback`
  returns arbitrary `bs`); `Txn/WJoin.wb_header` (the page is a `W` slot) fails in the pending case
  too. Any design needs that byte link for `Commit`'s error path (Reload reads those bytes). Options:
  (A) `wdbOK` unchanged, `Commit` holds a local weaker `wdbOKc` from the free to the publish/rollback;
  (B) the store keeps the deposited bytes of a freed freelist page (`store_free`'s flpg branch
  records them, `store_rollback` returns them: e.g. a writer-held witness of `σ.bytes` on those
  slots). (B) is needed in both.

- **U10c's access lemmas** (coordinator, after 42): new `Inv/WAccess` (proved): `WX.setFlPage` (moved
  from `Tx__commitFreelist.lean`, same definition: U10c deletes its copy), **`wdbW_fl_acc`** and
  **`wtxW_flpage_acc`** (U10c's local statements verbatim).

- **41: design (not yet applied; Open's unsynced `loadFreelist`, `DB__loadFreelist`'s `hF` and
  `open_setFl_gap`).** Why the reader sets are empty there: during the opening only the spare pair
  can register a reader (a pool loan needs `isBolt`, which `Open` has not published), and
  `freepages`' spare reader has deregistered. Make both facts ghost state:
  1. **opening one-shot** `B.opn` (new `BNs` name, allocated at `Open`): `pending` held by `Open`
     until after `loadFreelist`, then `shot` (persistent) and the shot witness goes into
     `isBoltCoreP`/`isBolt` (so `beginTx` with a pool loan knows the opening is over);
  2. **spare-idle token** `B.spr` (new name): `ghostVar B.spr ½ false` held beside the spare pair
     (`rdPair K.B K.db K.sp` where it is the spare: `wdbOwn`/`wdbLive`, `Open`), the other half in
     `metaR`; `beginTx_s` sets both to `true` (the spare reader's `rdTxK`, src `spare`, holds its
     half), its `Rollback`/`close` sets `false` and gives the half back with the pair (`pairBack`);
  3. `metaR` gains `ghostVar B.spr ½ s ∗ (shot ∨ ⌜(s = false → F = ∅) ∧ (s = true → ∃ k t, F =
     {[k := t]})⌝)` (registration under `pending` only by the spare: a pool `beginTx` has `shot`);
     `pagesInv` the same for `σ.R` (its own quarter of `B.spr`, or a second name).
  Then at `loadFreelist`, `Open` (holding `pending` and the spare's `½ false`) gets `F = ∅` from
  `metaR` and `σ.R = ∅` from `pagesInv`. **`DB.freepages.spec`'s addition**: pre and post
  `ghostVar K.B.spr (1 : Qp).half false` (the spare is idle before and after; U10e's spec file).
  `beginTx_s.spec`: pre takes that half, the reader keeps the `true` half; nothing needs the
  `metaR` authority split. Cost: `BNs` (+2 names, `bnsOf`/`mkGs`), `metaR`, `pagesInv`, `rdTxK`'s
  spare case, `wdbOwn`/`wdbLive` (the spare's half beside `rdPair`), `isBoltCoreP` (shot), and the
  store's `register`/`deregister` lemmas (keep the clause). Not applied: a root-level change
  (`Inv/Names`, `Inv/Locks`, `Inv/Store`) waiting for the coordinator's go and a quiet moment.

- **37.10 (part)**: `os.File.Close.spec`'s post ends `∗ fmtErrorOkOrNil err` (proved from the model:
  `os.wp_wrapErrno_ok` in the errno branch, `fmtErrorOkOrNil_nil` on success; no new trust);
  bboltfs `DB__close`, `DB__closeCrash`, `Open`, `OpenCrash` adapted (`⟨Hf, -⟩`); crashlog's `-`
  unchanged. U11's `Open/Close.os.File.Close.specE` can go (its user `hClose … as %err2 ⟨Hfo,
  #HeC⟩` matches the new post up to `fmtErrorOkOrNil`).

### Maintainer 7's hand-off (2026-11-04): what is left

- **Coordinator's decisions (2026-11-04, after maintainer 7's report)**: batch 40 = (A) and (B):
  `wdbOK` unchanged; `Commit` (U10g) holds a weaker local invariant from the old freelist page's
  free until publish/rollback; the store keeps a freed freelist page's bytes so that
  `store_rollback` returns them (state it for `Commit`'s rollback after `commitFreelist`). Batch
  41: go, as designed above (`B.opn`, `B.spr`, the `metaR`/`pagesInv` clauses); `DB.freepages`'
  pre/post `ghostVar K.B.spr ½ false` added by U10e once the shared side lands (or by the
  maintainer if U10e's file is committed and not mid-edit). Then 37.10's `os.OpenFile`, 37.9,
  37.3, interfaces. **Not started by maintainer 7** (context exhausted): the next maintainer
  starts here.
- **Coordinator's addition (U9q's need; decided; after 40B/41)**: root-bucket entries' names `≤
  MaxKeySize` (32768): in `fileHolds`' `rootShape` (definition and frozen docstring only: true of
  every file bbolt writes, `CreateBucket` checks it, D12) and in the writer invariants
  (`entriesBounded` for the root bucket's leaf entries, or wherever root entries are bounded);
  producers `beginRWTx` (from `rootShape`), `CreateBucket` (its premise), spill (the new tree's
  `treeOK`). `Bucket.spill`'s `rinv_inline`/`rinv_put` need it (an inline value up to 1040 bytes
  plus the name). Not started by maintainer 7.
- **40** (not applied, analysis above): needs the coordinator's choice (A)/(B); (B), the store
  keeping a freed freelist page's bytes for `store_rollback`, is needed either way for `Commit`'s
  rollback after `commitFreelist`.
- **41** (designed above, not applied): root-level (`Inv/Names`, `Locks`, `Store`); `DB.freepages`'
  pre/post gain `ghostVar K.B.spr ½ false`.
- **37.10 (rest)**: `os.OpenFile.spec`'s post `… ∗ fmtErrorOkOrNil err` after the disjunction (as
  Close/Sync). Proof (`Proof/os/OpenFile.lean`, error branch after `unfold os.model.pathError`):
  `iapply wp_fupd; wp_apply wp_errno; iStructNamed pe; ipersist` the fields, then
  `os.pathError_fmtErrorOk pe_ptr _ path (errnoErr e)` with `errnoErr_fmtErrorOk e he0` (as
  `os.wp_wrapErrno_ok`); success: `fmtErrorOkOrNil_nil`. Users: `Proof/os/Crash.lean`,
  `Proof/os/CrashStSpec.lean`, crashlog `Boot`, bboltfs `Open`/`OpenCrash`, bbolt `Open` (U11).
- **37.9**: `Spec/fmt/Errorf.lean`'s post `… ∗ ⌜IsPointerError err⌝` (import
  `Perennial.Proof.errors.Base`). Users outside bbolt (kv/kvdurable/kvreconf examples, raft
  `Link`, cache `Cache__Watch`, `Proof/fmt/Link`) bind the post with `-`/`%_` or not at all: check
  each builds (a `%_` over two pures may not). Then the bbolt threading of the hand-off of
  maintainer 6 (`errPtrTyped` in the error posts of `DB.fileSize`, `mmapSize`, `munmap`, `mmapF`).
- **37.3**: as maintainer 6's hand-off (`vwAuth`, ~80 `wtxCore` pattern sites).
- **Interfaces** not regenerated (Options, Bucket.spill, os.File.Close, newBoltLoggerZap changed);
  TCB baseline update at the checkpoint (38.1's axioms, above).

## Shared-statement fixes, batches 40B and 41 (maintainer 8, 2026-11-04; decided by the coordinator)

`BNs` gained three names (`Inv/Names`, positions 18-20): `fpb`, `opn`, `spr`; `Open` must
allocate them (`Open/Core`'s two `⟨…⟩` constructors and its `pagesInv`/`metaR` construction).

- **40B (`b83de5ce1c`): the freed freelist page's bytes.** `Inv/Store`: `fbCond C fl wtx pb` (the
  live, unpublished writer `w` has `C.flpg = some f`, `f` no tree slot, in its pending entry, as
  some `x` with `x.toNat = f`); **`fbInv B σ`** (inside `bytesWit`, so `pagesInv`'s patterns are
  unchanged): `∃ F, ghostVar B.fpb ½ F ∗ (ghostVar B.fpb ½ F ∨ ⌜fbCond …⌝) ∗ ⌜fbCond … → the store
  slots in F hold F's bytes⌝`; **`fbTok B C fl ws F`** (the writer's side: `⌜fbCond⌝ ∗ ghostVar
  B.fpb ½ F`, or `⌜¬ fbCond⌝`); `fbRec id n pg` (the recorded run), `fbRec_lookup`;
  `wdbOK_not_fbCond`, **`fbTok_of_wdbOK`** (under `wdbOK` there is no freed page, `flCurOK`).
  Lemmas: `store_free` unchanged but its freelist-page case now takes `0 < n` (first conjunct;
  it leaves the token home); new **`store_free_fl`** (`Commit`'s free of the old freelist page,
  premises unbundled) returns `fbTok B C fl' ws (fbRec id n pg) ∗ ⌜fbCond C fl' ws.2.1 ws.2.2.1⌝`;
  **`store_rollback`** takes `(F)` after `w` and `fbTok B C fl ws F` (last in the pre) and its
  post ends `⌜fbCond C fl ws.2.1 ws.2.2.1 → ∀ s ∈ S, ∀ v, F !! s = some v → bs s = v⌝`;
  **`store_publish`** takes `(F)` after `bs` and `fbTok B C fl (some v, some w, false, wl) F` (last
  in the pre). `wdbOK` unchanged (batch 44 brings the flagged `wdbOK'`). Adapted: `Tx__Rollback`
  (`fbTok_of_wdbOK … ∅`). **Broken, active units**: `Tx__rollback.lean:220,287` (`store_rollback`:
  pass `F` and an `fbTok`; after `commitFreelist` the one from `store_free_fl`, otherwise
  `fbTok_of_wdbOK`; the post has one more pure), `Commit/Step.lean:180` (`store_publish`: `F` and
  the token), `Open/Core` (names; `bytesWit` now ends `∗ fbInv B σ`: `iexists ∅; ileft` both
  halves of a fresh `fpb` at `∅`).
- **41 (`c6406935ad`): the opening and the spare state.** `Inv/Locks`: **`opnShot B :=
  dghostVar B.opn DFrac.discard true`** (persistent; `opnShot_pending` against `dghostVar B.opn
  (own 1) false`, which `Open` holds until after `loadFreelist`); `sprCl o M := ∀ k v, M !! k = some
  v → o = some k`; `B.spr : ghostVar (Option Nat)` (the plan's Bool refined: `some k` is the spare
  reader's key, so the reset after its deregistration knows no reader is left): spare side ½
  (**`spareTok B`** at `none`; **`sparePair B db sp := rdPair ∗ spareTok`**, now in `wdbOwn`,
  `wdbLive`, `pairBack .spare`, and `DB.beginTx_s`'s/`DB.freepages`' pre (and the latter's post)
  in place of `rdPair`), `metaR` ¼ (its `ghostMapAuth B.fltx 1 F` is now **`fltxAuth B F`** :=
  that `∗ ∃ o, ghostVar B.spr ¼ o ∗ (opnShot B ∨ ⌜sprCl o F⌝)`), `pagesInv` ¼ (its
  `ghostMapAuth B.rds 1 σ.R` is **`rdsAuth B σ.R`**, the same over `σ.R`). The spare reader holds
  `ghostVar B.spr ½ (some k)`: `rdTx`'s and `rdTxK`'s non-loan case (in place of `emp`).
  `isBoltP` ends `∗ opnShot B` (a pool reader has it). Store lemmas: **`store_register`** takes
  `opnShot B` (last); new **`store_register_spare`** (`spareTok`, `metaR`'s quarter `o` → the
  reader's `½ (some k)`, `metaR`'s `¼ (some k)`, `⌜o = none⌝`); `store_deregister` unchanged
  (keeps the clause); new **`store_spr_reset k t o`** (the spare's `½ (some k)`, `metaR`'s `¼ o`
  and its `fltx` fragment `k ↪ t`, under `metalock` after `store_deregister` and before deleting
  `k` from `F`: back to `spareTok`, `¼ none`, `⌜o = some k⌝`); new **`store_setFl`** (=
  `DB__loadFreelist.open_setFl_gap` with `spareTok B ∗ dghostVar B.opn (own 1) false` in pre and
  post: proved, the gap can go). Users must repack `fltxAuth` after changing `F`: insert under
  `opnShot` (pool) or after `store_register_spare` (`F` was empty: `sprCl none F`), delete keeps
  `sprCl` (spare: after `store_spr_reset`, `F ⊆ {k}` minus `k`).
  `DB.freepages`' spec: `sparePair` in pre and post is the decided `ghostVar K.B.spr ½ false`
  (as `none`).
  Idle units adapted (build): `Txn/RdInit` (`rdTxK_intro`'s last premise), `Txn/RemoveTx`
  (`wp_removeTx` takes `if r.src = .loan then emp else ghostVar K.B.spr ½ (some k)` and gives
  back `if … then emp else spareTok K.B`; it resets the spare state), `Tx__close_r`,
  `DB__beginTx` (`opnShot` from `isBoltP`), `DB__beginTx_s` (`store_register_spare`),
  `DB__beginRWTx`, `Inv/Tx`. **Broken, active units**: `Open/Core` (allocate `fpb` (∅, both
  halves to `pagesInv`'s `fbInv`, left disjunct), `opn` (`dghostVar … (own 1) false`, kept by
  `Open`), `spr` (`none`: ¼ `metaR`'s `fltxAuth`, ¼ `pagesInv`'s `rdsAuth`, ½ `spareTok` beside
  the spare pair, which is now `sparePair` in `wdbOwn`); the two `⟨…⟩` `BNs` constructors take 21
  names; `isBoltP` ends `∗ opnShot B`: after `loadFreelist`, `dghostVar_update` to `true` and
  `dghostVar_persist`), `DB__loadFreelist` (`open_setFl_gap` → `Inv/Store.store_setFl`, with
  `spareTok`/`opn`; `freepages` takes `sparePair`).
- **Batch 44.3 (`a882210a50`)**: `wtxEnd` has no `txShape` clause (8 conjuncts: `K.full`,
  records, `wdbLive`, `rwlock`, `cls` half, `ghostVar r.n.v 1`, data quarter, pure). Adapted:
  `Tx__close_w`, `Tx__Rollback`. **Active users to adapt**: `Tx__rollback` (its `iunfold wtxEnd`
  patterns, lines 168/240/353/449/470), `Tx__commitFreelist`, `Commit/AssembleEnd`,
  `Tx__Commit_err`.
- **Batch 44.8 (`fa83cfcff7`)**: `internal/freelist/Lemmas/Model.toList_lookup_perm` renamed
  `toList_lookup_perm_w64`.

### Maintainer 8's hand-off (2026-11-04): what is left, in the coordinator's order

1. **Item 3 + batch 43.4** (root-bucket entry names `0 < len ≤ MaxKeySize = 32768`): not started.
   `rootShape` (`Model/Tree:236`) per-entry tuple `⟨flags, 0 < ksize, ksize + vsize ≤ max,
   nested⟩`; any new conjunct shifts positional users: `Write/Bound` (`topPg_of`), `Read/WOpenOK`,
   `Spill/STree`, `Spill/BktFinal` (spill: producer), `Commit/CheckPureRoot:304` (Commit). Frozen
   docstring in `Spec/go_etcd_io/bbolt/Api.lean:159`. Writer side: `posShape`'s root clause
   (`bl = X.rl` entries) or `entriesBounded`; producers `beginRWTx` (from `rootShape`),
   `CreateBucket` (premise), spill.
2. **Batch 43** (U9t's `StartFacts`, `Spill/BktLoopPureStart.spill_startFacts`): 1 (`treeOK w.C ∧
   w.C.hwm ≤ X.t.mv.pgid'.toNat` as a writer fact), 2 (accessors from `wtxW`: `pgid < 2^62`, root
   `bm` injective), 3 (no cached child is the root, `heapOK`/`bktClean`): not started.
3. **37.10 `os.OpenFile`** (recipe in maintainer 7's hand-off; `Proof/os/OpenFile.lean:95`'s error
   branch as `os.wp_wrapErrno_ok`, `ErrorOk.lean:77`), **37.9**, **37.3**: not started.
4. **Batch 44** 1, 2, 4, 5, 6, 7: not started (44.3, 44.8 done). For 44.1 note that 40B's
   `store_free_fl` already hands the writer `fbTok` with `fbCond` (the freed page's ids pending
   for its own txid): `wdbOK' true` is the matching relaxation of `flCurOK`.
5. **U10h's link** (`Commit/CheckKeyOrder*` into `DB.freepages`' check; `keyToString` is now
   `(f : GoFunc)`): not started.
6. Interfaces: regenerate once every bbolt module builds.

## Shared-statement fixes, item 3 and batches 43, 44 (maintainer 9, 2026-11-04; decided by the coordinator)

- **Item 3 + 43.4 (`58750b5b17`): root-bucket names of `1..MaxKeySize` bytes.** `rootShape`
  (`Model/Tree`; `treeOK`'s and `fileHolds`' docstrings, `Spec/.../Api.lean`) has the per-entry
  tuple `⟨flags, (0 < ksize ∧ ksize ≤ maxKeySize), ksize + vsize ≤ max, nested⟩` (the name bound
  merged into the second component: `.2.2.1`/`.2.2.2` users unchanged). `entriesBounded` per entry:
  `0 < key ∧ key + value ≤ max ∧ (bl = X.rl → key ≤ maxKeySize)` (users of `.2` as the sum take
  `.2.1`). `posShape` per entry: `(flags ↔ bl = X.rl) ∧ (0 < ksize ∧ ksize + vsize ≤ max) ∧ (bl =
  X.rl → ksize ≤ maxKeySize)` (the bound unconditional: the root's view entries too, which gives
  43.4's `rootKeys` on the root's page positions). Adapted: `Txn/WInit`, `Read/WOpenWOK`,
  `Write/MatOK` (`newNodeBnd` takes `hroot : P → page keys ≤ maxKeySize`; its two callers pass
  `sorry`, OPEN U7: the root bucket's page keys, a leaf's by `posShape`, a branch's by exact
  branch keys), `Rebalance/RblXSMat` (same, OPEN U8), `Spill/DerefWOK`, `Spill/BktStart`.
  **Broken, active**: `Spill/BktLoopPureStart.lean:116` (`rootLoc_start`: pass
  `(hok.2.2.2.1 … w hw).2.1`-style, i.e. `⟨(…).1, (…).2.1⟩` for the pair it wants) and `:169`
  (`hs.2 hne` → `hs.2.1`), U9x2. Producers still to prove the new conjuncts: spill (`rootShape` of
  the new tree, `BktFinal.spillOK_of_root`'s `hshape`, from `entriesBounded`'s root clause),
  `CreateBucket` (its premise `n.length ≤ maxKeySize`), Put/Delete (non-root buckets: vacuous).
- **Batch 43 and 44.2, 44.4-44.7 (`39310f1a07`): the writer's carried facts, the spill's start.**
  - `Inv/Tx.wrFacts X := liveReach X ∧ X.t.t.commitHandlers' = slice.nil ∧ (∀ B, X.t.bs !! X.rl =
    some B → ∀ k c, B.bm !! k = some c → c ≠ X.rl)`, the last conjunct of `wtxFrac`'s facts and
    of `boltTxDef_wtxW`'s (`⌜wOK X ∧ T.cur = … ∧ T.base = … ∧ gensOK T X ∧ wrFacts X⌝`: `Hf.2.2.2.1`
    is `gensOK`, `Hf.2.2.2.2` `wrFacts`). 44.2: `Commit/AssembleGaps.wOK_liveReach` → `Hf.2.2.2.2.1`;
    44.5: `wtx_handlers_nil` → `Hf.2.2.2.2.2.1`. Producer `Txn/WInit.wrFacts_wx0` (`beginRWTx`).
  - `Inv/Txs.metaCopyOK mv C` (= U10g's `wMetaOK X w` with `mv = X.t.mv`, `C = w.C`); `txExcl`'s
    writer facts end `flViewU X w.fl ∧ metaCopyOK X.t.mv w.C ∧ treeOK w.C` (44.4, 43.1);
    `Tx.Rollback`'s `TxExclWGap` post is `⌜flViewU X w.fl ∧ metaCopyOK X.t.mv w.C ∧ treeOK w.C⌝`.
    Producer `Txn/WInit.metaCopyOK_init` (`beginRWTx`).
  - **The names that replace `spill_startFacts`** (U9x2): `Spec/.../Bucket__spill.spillStartOK X w
    := treeOK w.C ∧ w.C.hwm ≤ X.t.mv.pgid'.toNat ∧ ∀ B0, X.t.bs !! X.rl = some B0 → (∀ k c, B0.bm
    !! k = some c → c ≠ X.rl) ∧ (∀ k k' c, … → k = k')`, a new premise of `Bucket.spill.spec`
    (after `flViewU X w.fl`), gives `StartFacts`' `cok`, `hwm`, `notRoot`, `inj`; `mark62` is
    `Inv/WAccess.mark62_of_mapLen _ _ hml (wdbW_mapLen_le …)` (the latter `wdbW … ⊢ ⌜mapLen w.ms ≤
    0xFFFFFFFFFFFF⌝`); `rootKeys` from `entriesBounded` (`.1`, nodes) and `posShape` (`.2.1.1`, the
    root's page positions). `Commit` gives `spillStartOK X1 w1` from `txExcl` (`metaCopyOK`'s
    `pgid = hwm`, `treeOK`), `gensOK_bktLoc_inj` and `wrFacts`, kept by `rebalance` (44.6).
  - 44.6: `Bucket.rebalance.spec`'s post ends `… ∧ X'.t.t = X.t.t ∧ X'.t.mv = X.t.mv` (proved from
    `rblRel`). 44.7: `Bucket.spill.spec`'s success post ends `… ∧ X'.t.t = X.t.t ∧ X'.rl = X.rl ∧
    X'.t.mv = { X.t.mv with pgid' := X'.t.mv.pgid' }` (the spill unit proves it).
  - **Broken, active**: `Tx__Commit_err.lean:180` (`%Hflv` is now the triple: pass `Hflv.1` to
    `wp_rebalance`, `:317`; `wtx_wMetaOK` → `Hflv.2.1`, `wOK_liveReach X Hf.1` → `Hf.2.2.2.2.1`;
    the rebalance post's `%Hrb` has two more conjuncts at its end; the spill call takes
    `spillStartOK`), `Commit/AssembleGaps` (gaps 1, 4, 5 can go), `Bucket__spill.lean` (U9x2: the
    spec's new binder; its post's three new conjuncts).
- **Coordinator's addition (a)** (Commit's gaps 6/7, `Tx__Commit_err.lean:358,385,411,454`): all
  covered by the spec changes above: `hmv1` is the rebalance post's last conjunct; `hrl2` the spill
  posts' `(X'.t.bs !! X'.rl).isSome`; `hmv2` their `X'.t.mv = {X.t.mv with pgid' := …}`; on the error
  side `hwr2` from `X'.t.t = X.t.t`, `htx2` from the meta copy (`X'.t.mv.txid' = X.t.mv.txid'`).
  Producers to prove (no `sorry` was added to their files; they do not build against the new
  spec until they do): `Bucket__spill.lean` (U9x2: both posts' new conjuncts, its spec binder
  `spillStartOK`), and through it `node.spill`'s `spPost` (U9w2) for the root's record and the meta
  copy; `Bucket.rebalance`'s new conjuncts are proved (`rblRel`).
- **44.1 (`4581da6da2`, `ed366aecb1`): the flagged writer side**, new module `Inv/WdbFlag`:
  `flCurOKr fl C wtx pg` (`flCurOK` but the synced page's slots may be pending, not free, for `wtx`
  only), `flClause fr w`, `wdbOK' fr w` (= `wdbOK` with `flClause fr` as its 6th conjunct;
  `wdbOK'_false : wdbOK' false w ↔ wdbOK w` is `Iff.rfl`), `wdbOK_wdbOK'`, **`wdbW' fr K tx v w`**
  (`wdbLive` ∗ `⌜wdbOK' fr w ∧ ms ∧ view⌝` ∗ `∃ F, fbTok K.B w.C w.fl (wLive v w.C) F`),
  `wdbW_wdbW'` (any flag, `F = ∅`), `wdbW'_wdbW` (flag false), `wdbW'_ok`. `Commit` forms `wdbW'
  true` after `store_free_fl` (its `fbTok` and `fbCond`; the slot clause's right disjunct from the
  free). `DB.grow.spec` is over `wdbW' fr` (`∀ fr` first; proof still U4's `sorry`): **breaks**
  `Tx__Commit_err`'s grow call (U10i: pass `fr`; before the free `wdbW_wdbW' false`).
  **Not done: `Tx.allocate.spec` over `wdbW' fr`** (`commitFreelist` allocates after the free). Its
  proof (`Tx__allocate`, complete) and `Mmap/Alloc`, `Mmap/AllocBase`, `Mmap/RemapEnd`
  (`wdbOK_alloc`, `wdbOK_remap`, `wdbLost_intro`, `remap_post`) must carry `wdbOK' fr` and the
  token: the alloc/remap steps never touch `C.flpg`'s clause but through `fl` (allocation removes
  free ids: `flCurOKr`'s slot clause and `free ⊆ flIds` keep) and `W`/`ms` (the clause reads
  `extentBytes w.wb f`, unchanged by alloc; a remap keeps `wb`). Plan: state each lemma at `wdbOK'
  fr` with a `cases fr` whose `false` case is the existing lemma, the `true` case its copy; the
  `wdbLost` side (a failed remap) needs a flagged `wdbLost'` too (Commit's rollback after it
  takes the token to `store_rollback`). `wtxEnd`/`store_rollback` users take the token from
  `wdbW'`.
- **37.10 (`0506c7fb90`)**: `os.OpenFile.spec`'s post `(… ∨ …) ∗ fmtErrorOkOrNil err` (proved:
  `pathError_fmtErrorOk` with `errnoErr_fmtErrorOk`); bboltfs `Open` adapted. `Open.lean`'s
  `os.OpenFile.specE` (U11g) is now `os.OpenFile.spec` verbatim: drop it, take
  `os.OpenFile.wp_proof`. The crash variants (`specCrash`, `specCrashS`) are unchanged.
- **37.9, spec part (`4581da6da2`)**: `fmt.Errorf.spec`'s post ends `∗ ⌜IsPointerError err⌝`
  (import `Perennial.Proof.errors.Base`); the axiom `fmt.Errorf.wp_proof`'s statement changed (TCB
  baseline: the coordinator's). bbolt's binders adapted (`Mmap/Alloc` ×3, `Munmap`: `%Hptr`;
  `FileSize` ×2, `Map`). Users outside bbolt bind with `-`/`%_`/partial patterns (not rebuilt here:
  cache `Cache__validate*`, k8s, etcd server, kv examples). **Not done**: the threading of
  `errPtrTyped` into the error posts of `DB.fileSize`, `DB.mmapSize`, `DB.munmap`, `mmapF`
  (maintainer 6's recipe), and `RemapBody`'s four `fmtErrorOk_errPtrTyped` uses.

### Maintainer 9's hand-off (2026-11-04): what is left, in order

1. **44.1's `Tx.allocate`** over `wdbW' fr` (plan above), then `commitFreelist` (U10i) takes it.
2. **37.9's threading** (`errPtrTyped` in the four Mmap error posts; `Hptr` is now bound in
   `Mmap/Alloc`, `Munmap`; `FileSize`/`Map` bind `%Hptr0`/`%Hptr`).
3. **U10h's link** (`7daa62fdcc`, `df7dc998a8`, `52fbbdcb1f`: `Commit/CheckKeyOrder{,Verify,Int}`
   prove `Tx.recursivelyCheckPageKeyOrder_ok`; link it into `DB.freepages`' check): not started.
4. **37.3** (`vwAuth`, ~80 `wtxCore` pattern sites): not started.
5. Interfaces and the TCB baseline: at integration (`fmt.Errorf.wp_proof` changed).
- **Open `sorry`s added by maintainer 9**: `Write/MatOK` ×2 (the root bucket's page keys ≤
  `MaxKeySize`, `newNodeBnd`'s `hroot` at its two callers; U7), `Rebalance/RblXSMat` ×1 (the same,
  U8). Removable once someone proves them: `Commit/AssembleGaps`' gaps 1, 4, 5 (now facts:
  `wrFacts`, `metaCopyOK`), `Spill/BktLoopPureStart.spill_startFacts` (from `spillStartOK`).

## Shared-statement fixes, 44.1's `Tx.allocate`, 37.9, coordinator's additions (maintainer 10, 2026-11-04)

- **44.1, `Tx.allocate` over the flagged writer side (`04de465202`, `4f750f5d78`).** `Inv/WdbFlag`:
  **`wdbLost' fr`** (`wdbLost` with `wdbOK' fr` and `∃ F, fbTok … (some v, some (txid+1), false,
  false) F`), `wdbLost_wdbLost'`, `wdbLost'_wdbLost`; the device **`WDb.noFl`** (`flpg := none`:
  `wdbOK'_noFl`, `wdbOK'_of_noFl`; a pure `wdbOK` lemma that does not read the freelist page's clause
  applies to `wdbOK' fr` through it); `wdbOK'_flClause`, `flClause_congr` (C, fl, wb kept),
  `flClause_alloc`; `fbTok_ws` (reads only the txid and publish flag), `fbTok_alloc`.
  **New spec `Tx.allocate_f.spec`** (`Spec/…/Tx__allocate_f.lean`: `∀ fr` first, `wdbW' fr`,
  `wdbLost' fr`), proved (`Proof/…/Tx__allocate_f.lean`, `Mmap/TxAlloc`); **`Tx.allocate.spec`
  unchanged**, derived at `fr = false` (`Tx.allocate.spec_of_f`): its callers (spill) are untouched.
  Flagged through the chain (`∀ fr` first): `DB.allocate.spec`, `DB.mmap.spec`,
  `DB.mmapUnlocked.spec`; lemmas `wdbOK'_alloc` (AllocBase), `wdbOK'_lost`, `wdbLost'_intro`
  (RemapLost, take the token), `wdbOK'_remap`, `wdbRemap_remap'`, `remap_W_file'`,
  `wdbW'_remap_intro`, `remap_post'` (RemapEnd), `wdbOK'_mem_W`, `wCells_gather'` (RemapBase),
  `wdbOK'_size_lt/_page` (RemapGaps), `remap_gather {fr}`, `wdbW'_file_acc`, `fbTok_wLive` (Alloc).
  **For U10i (`Tx__commitFreelist`)**: take `hAlloc : Tx.allocate_f.spec`; the spec gets `∀ fr`
  and `wdbW' fr` in pre and success post, `wdbLost' fr` in the second frame entailment
  (`F ∗ wtxLost … ∗ wdbLost' fr K tx X'.v w' ⊢ |==> wtxEnd …`); call `hAlloc fr …`. Open:
  `wtxEnd` holds `⌜wdbOK w⌝` and no token, so with `fr = true` neither frame entailment can be
  proved (no `wdbOK` after the free); `wtxEnd` (and `Tx.rollback.spec`'s `rbOK`) needs the flag
  and the token too (`store_rollback` takes it). Not done (a shared-statement change for the
  coordinator to decide).
  **`DB.grow`'s proof** (U4's `sorry`, `DB__grow.lean`): not started (a unit's work: Truncate,
  Sync, `wBytes` past the old end).
- **Coordinator's addition (1)** (`4f750f5d78`): `X'.t.bs = X.t.bs` after a remap is false
  (`dereference` copies the nodes, `WX.rebase` marks view sources stale). What holds, new module
  `Mmap/RemapRec`: `derefRel_rebase_tt` (`(Xd.rebase b).t.t = X.t.t`), `derefRel_rebase_bs` (every
  bucket record's `BRec.fixed` = `(bv, ib, nm, bm)` kept, and which buckets have one),
  `derefRel_rebase_root` (the root's record's `isSome` and `bm`). Not wired into
  `Tx.allocate_f.spec`'s error post: it already gives `∃ Xd b, derefRel X Xd ∧ X' = Xd.rebase b`.
- **Coordinator's addition (2)** (`9660c66cea`): `Bucket.rebalance.spec`'s post ends `… ∧ X'.t.mv =
  X.t.mv ∧ (X'.t.bs !! X.rl).map BRec.bm = (X.t.bs !! X.rl).map BRec.bm` (from `rblRel`).
  **Broken, active**: `Tx__Commit_err.lean:316` (`%Hrb`: the old last conjunct `X'.t.mv = X.t.mv`
  is now `.1` of the last pair).
- **37.9's threading (`2024dee090`)**: `errPtrTyped` moved to new `Mmap/ErrPtr`
  (`errPtrTyped_of_ptr` from `IsPointerError`, `errPtrTyped_ptrOk`, `errPtrTyped_errno`); the error
  posts of `DB.fileSize`, `DB.mmapSize`, `DB.munmap`, `mmapF` are `⌜err ≠ nil ∧ errPtrTyped err⌝ ∗
  fmtErrorOk err`; RemapBody's four stand-in uses gone. `fmtErrorOk_errPtrTyped` (RemapGaps, a
  `sorry`) stays for `Open/PageSize.lean:419` (`os.File.Stat`'s error; needs Stat's error post to
  say `IsPointerError`, as OpenFile's). **Broken, active**: `Open/MmapOwn.lean:111,145,194` (U11g:
  `absurd rfl hne` → `hne.1`, `he` → `he.1`; the pair's `.2` is the `errPtrTyped`).
- **U10h's link (item 3): blocked.** `/tmp/m10/FreepagesLink.lean` (outside the repository: it
  does not build) composes `Tx.recursivelyCheckPageKeyOrder_ok.wp_linked`,
  `Tx.recursivelyCheckBucket_root.wp_linked`, `DB.freepages.wp_linked` from the proved pieces. It
  waits for `Commit/CheckSplit.lean:47-52` (U10i), broken since batch 41: **finding**: `rdTxK`'s
  (`Inv/Ctx:134`) and `rdTx`'s (`Inv/Tx:156`) spare branch is `ghostVar K.B.spr (1 : Qp).half (some
  k)` at every fraction `q`, so a spare reader cannot be split (`rdTxK_halves`) and
  `boltTxDef_fractional` (`sorry`) is false for it. Proposed fix: `ghostVar K.B.spr q.half (some
  k)` in both (identical at `q = 1`; `ghostVar` halves split), then CheckSplit's `Hp2` splits it.
- **Not started**: 37.3 (`vwAuth`), item 5 (`Write/MatOK` ×2, `Rebalance/RblXSMat` ×1: the root
  bucket's page keys ≤ `MaxKeySize`).

### Maintainer 10's hand-off (2026-11-04): what is left, in order

1. Decide/apply the `rdTx`/`rdTxK` spare-branch fix (above), then build `Commit/CheckSplit` (U10i)
   and move `/tmp/m10/FreepagesLink.lean` in as `Commit/FreepagesLink.lean`.
2. The flagged `wtxEnd` (with `wdbOK' fr` and the `fbTok`), for `commitFreelist`'s and `Commit`'s
   rollbacks after the free; `rbOK`/`Tx.rollback.spec` accordingly.
3. 37.3 (`vwAuth`), item 5's three `sorry`s, `DB.grow`'s proof.
- Open `sorry`s: none added by maintainer 10; `fmtErrorOk_errPtrTyped` has one user left
  (`Open/PageSize`).

## Shared-statement fixes, the coordinator's queue for maintainer 11 (2026-11-04)

- **Item 1, the flagged rollback (`475849f646`).** `wtxEnd` held `⌜wdbOK w⌝` and no token, so no
  rollback after `Commit`'s free of the synced freelist page could be stated. A finding on the way:
  with only `∃ F, fbTok … F` the rollback is unprovable (the bytes `store_rollback` returns for the
  freed page's slots are `F`'s, unrelated to `w.wb`, which `flCurOK` reads after the rollback). New
  in `Inv/WdbFlag`: **`fbRel w F`** (a pending slot of the synced page's extent `[f, f + 1 +
  pageOverflow (w.wb f))` has the page's id in the writer's pending entry, and `F !! s = some (w.wb
  s)`), carried next to the token: `wdbW' fr`, `wdbLost' fr` end `∃ F, fbTok … F ∗ ⌜fbRel w F⌝`
  (`fbRel_of_wdbOK`: vacuous under `wdbOK`; `fbRel_congr` (C, pending, wb kept), `fbRel_alloc`).
  **`wtxEnd' fr`** (`wdbOK' fr`, the token with `fbRel`), `wtxEnd_wtxEnd'` (any flag),
  `wtxEnd'_wtxEnd` (false); `wtxEnd` and `rbOK` unchanged (`rbOK` reads no `wdbOK`). New spec
  **`Tx.rollback_f.spec`** (`Commit/RollbackFSpec`: `∀ fr`, `rbOK`, `fr = true → ws.2.2.1 = false`,
  pre `wtxEnd' fr`), proved without `sorry` in `Tx__rollback_f.lean` (Tx__rollback's proof with
  the token to `store_rollback` and `Commit/RollbackFlag.wdb_rollback_f`/`flCurOKr_rollback`; its
  helpers renamed `rb…`), and **`Tx.rollback.spec_of_f`**. Mmap/{Alloc,RemapEnd,RemapLost,RemapBody}
  thread `fbRel` (`wdbW'_remap_intro`, `remap_post'`, `wdbLost'_intro` take `hF : fbRel w F`).
  **For U10j**: (a) `Tx__rollback.lean` may become `theorem Tx.rollback.wp_proof … :=
  Tx.rollback.spec_of_f (Tx.rollback_f.wp_proof wp_meta wp_Txid wp_Freelist wp_FlRollback
  wp_hasSynced wp_freepages wp_NSR wp_Reload wp_page wp_close)` with `public import
  Proof.go_etcd_io.bbolt.Tx__rollback_f` (its own helpers can then go; `Tx__rollback_f` does not
  import it). (b) `commitFreelist`/`Commit` after the free take `wp_rollback_f` and form `wtxEnd'
  true`; at the free (`store_free_fl` with `pg = w.wb`, `n = 1 + pageOverflow (w.wb f)`) they prove
  `fbRel w2 (fbRec (W64 f) n w.wb)` (`fbRec_lookup`; the page id is in the writer's pending entry
  after `freePages`). U4e already threads it through `DB.grow` (`fbRel_grow`).
- **Item 2 (`5c2e7b35ac`)**: `rdTx`'s and `rdTxK`'s spare branch is `ghostVar K.B.spr q.half (some
  k)` (identical at `q = 1`). `boltTxDef_fractional` was already proved (batch 37.15; its reader
  branch is the loan's, the spare branch does not occur in it).
- **Item 3 (`5c2e7b35ac`, `013bd3207d`)**: `Commit/CheckSplit` repaired (`rdTxK_halves` splits the
  spare share); **`Commit/FreepagesLink`** landed (maintainer 10's link: `Tx.recursivelyCheck
  PageKeyOrder_ok.wp_linked`, `Tx.recursivelyCheckBucket_root.wp_linked`,
  `DB.freepages.wp_linked`). Also `Txn/StatSlot` repaired (broken since batch 41: `isBoltP`'s
  `opnShot`), so `DB__Stats` builds again.
- **Item 4 (`9ad486c3db`, a helper)**: `Write/MatOK`'s two `hroot` sorries proved (new
  `Write/RootKeys`: `pageKeys_le_of_treeKeys`, `posShape_rootLeaf`, `ownHas_snoc`).
  **Open**: `Rebalance/RblXSMat.lean:275` (the same premise): `rblX` (`Rebalance/RblX.lean:38`)
  carries no `posShape` (nor its root-name clause), which it needs; that is also the open
  `RblX.lean:159` (`rebalOK_of_rbl`'s `leafShape`/`posShape` sorries). Fix: `rblX` carries
  `posShape X` (its producers and every step lemma keeping it), then the sorry closes as MatOK's
  child case. Not started (a change to U8's statements).
- **37.3 (`3055e05b6b`)**: the writer's view registry's authority, `Inv/Txs.vwOwn γ` (auth, every
  entry's persistent fragment, `∀ k u, V !! k = some u → u = {v0 with base := k}`), lives in the
  transaction's `txsInv` entry (`readerHandles`' writer case; it was `emp`), **not** in
  `wtxCore`/`wtxFrac`: no pattern site changed. `Txn/WInitH.wr_names_alloc` returns it (a last
  conjunct), `DB__beginRWTx` registers it. **Gap 3 proved** (`Mmap/RemapGaps.wtxCore_viewOf_rebase`,
  now with `(hE : ↑(txsN K.N) ⊆ E)`): open the entry (`Txn/Txs.txs_open`), the done entry
  excluded by `statsTok`, find or insert the new base.
- **Item 6 (`34ff6c7115`, a helper)**: `os.File.Stat.spec`'s post ends `⌜∀ ii, err =
  GoInterface.ok ii → IsPointerError ii⌝` (proved from the model: no trust change); users bind it
  with `-` (`Mmap/FileSize`, bboltfs `Open`, `OpenCrash`, crashlog `Boot`). **Breaks U11g**:
  `Open/PageSize.lean:290` (`⟨Hfo, Hfd, Hm, Hr, #Hek⟩` → `⟨Hfo, Hfd, Hm, Hr, #Hek, %Hptr⟩`), `:419`
  (`ihave %Hpt := fmtErrorOk_errPtrTyped _ $$ Hek` → `have Hpt := errPtrTyped_of_ptr ii (Hptr ii
  rfl)`), `Open.lean:458` (`#Hse⟩` → `#Hse, -⟩`). Then `RemapGaps.fmtErrorOk_errPtrTyped` has no
  user: delete it (one `sorry` fewer: the TCB baseline, at integration).

### Maintainer 11's hand-off (2026-11-04): what is left, in order

1. `rblX` carries `posShape` (item 4's last `sorry`, `RblXSMat:275`, and `RblX:159`).
2. U10j: switch to `Tx.rollback_f` (above); U11g: the three Stat edits, then delete
   `fmtErrorOk_errPtrTyped`.
3. Interfaces and the TCB baseline at integration.
- Open `sorry`s: none added by maintainer 11; removed: `RemapGaps.wtxCore_viewOf_rebase` (gap 3),
  `Write/MatOK` ×2 (item 4).

## Shared-statement fixes, the coordinator's queue for maintainer 12 (2026-11-04)

- **Item 1, the receipts' bound (`3369bd5d50`; decision D-H).** `Open.spec` already takes
  `[ReceiptBoundLe GF (2 ^ 62)]`, so the frozen triple is unchanged; `isBoltCoreP`'s pure facts now
  begin `(t0 < 2 ^ 62 ∧ receiptBound GF ≤ 2 ^ 62) ∧ db ≠ null ∧ ↑N ## ↑osN` (the `.1` was unused;
  `.2.1`, `.2.2` users unchanged). Lemmas: `Inv/Bolt.receipt_txid_lt t0 c ht0 hrb : ⧗ (c - t0) ⊢
  ⧗ (c - t0) ∗ ⌜c + 1 < 2 ^ 63⌝`, `isBoltCoreP_receipts`, `isBoltCoreP_txid_lt`;
  `Inv/WdbFlag.wdbW'_txid_lt fr K tx v w : K.core ∗ wdbW' fr K tx v w ⊢ wdbW' fr K tx v w ∗
  ⌜w.C.txid + 1 < 2 ^ 63⌝` (and `wdbW_txid_lt`). **For U10k**: `Tx__Commit_err.lean:372`'s
  `htx63` (and `commitStep_commit`'s `htree`): `icases wdbW'_txid_lt fr K tx _ _ $$ [Hkc Hwdb] with
  ⟨Hwdb, %htx⟩` (`Hkc` the core), then `X1.t.mv.txid' = w.C.txid + 1` from the meta copy.
  **Broken, U11g**: `Open/Core.lean:289` (`open_core_fl`'s `exact ⟨htx.2, hdb, hN⟩`). Fix: add
  `[ReceiptBoundLe GF (2 ^ 62)]` after `[ThreadBoundLe GF (2 ^ 29)]` to `open_core_fl` and
  `open_core` (Open/Core) and to `DB.loadFreelist.spec_open`'s binder (`DB__loadFreelist.lean:101`,
  `∀ [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 62)] …`); the line becomes `exact
  ⟨⟨htx.2, ReceiptBoundLe.le (GF := GF) _⟩, hdb, hN⟩`. `Open.lean`'s `hLoad` then resolves the
  instance from `Open.spec`'s.
- **Item 2 (`d3c91bd0d1`)**: `Tx.close_w.spec`'s post is `txDoneDef tx ∗ tx.[Tx, go!"commitHandlers"]
  ↦ X.t.t.commitHandlers'`; proof and its callers (`Tx__Rollback`, `Tx__rollback_f`: `as ⟨Hdone,
  -⟩`) adapted. `Tx__Commit_err` takes `wp_close` but does not call it yet: bind `as ⟨Hdone, Hch⟩`.
- **Item 3 (`ad788d5fa6`): dirty pages past the end of the file.** OsFs's `WriteAt` extends the
  file (`os.File.WriteAt.spec`: the zero gap, then the data; it needs the cells of the gap, `[min
  off size, off + n)`), so the write is possible; `Tx.write.spec` is kept (proved, pages inside the
  file) and **`Tx.write_ext.spec`** is new (`Spec/go_etcd_io/bbolt/Tx__write_ext.lean`): `bufsOK
  bufs (l / 4096)`, `l < 2 ^ 63`, a tail `T` with `(bufSlots bufs ++ T).Nodup`, `T` inside the
  mapping and every slot of the mapping not wholly inside the file in `bufSlots bufs ++ T`; the
  slots as `wrSlotsSz b p S wb size` (`Inv/WSlots`: `wBytes p S wb size` and the cells, i.e. the
  writer's own form: a slot past the end owns no `osBytes`). Post: `om.size ≤ om'.size ≤ max om.size
  l`, a tail slot inside the old file keeps its bytes, lengths of the slots inside the new file;
  success: every page slot inside the new file, `slotsOwn` of the pages, `wrSlotsSz T wb'
  om'.size`; error: `wrSlotsSz (bufSlots ++ T) wb' om'.size`. Proof
  (`Proof/go_etcd_io/bbolt/Tx__write_ext.lean`): **the in-file case from `Tx.write.wp_proof`**; the
  case of a page past the end is a `sorry` (**OPEN**, a unit's work: `Tx__write.lean`'s loop over
  the current size; each `WriteAt` takes the gap's cells from `T`). New in `Inv/WSlots`:
  `wrSlotsSz`, `wrSlotsSz_app`/`_congr`/`_grow`/`_in` (`= wrSlots` inside the file),
  **`wSlots_carveSz`** (`wSlots_carve` without the size premise: `S` inside the mapping only),
  **`wSlots_returnSz`** (back at the new size; the rest of `W` inside the old file). **For U10k**
  (`Commit/TailWrite.cm_write_step`): take `Tx.write_ext.spec`; `T` = the `W` slots below
  `l / 4096` not wholly inside the file and not in `bufSlots` (all of them `W` slots: past the file
  is past the mark, `wdbOK`'s tree/pending clause); carve `bufSlots ++ T` with `wSlots_carveSz`;
  return with `wSlots_returnSz` (`size' = om'.size`, the rest inside the old file since every slot
  not wholly inside is in `S`). `DB.grow.spec` unchanged (U4e): under `NoGrowSync` it leaves the
  size, the write then extends the file.
- **Item 4 (`0ca67db5a4`): the buffers' slots not free, the extents disjoint.** `Spill/NodeSpec.bufsOK`'s
  and `Bucket__spill.spillBufs`' per-slot clause is now `id.toNat + j ∉ treeSlots C ∧ id.toNat + j
  ∉ pendSlots fl ∧ (∀ x ∈ fl.free, x.toNat ≠ id.toNat + j) ∧ ∀ id' pg', X.t.bufs !! id' = some pg' →
  ∀ j' < 1 + pageOverflow pg', id.toNat + j = id'.toNat + j' → id' = id` (the two definitions stay
  textually equal: `BktEndPost.end_bufs` is `exact`). `Inv/WSlots.bufSlots_nodup_of_disj` turns the
  last conjunct into `(bufSlots bufs).Nodup` (`tx.write`'s premise). Adapted:
  `Spill/BktLoopPureInline` (proved: `freePages` keeps `free`, the buffers unchanged).
  **Named `sorry`s for U9w4** (`Spill/PcStepBufs.pcStepX_bufsOK`, 4): the new buffer's run is no
  longer free (`allocRes` takes the run out of `free`; `allIds` has no duplicates) and meets no old
  buffer's extent (an old buffer's slots are not free, by its own clause, and lie below the old
  mark, where a mark allocation does not reach); an old buffer's slots stay non-free (`free` only
  shrinks: `applySteps_free_sub`) and miss the new buffer's run (the same two facts). **For U10k**:
  `Tx.commitFreelist.spec`'s success post (`Tx__commitFreelist.lean`, U10k's file) should add that
  the freelist page's extent `[id, id + flCount …)` meets no slot of `X1`'s buffers (the run is
  allocated from `free` or the mark, which `spillBufs`' new clauses exclude), so that
  `(X1.setFlPage …)`'s buffers keep `bufsOK`'s disjointness for `tx.write`.
- **Item 5 (`49353188ba`; decision D-I)**: `fileHoldsDef`'s pure facts `m.maps = ∅ ∧ xs.length =
  m.size ∧ m.size < 2 ^ 62 ∧ fileOK …`; `fileHolds_decode` gives `⌜m.maps = ∅ ∧ xs.length = m.size ∧
  m.size < 2 ^ 62⌝`; `Api.lean`'s docstring. **Broken, U11g**: `Open/FileFacts.lean:47-54`: `have
  hsz : m.size < 2 ^ 62 := hml.2.2` (the `sorry` goes), and `hml.2` → `hml.2.1` at `:51`, `:54`.
  `DB.Close`'s proof must give the bound back (the writer side's `m.size < 2 ^ 63` is not enough;
  open, for its unit).
- **Item 6 (`f26a2ebb39`)**: `DB.Begin_err.spec`'s error branch `⌜err ≠ nil ∧ tx = null⌝ ∗
  fmtErrorOk err ∗ …`; `DB.beginTx.spec`'s error branch begins `⌜tx = null⌝ ∗ beginErr err ∗ …`,
  `DB.beginRWTx.spec`'s is `⌜tx = null⌝ ∗ beginErr err`; proofs and `DB.Begin` adapted. **For
  U11g**: `Open.lean`'s `DB.Begin_err.spec_w` can go: `hBegin` becomes `DB.Begin_err.spec` at `w =
  true` (`wp_apply hBegin db γ true (fun _ => emp)`; its pre's `if` is `emp`, the post's `∃ D,
  boltTx …`; the error branch `⌜err ≠ nil ∧ tx = null⌝ ∗ fmtErrorOk err ∗ emp`).
- **Item 7, `fs.FileMode.String`: not landed (checked, then reverted).** `io/fs` is this
  repository's (project `bboltfs`, not Perennial's). Adding `"FileMode.String"` to
  `Code/io/fs.toml`'s `translate` list and `etc/goose.py --project bboltfs` translate it (only
  `Code/io/fs.lean` changes: `FileMode.String.impl`, and `FileMode.TypeAssumptions` gains
  `String_unfold`/`ptr_String_unfold`); `etc/goose.py --check --project bboltfs` passes. Reverted
  because `Code.io.fs` is imported by every project (`os`), so the change rebuilds the whole tree
  for every agent in the shared worktree: land it when a full rebuild is acceptable, with the
  proof. The proof of `Open/FileModeString.fs.FileMode.String.spec` (`{{True}} … {{s, RET #s;
  True}}`): two `wp_string_for_range` loops (Perennial `Golang/Theory/String.lean`) over the
  constants `"dalTLDpSugct?"` (13 runes) and `"rwxrwxrwx"` (9), invariant `w ↦ W64 n` with `n ≤ i`
  (first loop), `n ≤ 14 + i` (second; the `w == 0` step adds one), and `buf ↦ ` any `[32]byte`, so
  every `buf[w]` is in bounds (`w ≤ 22 < 32`); then `string(buf[:w])`. Then U11g's `hModeStr`
  (`Open.lean:270`) is discharged.

### Maintainer 12's hand-off (2026-11-04): what is left

1. Item 7 (above): land the translation with the proof, at a moment a full rebuild is acceptable.
2. Item 3's `sorry` (`Tx__write_ext.lean`, the past-the-end case): a unit (Commit/Write*, idle).
3. `commitFreelist`'s post clause (U10k, above); the four `pcStepX_bufsOK` clauses: proved by U9w5 (`9034f79cb2`).
4. U11g: the item 1, 5, 6 changes above (`Open/Core`, `DB__loadFreelist`, `Open/FileFacts`,
   `Open.lean`'s `spec_w`).
5. `DB.Close`'s `fileHolds` must give `m.size < 2 ^ 62` (D-I).
6. Interfaces and the TCB baseline at integration.
- Open `sorry`s added by maintainer 12: `Tx__write_ext.lean` ×1 (U10-style unit),
  `Spill/PcStepBufs.lean` ×4 (U9w4). Removable once U11g applies item 5: `Open/FileFacts`' `hsz`.

## Shared-statement fixes, the coordinator's queue for maintainer 13 (2026-11-04)

- **Item 1 (`d64ce6258c`; decision D-J): U4e's three `wdbOK'` gaps, proved.** `wdbOK`/`wdbOK'` end
  `… ∧ (∀ s, 4096·s < size → size < 4096·(s+1) → size - 4096·s ≤ |wb s|) ∧ 0 ≤ w.fd.toInt`;
  `flClause true w` is `∀ f, flpg = some f → 16 ≤ |wb f| ∧ flCurOKr …`. The brief's
  "`|wb s| = 4096` for every slot the file reaches" is false at `Open` (`openWb` is unpadded), so
  the partial-page clause is the weaker one `DB.grow` needs. `W`'s bound is **not** rounded up: the
  maxMapSize corner cannot occur (`Mmap/GrowWdb.wCells_aligned`: `wCells`' partial last cells of a
  `0xFFFFFFFFFFFF` mapping would lie past `maxAddr = 2^47`), and `wdbW'_grow_acc` now gives
  `mapLen w.ms % 4096 = 0`. `Mmap/GrowPure`: `wdbOK'_flHdr`, `wdbOK'_partSlot` (now with `b L hms
  hal`), `wdbOK'_fd` proved; `wdbOK'_grown` takes `hpart'` (the new size's partial page);
  `GrowEnd.grown_W_sub`/`grow_finish`/`grow_finish_same` take `hal`. `DB.grow`'s proof has no
  `sorry` left. `DB.loadFreelist.spec_open` takes `0 ≤ fd.toInt` (after `lfOK`); `wdbOK_open` takes
  `hfd`. Adapted: WdbFlag, WJoin, Publish, RemapEnd/Lost, Rollback{Facts,Flag,Reload}, WRelease,
  WRoll, CoreFacts, DB__loadFreelist, DB__grow.
  **Broken, active**: (U11h) `Open.lean:723-724`: `wp_apply hLoad … (openOK_lfOK …) Hfd.2 $$ …`
  (`Hfd` from `OpenFile`'s post, `%Hfd` at :438; `Hfd.2 : 0 ≤ fd.toInt`). (U10l)
  `Commit/TailAcc.lean:62-68` (`wdbOK_reslot`): bind `h16, h17` and give `…, ?_, h17⟩` with a new
  premise `hpart : ∀ s, 4096·s < m.size → m.size < 4096·(s+1) → m.size - 4096·s ≤ (wb s).length`
  (callers: the written file is grown to page ends, or unchanged with `wb` kept on the partial
  page); `Commit/TailPub.lean:107,134,197`: `hok.2^14` is now a triple, use `hok.2^14.1`, and
  `:134`'s constructor needs the two new clauses.
- **Item 3 (`1026f0d7c3`; D-J): `tx.meta`'s positive address.** `wtxCore`'s facts end `… ∧ txRoot tx
  ≠ null ∧ 0 < X.t.t.meta'.addr` (and `Spill/NodeSpillSplitObjs.splitFr`'s copy); `wtxFrac`'s facts
  `… ∧ txRoot tx ≠ null ∧ 0 < X.t.t.meta'.addr ∧ wrFacts X`. Source: `Txn/MetaAlloc.Meta.wp_alloc_pos`
  (a local copy of Perennial's test-example `struct_wp_alloc_pos`; `notes/perennial-changes.md`),
  used in `Txn/Init.wp_Tx_init`, whose post ends `∗ ⌜0 < m.addr⌝`; `DB__beginRWTx` records it.
  **For U10l**: `Tx__Commit_err.lean:829`'s `haddr` is `Hr.2.2.2.2.2` of `wtxCore`'s facts
  (`(Xt.clearPages pml).t.t.meta' = X.t.t.meta'` by `rfl`/unfolding, as `managed'`); the step
  lemmas keep it as they keep `managed'` (`by unfold WX.setNode; split <;> exact Hr.2.2.2.2.2`).
- **Item 2 (`8d9ac5806e`): `posShape`'s per-entry tuple** gains `(bl = X.rl → leafFlags pg i % 2 =
  bucketLeafFlag → ∀ bpg, bktLeafPg X.v.pages (leafValue pg i) bpg → ∀ j < pageCount bpg, …)`.
  Producers adapted: `Txn/WInit` (from `rootShape`'s fourth clause), `Rebalance/RblXShape`
  (`rw [hv] at ho hp ⊢`), `Write/MatOK.hps'`, `Write/RootKeys` (`.2.2.1`); U9x9 adapted
  BktRootKeys/BktLoopPureStart (`a8146a88ea`). **Not done**: the three consumers' `sorry`s
  (`Rebalance/RblMat.lean:518`, `Read/WOpenOK.lean:252,351`, `Write/MatOK.lean:475,696,699`). Plan
  for `RblMat:518`: `mat_clean` takes `hnest : pageFlags pg = leafPageFlag → ∀ j < pageCount pg,
  leafFlags pg j % 2 = bucketLeafFlag → ∀ bpg, bktLeafPg W.pages (leafValue pg j) bpg → ∀ k <
  pageCount bpg, leafFlags bpg k % 2 = 0 ∧ 0 < leafKsize bpg k ∧ leafKsize bpg k + leafVsize bpg k
  ≤ bboltEntryMax`; the `sorry` is `fun _ bpg hb => hnest hfl j hjc hbk' bpg hb`; `rbl_nodeAdded`
  (`RblMat:1092`) passes it through as a premise, and its caller (`RblXSMat`, with `hPS` and the
  page position `hposw`, as for `posShape_rootLeaf`) and `MatOK:1027,1213` derive it from
  `posShape`'s new clause (`bl = X.rl` from its first clause and `hbk'`). `WOpenOK.leafBkt_nest_plain`:
  a view page's entry by `posShape`'s new clause, a node's entry by `bvalOK`'s third clause.
- **Item 4 (decision D-K): Option A**, decided, not threaded: the new mark's pages are always
  written (Go's `tx.pages` keeps every allocation until `tx.write`, which writes them all), so
  `wdbOK`'s clause 3 is kept. The vehicle `markCov X hwm := ∀ s, hwm ≤ s → s < X.t.mv.pgid'.toNat →
  s ∈ bufSlots X.t.bufs` (D-K) is to be carried by `Bucket.spill.spec`'s and
  `Tx.commitFreelist.spec`'s success posts and `cmPubPre`, and used by `cm_pub_ok`. Not started (a
  change to U9x9's and U10l's statements: schedule it with them).
- **Item 5: nothing to do** (D-I amended): `DB.Close.spec`'s post is `True` (D9), nothing gives
  `fileHolds` back.
- `FileMode.String`: not landed (as briefed).

- **Item 2's consumers: closed** (helper, `192f776872`, `5fb5f557e7`, `5bce40e503`, `49074fa526`):
  new `Write/BoundNest` (`matNest`, `viewWF_matNest`: a well-formed view's bucket entries' leaves
  are plain, from `viewWF` alone); `mat_clean`/`matR_clean` take `hnest : matNest W.pages pg`
  (callers in MatOK pass `viewWF_matNest`); `newNodeBnd` takes `hbk`, `hkb` (from `posShape` and
  `pageKeys_le_of_treeKeysN`); `Read/WOpenOK.leafBkt_nest_plain` takes `hbm : B.bm !! w.key = none`
  (unused). Six `sorry`s gone (RblMat ×1, MatOK ×3, WOpenOK ×2).
- **Queue (a) (`e1482ab309`): `Bucket.spill.spec`** takes `markCov X w.C.hwm` (after `X.t.mv.txid'.toNat
  < 2 ^ 63`), and its success post's pure conjunction ends `… ∧ X'.t.mv = {X.t.mv with pgid' := …} ∧
  (∀ s ∈ treeSlots (spillC X' w.C.pages), s ∉ pendSlots w'.fl) ∧ markCov X' w.C.hwm` (the last two
  are new, after the old last conjunct). `markCov` moved to the new `Commit/MarkCov`
  (`markCov_of_eq`: vacuous at the committed mark); `Commit/TailPub` imports it.
  **For U9x10** (`Bucket__spill.lean:109`, `Spill/BktEnd*`): prove the two new conjuncts (the spill
  frees only base pages it rewrites, so a kept base page's slots are not pending; `markCov`: the
  mark moves only by `allocRes`'s mark case, which adds the run `[pgid, pgid + count)` as a buffer of
  overflow `count - 1`, and `bufs` only grows, ids and overflows kept). **For U10m**
  (`Tx__Commit_err`): pass `markCov_of_eq X w.C.hwm h` to `wp_spill` (the mark is `w.C.hwm` at the
  spill's start, `cmTailOK`'s `w.C.hwm = opg.toNat`); the success pattern gains two names after the
  `X'.t.mv` conjunct (the OPEN notes at :582, :584, :699, :702). Still to do:
  `Tx.commitFreelist.spec`'s post carrying `markCov` (its allocation), U10m's.
- **Queue (b): `Tx.write_ext.spec`** takes `hpart : ∀ s ∈ bufSlots bufs ++ T, 4096 * s < om.size →
  om.size < 4096 * (s + 1) → om.size - 4096 * s ≤ (wb s).length` (after the whole-page premise;
  `wdbOK`'s D-J clause gives it). `Tx__write_ext` keeps its `by_cases`: `Tx.write_ext_gen`'s `hstr`
  (`4096 * s < om.size → om.size ≤ 4096 * s + |wb s|`, no upper bound) is false for a target slot
  wholly inside the file, so `write_ext_gen` cannot be used directly; `write_ext_straddle` stays
  until `hstr` is weakened to `hpart`'s form inside `WriteExtRun` (its use is at the straddling
  slot). The post's new facts are **not** added: they do not follow from the post (they need
  `WriteExtRun`'s run invariant), and `size' = size ∨ size' % 4096 = 0` is **false on the error
  branch** (`os.File.WriteAt` may write a prefix of a chunk before failing, and a page over
  `MaxAllocSize - 1` bytes is written in several chunks): it belongs to the success branch only.
  Both and the weakening are one `WriteExtRun` edit (~24 min per elaboration). **For U10m**
  (`Commit/TailWrite.cm_write_step`): pass `hpart` from `wdbOK`'s clause 16.

- **Synced-freelist queue (U10m/U10n) and `bktNested`'s ipg clause: checkpoint, not landed.**
  Item 4 landed (`4824c8a91b`: `fbRec`/`fbRec_lookup` in a pure section of `Inv/Store`; U10m:
  replace `Commit/FreeFlPure.ff_fbRec_lookup`'s use at :190, delete the copy). **Item 1 blocked**:
  no public clause gives the freelist page's header id at `Open` (`Inv/FileHolds.flFileOK` says
  nothing of `pageId (filePage xs f)`; Go's `freelist.Read` does not check it): `flFileOK` must
  gain it first (behind `fileHolds`: the coordinator's decision; producers `fileHoldsDef_new`,
  `Open/InitImage`). **Items 2, 3 and 5 written, reverted to scratch** (they broke other units
  while uncommitted): the patch `/home/ubuntu/.claude-E/jobs/e232d4e0/tmp/m13/m13_items.patch`
  (`git apply` from the worktree root; 21 files), the new module `…/m13/FreeFlOK.lean` (→
  `Commit/FreeFlOK.lean`), the leaf targets `…/m13/m13_targets.txt`. Contents: `flCurOK`'s and
  `flCurOKr`'s 13th clause `∀ a, fl.allocs !! W64 f = some a → a.toNat ≤ C.txid`; `flCurOKr`'s slot
  clause `¬ coversSlot … ∧ s ∈ pendSlots fl ∧ W64 s ∉ fl.free ∧ ∀ t pd, … → t = wtx`;
  `flCurOK_flCurOKr` deleted; `wdbOK_wdbOK'`, `wdbW_wdbW'`, `wdbLost_wdbLost'`, `wtxEnd_wtxEnd'` at
  flag `false` only (callers `Tx__Commit_err:492,506,515,742` drop the argument); `flClause_alloc`,
  `wdbOK_alloc`, `wdbOK'_alloc` take `hr : r ∈ w.fl.free`; new `Commit/FreeFlOK.wdbOK'_free_fl`
  (Tx__Commit_err:1092), `flAlloc_ne_wtxid` (`cm_free_fl`'s `hal`), `wdbOK'_true_extPend`
  (`TailFPure.flExtPend_of_true`); `cmPubPre_commitFl` takes `hal4` (Tx__Commit_err:583 passes
  `Hcf4.2.2.2.2.2.2`); `FreeFlPure.freeFl_ok:167`'s flagged part becomes `wdbOK'_free_fl w f hok
  hf`. `bktNested`'s last clause `(C.ib.root' = W64 0 → C.bv.rootNode' = null → C.ipg = inlinePage
  v)`: RblXSSim/RblXSKill/RblXMg/RblXSCol/RblXSRm fixed in the patch; open: `Write/MatOK:241`,
  `Spill/DerefWOK.bktNested_step` (`(bktStep_fields hsC).2.2.2.2.1`), `Read/WOpenWOK:459`
  (`bktOpened`: `inBucketRoot_zero`). **To land**: apply, finish item 5's producers, build the
  targets in one go, land U10m's three call-site edits with it (a quiet window or a coordinated
  hand-over of `Tx__Commit_err`, `FreeFlPure`).

### Maintainer 13's hand-off (2026-11-04): what is left

0. Land the scratch patch (synced-freelist items 2, 3, 5; above), after the coordinator decides item 1 (`flFileOK`'s header id).
1. U11h's `Open.lean:723` (`Hfd.2`) and U10l's `TailAcc`/`TailPub` adaptations (item 1, above);
   until then `Commit/Tail*`, `Commit/Pub*`, `Tx__Commit_err` and `Open` do not build.
2. Item 2's consumers: done (above). `WriteExtRun`: weaken `hstr`, add the post facts (queue (b)).
3. Item 4's threading (`markCov`, D-K).
4. Perennial: move `struct_wp_alloc_pos` to `Golang/Theory` (`notes/perennial-changes.md`).
5. Interfaces and the TCB baseline at integration (`DB.grow`'s three `sorry`s gone).
- Open `sorry`s: none added; removed: `Mmap/GrowPure` ×3.

### Maintainer 14 (2026-11-05): landed, and the hand-off

Landed (each built over the importers that name what changed, then committed and pushed):
- **`efa69ca1ae`, maintainer 13's synced-freelist patch** (its items 2, 3, 5, above), with the
  `bktNested` ipg clause's producers: `Write/MatOK` (`wOK_matX` takes `hipg : B'.ipg = B.ipg` after
  `hrn`), `Spill/DerefWOK.bktNested_step` (`bktStep_fields`), `Read/WOpenWOK` (`openedRec`'s ipg,
  `inBucketRoot_zero`; `XO_bs_old` also gives `D.ipg = D0.ipg`). Consumers adapted: `Spill/BktVal`,
  `RblXSSim`/`RblXSKill` (`hfwd` patterns), `RollbackReload:81`, `Mmap/Alloc:695` (`hcan.2.2`).
  U10n's call sites in `Tx__Commit_err` (the `false` arguments dropped, `hal4`), `FreeFlPure`
  (`wdbOK'_free_fl`, Inv/Store's `fbRec_lookup`). Also fixed `DerefWOK.posShape_step`, broken
  before (`rw [.., h.1]` for the view in `posShape`'s `bktLeafPg` clause).
- **`513b552934`, D1**: `gensOK`'s third clause `∀ b n, X.handles !! b = some (n, T.gen n) →
  bktLoc X n = some b`; `gensOK_handle_bktLoc` (`h.2.2`) in `Inv/Tx` (Bucket__Get's `sorry` gone:
  `Bucket.Get/Put/Delete` close); `gensOK_bktOpened` takes `hnr : bl ≠ X.rl → g < T.gen name`
  (callers open from the root); `gensOK_dropBkt` by `gensD1_dropBkt`. The second clause is `.2.1`.
- **`daa0817af4`, item 2 (D-L, `notes/bbolt-spec-decisions.md`, for the user's review)**:
  `flFileOK` (behind `fileHolds`; `Api.lean`'s docstring) gains `pageId (filePage xs f) = f`;
  `flCurOK`/`flCurOKr` end `… ∧ pageId pg = f`; `Commit/FreeFlOK.wb_pageId` gives `pageId (w.wb f)
  = f` (`cm_free_fl`'s `hid`, U10n's to use).
- **`a8c4c7689b`**: `Inv/ShapeOps.toList_insert_perm` → `toList_insert_perm_gm` (it clashed with
  `freelist/Lemmas/Model`'s); `Write/CreateBktWp` uses `Mmap/TxAlloc.wtxW_db_acc` (U7l's copy gone).

**Not started, the next maintainer's (both decided by the coordinator; both block DeleteBucket):**
1. **(A) a dead bucket's nil node cache** (U7j: after `child.nodes = nil` the bucket's `↦$` is
   unprovable, `ownMap_not_nil`). The coordinator's form `(if B.bv.nodes' = null then ⌜B.nm = ∅⌝
   else B.bv.nodes' ↦${dq} B.nm)` for every bucket would break `Read/WCtx.wtxW_nodes_nonnull` and
   `wtxW_nm_acc` (their only source of `nodes' ≠ null`, used by PutWp:408, DelWp:415,
   CreateBktWp:414, CreateBktIfWp:549, Bucket__spill:285/469, Walk:312). `objOwn` cannot tell a
   `deadB` entry from a `bs` one (`wtxHeap` maps `bobjs = bs ∪ deadB` with the `liveB` flag only),
   so per the coordinator's decision take the **heapOK route**: `heapOK` gains `∀ bl B, X.t.bs !!
   bl = some B → B.bv.nodes' ≠ null`, `objOwn`'s nodes clause takes the if-form, and
   `wtxW_nodes_nonnull`/`wtxW_nm_acc` (`Rebalance/BktRbl`; copy of the bucket case in
   `Rebalance/NodeRblBase.objOwn_bkt_unf`) read the fact from `heapOK` (callers unchanged).
   DeleteBucket moves the child from `bs` to `deadB` before `child.nodes = nil` (Go:
   `delete(b.buckets, key)` precedes it). Every `heapOK` producer (about 51 files mention `heapOK`;
   `heapOK_step`, `heapOK_setNode`, `heapOK_of`, `heapOK_rebase`, AllocBase:118, …) adds the clause
   (a bucket's `bv` kept, or a fresh writable `openBucket`, whose `nodes` is `make`'s). Scratch for
   the objOwn half: `/home/ubuntu/.claude-E/jobs/e232d4e0/tmp/m14/objown_scratch.patch`
   (`nodesOwn_ne`, `NodeRblBase.nodesOwn_of_map`). Build the leaves of
   `etc/importers.py --leaves Proof/go_etcd_io/bbolt/Inv/WtxHeap.lean` (40) in one window.
   Cheapest placement (maintainer 14's estimate: `heapOK` has ~106 mentions in ~51 files, most
   pass-through): fold the fact into `heapOK`'s third clause, `B.bv.tx' = tx ∧ B.bv.nodes' ≠ null`,
   so producers that move it by `rw [hbv]` keep working; consumers of the equality take `.1`; only
   fresh buckets (`bktOpened`, `Txn/WInit`) and field-level proofs need new work.
2. **(B) `bktNested` gains, per opened child entry, `bvalOK vw.pages T.mv.pgid'.toNat v` and
   `inBucketRoot v ≠ 0 → treeKeys vw.pages (inBucketRoot v) none none`** (U7j). Producers: opening
   (`Read/WOpenWOK`: `hbv`, `htk` are already in `wOK_XO`'s premises), `Write/MatOK` (the mark may
   grow: needs `bvalOK` monotone in the mark), `Spill/DerefWOK`, `RblXSSim/Kill/Mg/Col/Rm`; spill
   breaks them where it breaks `C.ib.root' = (ibOf v).root'`. Append after the ipg clause and fix
   the users that name the ipg clause (`MatOK` `hipg2`, `DerefWOK` `hp`, `WOpenWOK` `hip0`,
   `RblXSSim`/`RblXSKill` `hipg`), as in `efa69ca1ae`.
3. Maintainer 13's items 2–5 (above) stand: `WriteExtRun`'s `hstr`, `markCov`'s threading, the
   Perennial move, interfaces and the TCB baseline at integration.
- Known breakages not mine at hand-off: `Tx__Commit_err:455` (`cmTailOK`'s new Bool argument,
  U10n's uncommitted `Commit/TailDefs`), `Write/Retarget:219` (a unit is on it).
- Open shared `sorry`s: none added; removed: `Bucket__Get.gensOK_handle_bktLoc` (D1).

### Maintainer 15 (2026-11-05): landed

- **(A), a dead bucket's nil node cache (heapOK route, decided by the coordinator for U7j).**
  `Inv/WtxHeap.objOwn`'s bucket clause holds `(if B.bv.nodes' = null then ⌜B.nm = ∅⌝ else
  B.bv.nodes' ↦${dq} B.nm)` (`nodesOwn_ne` rewrites it to the map when not nil;
  `Rebalance/NodeRblBase.nodesOwn_of_map` folds a map back); `heapOK`'s third clause is
  `B.bv.tx' = tx ∧ B.bv.nodes' ≠ null` for every bucket of `X.t.bs` (a consumer of the `tx` field
  takes `(hok.2.2.1 bl B hb).1`). `Rebalance/BktRbl.wtxW_bs_nodes_ne`/`Read/WQ.wtxWQ_bs_nodes_ne` read
  the fact; `wtxW_nm_acc`/`wtxWQ_nm_acc` (and so `wtxW(Q)_nodes_nonnull`) have their statements
  unchanged. Producers: `Txn/Heap.wtxHeap_bkt_acc`'s premise is `B'.bv.tx' = tx ∧ B'.bv.nodes' ≠
  null`; `Rebalance/HeapRbl.heapOK_of`'s `htx`, `wtxHeap_setBkt_acc`'s and `_live_acc`'s, and
  `Write/NodeAdd.wtxHeap_nodeAdd_acc`'s field premise is `B'.bv.tx' = B.bv.tx' ∧ B'.bv.nodes' =
  B.bv.nodes'` (callers `⟨rfl, rfl⟩`); `Read/WOpenH.wtxHeap_addBkt` takes `hnn`, `wtxW_bktOpen`'s
  pure premise ends `∧ C.bv.nodes' ≠ null`; `Read/WOpen.openedRec` ends `∧ C.bv.nodes' ≠ null`
  (`Bucket.openBucket_w`: `make`'s map, `ownMap_not_nil`); `Txn/WInitH.wtxHeap_wx0` (the root's
  `make`). Code that uses the map (`Bucket.node`'s insert, `node.rebalance`'s deletes) rewrites the
  clause with `nodesOwn_ne` and folds it back with `nodesOwn_of_map`.
  **DeleteBucket** (a later unit) moves the child from `X.t.bs` to `X.t.deadB` before
  `child.nodes = nil` (Go: `delete(b.buckets, key)` precedes it): a `deadB` bucket's `nodes'` may
  be nil, and its `objOwn` then holds `⌜B.nm = ∅⌝`.
- **(B), `bktNested` per opened child entry (U7j)**: after the ipg clause, `bvalOK vw.pages
  T.mv.pgid'.toNat v ∧ (inBucketRoot v ≠ 0 → treeKeys vw.pages (inBucketRoot v) none none)`.
  Opening gives both (`Read/WOpenWOK.wOK_XO`'s `hbv`, `htk`); `Spill/DerefWOK.bktNested_step`
  (`h.1`, the step's `mv`), `Write/MatOK`, `Rebalance/RblXSSim`/`RblXSKill`/`RblXSMat` carry
  them (view and mark unchanged; no `bvalOK_hwm` was needed); `Spill/BktEndOld.cachedNil_ipg`'s
  pattern takes a `-` more. Spill breaks them where it breaks `C.ib.root' = (ibOf v).root'`
  (`bktNested` is not kept through spill). Users that destructure the clause name the ipg clause
  then the two new ones (`hip0, hbo0, htk0`).
- Not built in (B)'s window, at the coordinator's request (U10w2's `WriteExtRun` compile of
  record): `Tx__write_ext`, `Tx__Commit_err`, `Tx__Commit`, `Commit/FreepagesLink`; they name
  neither `bktNested` nor `heapOK`'s third clause directly, but check them at integration. The
  open-sorry inventory below is unchanged by maintainer 15 (none added or removed).

## Writer reads at a fraction (U6w, 2026-11-05)

**The cause** (found by the coordinator). The public read triples (`Bucket.Get`, `Bucket.Cursor`,
`Cursor.First/Next/Last/Seek`) hold at any fraction `q` of either kind of transaction. The
invariant design had this right: `boltTxDef`'s writer branch holds `wtxFrac B tx r q T X` (the
heap, fills and registries' auths at `q`, the view cells at `q · wq`, the mapping fields at
`q · ¼`), and design review 1 checked the writer's `Get`/`Cursor` at a fraction (`pageNode`,
`b.nodes` and `tx.pages` are only read). U0b's contracts then stated *every* internal writer spec
over `wtxW` (`wtxCore` at `1`), the read-only ones included, so `boltTxDef_wtxW` (at `q = 1`) was
the only way in and the writer case of the public reads was unprovable. Batch 37 flagged it,
deferred it to U6f, and it was never followed up.

**The fix** (U6w):
- `Inv/Ctx`: `wtxCoreQ K tx r m q X` and `wtxWQ K tx r m q X` (every `1` of `wtxCore`/`wtxW` at
  `q`, the view cells at `QpMul q wq`, the mapping quarter at `QpMul q ¼`); `wtxCoreQ_one`
  (`rfl`) and `wtxWQ_one : wtxWQ … 1 X = wtxW … X`; `boltTxDef_wtxWQ` (a writer's `boltTxDef` at
  `q` is `wtxWQ` at `q` with `wtxFrac`'s facts, its agreed state's `q.half` and the data's
  `QpMul q ¼`). `wtxCore`/`wtxW` are unchanged definitions (their users unchanged). No splitting
  is needed inside the reads (each takes `wtxWQ` at `q` and gives it back whole); the split is
  `boltTx_fractional`'s (`boltTxDef_fractional`, proved), so no `ownMap` fraction lemma was needed.
- The read-only writer specs gain a `specQ` (over `wtxWQ` at any `q`, given back unchanged) in
  the same spec file; `spec` (over `wtxW`) stays, proved as `specQ`'s case `q = 1` (`wp_proof`
  from `wp_proofQ` by `wtxWQ_one`), so the write path's callers are unchanged.
  `Read/WQ` holds `wtxWQ`'s accessors (the `wtxW_*` accessors at `q`).
- Also (the coordinator's decision on maintainer R's proposal): `hdlAuth r q H` (the handle
  registry's auth at `q` with every handle's persistent fragment, `hdlFrags`, moved from
  `Read/WKey` to `Inv/Tx`) replaces the bare auth in `wtxCore`, `wtxCoreQ` and `wtxFrac`
  (fractional: `hdlAuth_fractional`); `wtxW_bktOpen` adds the new fragment, `beginRWTx` starts
  from `hdlAuth_of_empty`; `Bucket.Bucket_w` no longer takes or gives `hdlFrags`
  (`Read/WQ.wtxW_hdlFrags`).
- `nsearch_n`, `search_w`, `seek_w`, `keyValue_w`, `pageNode_w` have their `specQ`; `wp_proof` of
  `search_w`/`seek_w` take their callees' `specQ`s.
- **F2 (the contracts review): a writer's view at a fixed key.** `viewOf r v` is `null ↪[r.n.vw]□ v`
  for both kinds (a writer's base view, minted by `beginRWTx`: `wr_names_alloc` inserts it beside the
  base-keyed one), so a cursor's, handle's or slice's view agrees with the writer's `X.v`
  (`Read/TxBytes.viewOf_agree`). `viewBase r v` (`v.base ↪ v`) is what `wtxCore`/`wtxCoreQ` hold and
  a remap re-bases (`Mmap/Remap*`, `wtxCore_viewOf_rebase` now takes `b ≠ null`); `wtxFrac` holds
  both (`viewW`); `boltTxDef_wtxW`/`_wtxWQ` give `viewOf r X.v` as a separate conjunct after
  `K.full`. `vwOwn`'s clause: every entry is `{v0 with base := u.base}`, at its key but `null`.
  `txBytesDef_acc` (was `sorry` in `Inv/Tx`) is proved in `Read/TxBytes` (imported by
  `Inv/FileHolds` for `Api.txBytes_acc`), for both kinds.

## Open shared `sorry`s (inventory, 2026-11-04, maintainer 3; updated by maintainers 13, 14)

In `Model/`, `Inv/` (the internal specs' proof stubs `Proof/go_etcd_io/bbolt/<T>__<M>.lean` are the
units', per the U0b table):

| statement | module | owner |
|---|---|---|
| `discardLogger_boltLogger` | `Inv/Bolt` | U11 (bbolt's package facts for `discardLogger`) |
| `fileHoldsDef_timeless`, `fileHoldsDef_new`, `fileHolds_decode` | `Inv/FileHolds` | U11 |
| `boltTxDef_fill`, `txBytesDef_acc` (`boltTxDef_fractional` proved, batch 37.15) | `Inv/Tx` | U5 (U12 for the laws' users) |
| `flView_cover` | `Model/WOps` | U8b |
| `wtxCore_viewOf_rebase` (gap 3): proved (37.3); `fmtErrorOk_errPtrTyped` (U11g's last user) | `Mmap/RemapGaps` | U11g |
| `boltCurDef_timeless` (a case) | `Inv/Tx` | U12 |
| `flView_canFree`, `flView_nodeFree` | `Model/WOps` | U8b |
| `treeData_spill` | `Model/LTree` | U9c |
| `metaOk_parity_write` | `Model/Meta` | U10 |
| `Tx.write_ext.wp_proof`'s past-the-end case (maintainer 12, item 3) | `Tx__write_ext` | a Commit/Write unit |

(Maintainer 14, 2026-11-05: rechecked, the `Model/`/`Inv/` `sorry`s are `Inv/Tx.boltTxDef_fill`,
`Model/LTree.treeData_spill`, `Model/WOps.flView_canFree`/`flView_nodeFree`; `Bucket__Get`'s
`gensOK_handle_bktLoc` is gone with D1.)

Maintainer 3's queue (C(1), C(4), E) is done in batch 30 above.

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
11. **The checksum is `fnv64a : List w8 → w64`**, not a parameter of `metaValid`: the parameter
    would thread through every predicate. *(Superseded, infra 5a/5b, `cd62a713dd`: `fnv64a` is
    `hash.fnv.fnv64a`, the real FNV-1a 64 of the translated `hash/fnv`, and `Meta.Sum64` is
    proved; U0a's was an uninterpreted `opaque`.)*
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
- `Meta.Sum64` is proved over `hash/fnv`'s FNV-1a 64 specs (infra 5b, `cd62a713dd`).

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

No unit waits on another's proof. (§5's item 0, `WriteAt` at any length, landed: infra 3,
`3d30fe6b6f`, premise `off.toNat + data.length < 2^63`, no 1 GiB limit.)

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
- **R3. Commit's error paths (U10).** Round 3: A1's `WriteAt` generalization (§5, item 0; landed,
  infra 3: premise `off.toNat + data.length < 2^63`, no 1 GiB limit) was needed first, since `tx.write`'s chunks reach `0x7FFFFFFE` bytes (a leaf of four maximal entries, or
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

