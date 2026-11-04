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

## Open shared `sorry`s (inventory, 2026-11-04, maintainer 3)

In `Model/`, `Inv/` (the internal specs' proof stubs `Proof/go_etcd_io/bbolt/<T>__<M>.lean` are the
units', per the U0b table):

| statement | module | owner |
|---|---|---|
| `discardLogger_boltLogger` | `Inv/Bolt` | U11 (bbolt's package facts for `discardLogger`) |
| `fileHoldsDef_timeless`, `fileHoldsDef_new`, `fileHolds_decode` | `Inv/FileHolds` | U11 |
| `boltTxDef_fractional`, `boltTxDef_fill`, `txBytesDef_acc` | `Inv/Tx` | U5 (U12 for the laws' users) |
| `boltCurDef_timeless` (a case) | `Inv/Tx` | U12 |
| `flView_canFree`, `flView_nodeFree` | `Model/WOps` | U8b |
| `treeData_spill` | `Model/LTree` | U9c |
| `metaOk_parity_write` | `Model/Meta` | U10 |

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

