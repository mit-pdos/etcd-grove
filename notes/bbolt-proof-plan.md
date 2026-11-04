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
5. *(open, with batch 14)* every bucket the root or a handle's, in `heapOK`.
6. **`node.size.spec`** has no `insSize ins < 2^63` premise (the sum wraps the same on both
   sides); U9a's proof, `Bucket.write`'s and `node.rebalance`'s calls adapted.
7. **`nodeAdded`** adds `∀ w ∈ r.ws, isBktFlag w.flags → w.vs = Src.view ∨ w.vs = Src.own
   DFrac.discard` (after batch 13's two clauses; patterns get `hrvs`) and, in the child case,
   `rp'.capOwn = rp.capOwn` (after `rp'.ksrc = rp.ksrc`). `r.nv.key' ≠ nil` when `r.ws ≠ []` is
   batch 13's `↔`. `Bucket.node` (U7) establishes them from `node.read`'s `pageWsAs pg (posSrc B)`.
8. **`flView_canFree`/`flView_nodeFree`** (stubs, U8b) take `viewWF X.v` (and the latter `covU X`)
   in place of `wOK X`.
9. *(open)* the shared `matReady` lemma for a view page from `wtxW`'s mapping fields.

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

## Batch 14 (kind-keyed heap objects, U7's finding): design, not yet applied

The writer heap's single object map keyed by location cannot show a fresh node location is no
bucket's (`structFieldRef` is abstract for non-plain structs; Perennial proposal in
`notes/perennial-changes.md`). Planned shape:
- `WTx.objs` folds only the nodes (the buckets' `ns` over `dead`, which holds dead nodes only); a
  new `WTx.bobjs` is the buckets (`bs` over a new `deadB : GMap Loc BRec`, default `∅`).
- `WX` gains `liveB : GMap Loc Unit` (bucket liveness): every bucket-sense `l ∈ X.live` (`liveOK`'s
  root and `bs` clauses, `liveReach`'s bucket clause, `derefPre`'s bucket clauses, `bktOpened`,
  `bktLocalOK`, `derefStep`/`derefRel`) moves to `liveB`; `X.live` is node liveness. (One shared live
  set is unsound here: killing a node at `l` would un-live a bucket at `l`, opening a bucket at `c`
  would revive a dead node at `c`.)
- `wtxHeap`: `[∗map] l ↦ o ∈ X.t.objs, objOwn … (l ∈ X.live) o ∗ [∗map] bl ↦ B ∈ X.t.bobjs,
  objOwn … (bl ∈ X.liveB) (.bkt B)`; `objsDisj` keeps only "a node is in at most one bucket";
  `objs_bkt` becomes a lookup of `bobjs`; `heapOK`'s registry clause is about node objects, and
  (batch 20 item 5) every bucket is the root or a handle's.
- Users to adapt: `Inv/WtxHeap`, `Model/Wtx`/`WOps`, `Rebalance/{Objs,Heap,HeapRbl,RblXS*}`,
  `Write/Heap`, `Txn/Heap`, `Mmap/Rebase`, `Spill/{Deref*}`, `Bucket__pageNode_w`, `node__*`.

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

- **21 (approved by the user, 2026-11-04; D-C precedent, U5b's finding after batch 17)**: `txDB tx γ
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

