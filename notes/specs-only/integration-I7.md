# Integration I7: bbolt (batches 4c, 4d)

Directories: `SpecPlan/Spec/go_etcd_io/bbolt/` (public, internal, `Model`/`Api`/`Internal`/`Options`),
`SpecPlan/Spec/go_etcd_io/bbolt/errors/` (new), `SpecPlan/Spec/go_etcd_io/bbolt/internal/{common,freelist}/`;
snippets `examples/specreq/{bbolt,bboltinternal}/`. Done in three parts: the API-level items
(here), a sweep of 4c's specs that call `internal/common`, and a sweep of the freelist interplay
(both sweeps ran as forks of this agent; their changes are listed below).

Note: another agent's WIP commit `629824d06e` (4a's round 1) swept in most of these changes while
they were in progress. The rest are uncommitted in the worktree.

## Build

`etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/bbolt SpecPlan/Spec/go_etcd_io/bbolt/errors
SpecPlan/Spec/go_etcd_io/bbolt/internal/common SpecPlan/Spec/go_etcd_io/bbolt/internal/freelist`: **OK, 295
modules**. The backend's and schema's `Api` (importers of `Bbolt`) still build. `go vet
./specreq/bbolt/...` is clean. `bboltinternal/*.go` are gofmt-clean, and `go vet`-clean when
dropped into a copy of the pinned bbolt's `internal/common` and `internal/freelist`.

## Changes by file

### API level (this agent)

- **`errors/Api.lean` (new, namespace `BboltErrors`).** `errIs`, `isErr`, `bboltErrNames`, and the
  laws `errIs_init.spec` and `errIs_distinct.spec` moved here from `Bbolt`'s `Api.lean`. They are
  facts of `bbolt/errors`' initialization. `internal/common` (a dependency of `bbolt`) needs them
  for `Meta.Validate`, and it should not import its client's API. `Bbolt/Api.lean` imports the
  new file and re-exports the names (`export BboltErrors (errIs isErr bboltErrNames)`), so 4c's
  files are unchanged.
- **`internal/common/Meta__Validate.lean`.** The error is now `∃ g, ⌜metaErr v = some g⌝ ∗
  BboltErrors.isErr g err`, which means the same as before. The sketch cites
  `errIs_init`/`errIs_distinct`.
- **`req/go_etcd_io_bbolt_errors.md`.** New section "from I7" recording the move.
- **4c-D1 (the sector rule) stated consistently as the user's open decision, not decided.**
  - `Api.lean`'s `boltFile` header: the rule is not in OsFs's crash relation today; it would go
    there under (a) or into a crash premise under (b).
  - `boltCrash.spec`'s docstring: true only under (a) or (b).
  - `Tx__Commit.lean`: D9 is all-or-nothing in the page cache, not in a crash image; the crash
    case needs 4c-D1.
  - `Tx__writeMeta.lean`: cites the open decision and `BboltCommon.meta_in_sector`.
- **`Open.lean`.** `loadFreelist` calls `Read`, or else `Init(freepages())`, not `NoSyncReload`
  (4d review's note).
- **Stale law names in docstrings.** `boltState_wf` and `txSize_agree` do not exist (they are
  conjuncts of `boltTx_wf` and `boltTx_size`); fixed in `Api.lean` and `Model.lean`.

### Fork: 4c vs `internal/common`

Nine 4c triples could not be proved: seven were false as stated, and two were too weak for their
callers. All nine are restated.

- **`Internal.lean` additions.**
  - New field `TxCore.roots`.
  - Pure helpers: `InodeR.toM`/`ofM`, `NodeR.itemsM`, `nodeHdr`, `nodePage`, `nodeWritable`,
    `inlineOk`, `NodeR.emptyLeaf`.
  - Internal opaques: `emptyBkt`, `bktVal`.
  - Internal defs: `curSt`, `seekRaw`.
  - Laws: `wtxCore_keys`, `bktVal_persistent`.
  - `txPage`'s docstring lists what its realization keeps for 4d's page specs.
- **`node__write`** (false). Go asserts an empty header and panics on 0xFFFF or more inodes, on
  an empty key, and on a branch child equal to the page id. The pre now has `nodeWritable (hdrOf
  bs) N`. The post, which only kept the length before, is `nodePage bs N` (4d's `writeNode` after
  the header store).
- **`node__read`.** The post gives `N'.isLeaf` and `N'.inodes` from `pageItems`.
- **`Bucket__inlineable`.** The result is tied to the cached root.
- **`Bucket__write`** (false). A nil root panics. Restated for both callers (spill, and
  `CreateBucket`'s fresh bucket); the post is `encInBucket ib ++ nodePage …`.
- **`Bucket__openBucket`** (false). `&value[0]` panics on an empty value, and the value was not
  tied to the bucket. The pre is now `bktVal`.
- **`Cursor__seek_i`** (conflicted with `keyValue`). The fork's `seek` does not step past a leaf's
  end. Its post is now `curPath ∗ seekRaw`, and `Cursor__next_i` and `Cursor__node` take `curSt`.
- **`DB__pageInBuffer`** (false). It indexed out of range, and `init` could not call it. The pre
  is now the page size and an in-range index; the post is the element address.
- **`DB__init`, `DB__getPageSize`.** New premise `M.pageSize = 4096`. `init`'s sketch shows txid
  ≥ 1 (metas at txids 0 and 1).
- **`DB__getPageSizeFrom{First,Second}Meta`** (false). A readable but invalid meta returns `ok =
  true` with `ErrInvalid`. The 4096 promise is now on `err = nil`.
- **`Tx__forEachPage`.** New premise `txPage` (an id outside the snapshot reads past the mapping).
- **`verifyPageReachable`, `verifyKeyOrder`** (false: untyped `val` arguments, post `True`). Now
  typed, with the maps and keys owned and the premises for the no-panic case.
- **`Tx__writeMeta`, `Tx__write`, `Bucket__CreateBucket`, `Bucket__spill`.** Sketches name 4d's
  laws and specs: `Meta.Write`, `metaSummed`, `metaValid_summed`, `meta_withMeta`,
  `meta_in_sector`, `Pages.Len/Less/Swap`, `UnsafeByteSlice`, and the zeroed pool page.

### Fork: freelist

- **`DB__freepages`.** The post now gives `Freelist.idsOk ids`, the slice's capacity, and the new
  internal `dbUnreached db γ ids` (the ids are exactly the pages below the high-water mark that the
  tree does not reach). Without these, 4d's `Init` premises and the F1 premise of `NoSyncReload`
  could not be met.
- **`Internal.lean`.** Imports the freelist `Api`. A new block, "The freelist's side", defines
  `dbUnreached` and lists the invariants the opaque resources keep:
  - `readersOk` with `R.length < 2^62`;
  - `F.count < flMaxIds`;
  - `canFree` and `canRollback`;
  - **the reload invariant 4d asked for**: every free page is in the current meta's freelist ids
    or unreached by its tree, and none is pending.
- **`newFreelist`.** The post now gives `flOwn fl FLState.empty ∗ flReaders fl []`.
- **`node__free`.** The post now records `pgid := 0`.
- **`DB__allocate`, `Tx__allocate`.** The premise is now `0 < sint.Z cnt < 2^32`. `count` is an
  `int`, and `uint.nat` admitted negatives.
- **`Tx__Rollback`.** The sketch claimed `Rollback` frees the transaction's allocations. Go and
  4d's model only forget them (they leak until the next reload).
- **`Tx__rollback_i`.** The users list was wrong; the sketch is now complete, with F1 discharged.
- **Sketches only:** `DB__loadFreelist`, `DB__beginRWTx`, `DB__beginTx`, `Tx__close`,
  `Bucket__free`, `Tx__commitFreelist`, `Tx__Commit`.
- **4d's freelist: no change needed.** Each `array__<M>`/`hashMap__<M>` is `Interface.<M>.contract`
  at `arrayIface`/`hashMapIface`. `Interface.<M>.spec` is the same contract at `flCall`. The
  constructors' posts fit `flOwn_dyn`. The model was checked against `shared.go`.

## Known integration items

| Item | Status |
|---|---|
| `metaOf`, `pageItems`, `withMeta`, `metaValid_summed`, `writeNode_read` | Exist. 4c now uses them in posts (`node.read`/`write`, `Bucket.write`) and sketches. |
| `meta_in_sector` | Exists (`16 + 64 ≤ 512`); cited by `Tx.writeMeta`. |
| Freelist invariant for the hash map's `Init` premise (4d round 1) | Kept: `Internal.lean`'s freelist block, `DB.freepages`' `dbUnreached`, `Tx.rollback`'s sketch. |
| Page size exactly 4096 | `BboltCommon.init.spec` gives `DefaultPageSize = 4096`. `OptsM.ok` requires `pageSize = 0`. `DB.init`/`getPageSize` take `M.pageSize = 4096`. |
| `readersOk` (txid ≥ 1) | Met: `fileHolds`' txid ≥ 1 (`init` writes txids 0 and 1, the newest is 1), and the txid stays below `2^64 - 1`. **But see open item 1.** |
| 94 internal specs vs common and freelist | Swept (above). |
| `errIs_init`/`errIs_distinct` | Answer 4d's request; moved to `bbolt/errors`' API. |
| 4c-D1 | Stated consistently as open. |
| `req/go_etcd_io_bbolt.md` (from 4a) | Answered by 4c's current specs: `Open`'s error disjunct with `dbOpenOk` as 4a's environment premise; the logger contract; a reader slot per `threadTok`; the two commit updates; `isErr ErrBucketNotFound`; `txBytes` live while the transaction is; `txSize < 2^48`/`boltImage`; `Close` gives `boltClosed`. 4a still counts `beReaderN ≤ 2^30 - 2`, which 4c says it does not need: that is 4a's choice. |

## Provisional names

- **Left: `Bbolt.osFileOf`** (`Api.lean`, used by `openFileOk`). There is no `SpecPlan/Spec/os/` on this
  branch and no batch owns `os`. It stays until someone provides the `os` package's `*os.File`
  representation, with `os.OpenFile` and `os.CreateTemp` giving it and the methods `Fd`, `Stat`,
  `ReadAt`, `WriteAt`, `Sync`, `Close` taking it (`req/os.md`, "from 4c").
- No other provisional names remain.

## What I need from directories I don't own

1. **`os`** (no owner): the `*os.File` representation, to replace `osFileOf`. Also `Getenv`
   returning some string, and `Getpagesize` = 4096 (`req/os.md`, from 4d). No boundary spec
   exists.
2. **`hash/fnv`** (no owner): `New64a`, `Write`, `Sum64` computing `BboltCommon.fnv64a`
   (`req/hash_fnv.md`), for `Meta.Sum64`/`Validate`/`Write`. No spec exists.
3. **`io`** (Perennial's): `io.NewSectionReader`, `io.CopyN`, and `(*os.File).ReadAt` through them,
   for `Tx.WriteTo`. No spec exists.
4. **`sort`**: `sort.SliceIsSorted` (`req/sort.md` item 3, for the hash map's `Init`). Not present
   in `SpecPlan/Spec/sort/` (only `SortAnyLess`, `StringSlice__Sort`).
5. **`strings.ToLower`, `reflect.DeepEqual`**: requested in `req/strings.md` and `req/reflect.md`.
   No spec exists.
6. **OsFs** (this repository's extension): the 4c-D1 sector rule if the user chooses (a); `rename`
   for defrag and restore (4a, 2e).

## Open items (not fixed)

1. **The txid bound across generations.** `fileHolds`' docstring keeps the txid "below the
   receipts' bound", but the receipts are counted per generation (`Open`'s `2^62`). The crash law
   hands `fileHolds` to the next generation, which can add another `2^62` commits, so no fixed
   bound survives an unbounded number of crashes. `readersOk` needs only txid < `2^64 - 1`, so
   nothing here breaks within a generation. The bound in `fileHolds` and the crash law should be
   stated together (for example txid < `2^63` plus a premise on the number of generations, or a
   bound carried in `BoltSt`). I did not change it: it is a modelling choice for the coordinator
   or the user.
2. **Still unprovable as stated.** `Tx.recursivelyCheck{Bucket,PageKeyOrder,PageKeyOrderInternal}`
   and `Tx.checkInvariantProperties` (untyped `val` maps and channel, only `boltTx`). These are
   `tx_check.go`'s consistency checks, which etcd does not call.
3. **Too coarse for their callers' proofs** (independent of 4d): the cursor movers' `∃ pos'`,
   `node.split`/`spill`, `DB.meta` (says nothing of the meta), and `Bucket.node` (does not tie the
   node to its page). To strengthen at repair time.
4. **Optional 4c-side law:** `nodeSize N = pageHeaderSize + (nodeBody true N.itemsM).length`.
   Nothing is needed from 4d.
