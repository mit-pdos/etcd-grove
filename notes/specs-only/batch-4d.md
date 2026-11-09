# Batch 4d: bbolt's internals (`internal/common`, `internal/freelist`)

Author's report (round 0, then round 1 repairs at the end). The Go code is the main tree's bbolt (project `bbolt` of `etc/goose.py`,
`upamanyus/bbolt` at `743299d8`, with bodies: `Code/go_etcd_io/bbolt/internal/{common,freelist}.lean`);
the `Bbolt/` part is the older bank-test tree and is not this batch's.

## Files

- `Spec/go_etcd_io/bbolt/internal/common/Api.lean` (namespace `BboltCommon`) and 89 spec files
  (`Page__*`, `Meta__*`, `InBucket__*`, `Inode__*`, `leafPageElement__*`, `branchPageElement__*`,
  `Pgids__*`, `Pages__*`, `Mergepgids`, `ReadInodeFromPage`, `WriteInodeToPage`, `NewInBucket`,
  `Assert`, `Verify`, `Unsafe{Add,Index,ByteSlice}`), and `Page__Typ` (round 1): 90.
- `Spec/go_etcd_io/bbolt/internal/freelist/Api.lean` (namespace `Freelist`) and 19 spec files
  (`NewArrayFreelist`, `NewHashMapFreelist`, `Interface__{Init,Allocate,Count,FreeCount,
  PendingCount,EstimatedWritePageSize,AddReadonlyTXID,RemoveReadonlyTXID,ReleasePendingPages,Free,
  Freed,Rollback,Copyall,Read,Reload,NoSyncReload,Write}`), each holding the method's
  `Interface.<M>.contract` and the interface instance; round 1 added `array__<M>` and `hashMap__<M>`
  for the 17 methods (the canonical concrete specs, instances of the contract): 53.
- Snippets: `examples/specreq/bboltinternal/{common,freelist}.go` (`//go:build ignore`, written as
  if in the packages; gofmt-clean; checked to `go vet` cleanly when dropped into a copy of the
  pinned bbolt's `internal/common` and `internal/freelist`).
- `req/`: `hash_fnv.md`, `os.md`, `strings.md`, `sort.md`, `reflect.md`,
  `go_etcd_io_bbolt_errors.md` (all new files, `## from 4d`).

Both directories build (`etc/specs-build.sh --dir`: 91 and 54 modules, round 1).

## Exported vocabulary

### `BboltCommon` (no opaque predicate)

The ownership of a page is **Perennial's `bytesPointsto p dq bs`** of its bytes (the mmap, a page
buffer, a bucket value already come as bytes); a typed struct on the heap (`tx.meta`, an
`InBucket`, an `Inode`) is Go's typed points-to. What the package exports is the meaning of the
bytes (transparent, the file format) and laws, so that a client never computes an offset:

- Constants: `pageHeaderSize`, `elemSize`, `metaSize`, `bucketHeaderSize`, the page flags,
  `bucketLeafFlag`, `boltMagic`, `boltVersion`, `pgidNoFreelist`; `pageFlagValid`, `pgidsSorted`,
  `sortPgids`.
- Decoding: `hdrOf` (the header), `leafElemOf`/`branchElemOf`, `leafKeyOf`/`leafValueOf`/
  `branchKeyOf`, `pageItemOf`/`pageItems` (the page's items as `InodeM`: flags, page id, key,
  value), `freelistCount`/`freelistIdsOf`, `metaOf`, `inBucketOf`; well-formedness
  `leafElemIn`/`branchElemIn`, `pageReadable` (what `ReadInodeFromPage` needs), `pageLaidOut`
  (readable, data after the elements and in order: what `WriteInodeToPage` leaves),
  `freelistReadable`, `nodeFits`.
- Encoding (what the writers leave): `withHdr`, `writeNode` (`nodeBody`, `nodeElems`, `nodeData`,
  `dataOff`), `readBack`, `freelistPage`, `withMeta`, `encMeta`, `encInBucket`, `metaSummed`.
- Checksums: `fnv64a`, `metaSum`; `metaErr` (which `bbolt/errors` variable `Validate` returns),
  `metaValid`.
- Addresses: `elemLoc p i`, `metaLoc p`, `bslice`, `leafKeySlice`/`leafValueSlice`/
  `branchKeySlice`, `itemKeySlice`/`itemValueSlice`, `pageInodeAt`/`pageInodesAt` (what
  `ReadInodeFromPage` builds), `elemsSlice`, `freelistIdsSlice`.
- Laws (pure): `hdr_withHdr` (a header store reads back, the rest untouched), `writeNode_read`
  (a written node reads back as `readBack`, laid out), `freelistPage_read` (the freelist page reads
  back), `meta_withMeta`, `meta_withHdr`, `metaValid_summed`.
- Laws (resources): `meta_view` (a meta page's bytes ⊣ the typed `Meta` at `metaLoc p`, any meta
  storable back), `inBucket_view` (a value's first 16 bytes as a typed `InBucket`), `pageKV_access`
  (a laid-out page lends every item's key and value slice at its share), `freelistIds_view`,
  `elemsSlice_index` (`&LeafPageElements()[i]` is `elemLoc p i`), `init.spec` (`DefaultPageSize`
  read-only, 4096), `meta_in_sector` (round 1).

Page methods take `bytesPointsto p dq bs` and answer in decoded terms; element methods are stated
relative to their page (`e = elemLoc p i`); setters of elements (used only by
`WriteInodeToPage`) over the typed element.

### `Freelist`

- Model (transparent): `PendingPg` (freer, allocator), `FLState` (`free : GMap Pgid Unit`,
  `pending : GMap Pgid PendingPg`, `allocs : GMap Pgid Txid`), `FLState.empty`, `idSet`, `ids`
  (sorted free and pending), `count`, `wf`, `flMaxIds = 2^59`, `idsOk`, `inRun`; operations
  `init`, `reload`, `canAlloc`/`alloc`, `canFree`/`freeRun`, `canRollback`/`rollback`,
  `releasable`/`mustRelease`/`release`, `readersOk`, `estimatedSize`; `flCall fl m` (a call
  through the interface, as Goose emits it).
- Opaque: `flOwn fl F` (the freelist but its readers, exclusive: the writer's, under `rwlock`) and
  `flReaders fl R` (its read-only txids as a multiset, exclusive: under `metalock`, so `beginTx`
  and `removeTx` work beside a writer).
- Laws: `flOwn_wf`, `flOwn_timeless`, `flReaders_timeless`, `flReaders_perm`.

## Main changes from the old specs

- **Offsets out of the clients' statements.** The old specs took typed header points-tos and a
  tail of bytes at `p +ₗ 16`, address premises (`0 < l.addr`, `... ≤ maxAddr`), and returned
  slices at computed offsets. Now: the page's bytes in, decoded answers out, element methods
  relative to the page, keys and values through `pageKV_access`, metas and bucket headers through
  view laws, round trips as laws. Address premises are gone wherever the bytes imply them.
- **The freelist over an abstract state**: free pages as a set (not the array's list), pending
  pages keyed by page (not by transaction), no `lastReleaseBegin`; the old `FLPg` with its
  `srLoop` replay of `releaseRange` is gone.
- **`ReleasePendingPages` characterized**: some set of pending pages is released, each releasable
  (no reader between its allocator and its freer), including all freed before every reader. The
  old spec replayed the code exactly.
- **Readers as their own resource** (`flReaders`; the old `flRoOwn`), with `Add`/`Remove` specs
  (new) and a multiset law.
- **`Init`, `Read` from any state** (not only a fresh freelist): `Reload` reinitializes a live one.
- **`Meta.Validate`'s error named** (`metaErr`) and non-nil.
- New specs: `Pgids.Len/Less/Swap`, `Pages.Len/Less/Swap` (for `sort.Sort`'s callers),
  `NewArrayFreelist`, `NewHashMapFreelist`, `Interface.Count`, `Freed`, `Copyall`,
  `AddReadonlyTXID`, `RemoveReadonlyTXID`.
- Premises moved into preconditions throughout.

## Left out (no old spec, no caller in bbolt or this batch's sketches)

`internal/common`: `Page.Typ`, `Page.String`, `Page.hexdump`, `NewPage`, `NewLeafPageElement`,
`leafPageElement.Bucket`, `LoadBucket`, `LoadPage`, `LoadPageMeta` (bbolt casts itself),
`CopyFile` (the CLI's), `UsedSpaceInPage`, `InBucket.String`, `Meta.Print`,
`Meta.IsFreelistPersisted`, `Meta.Magic/Version/Flags/SetFlags/Checksum`, the verification helpers
but `Verify` (`getEnvVerify`, `IsVerificationEnabled`, `Enable*`, `Disable*`).
`internal/freelist`: the concrete methods (`array.*`, `hashMap.*`, `shared.*`) and the unexported
interface methods (`freePageIds`, `pendingPageIds`, `release`, `releaseRange`, `mergeSpans`): the
realization of `flOwn` proves the interface's triples from them.

## Decisions for the user

1. **No opaque predicate in `BboltCommon`.** Pages are Perennial's byte points-tos; the package
   adds transparent decoders and laws. An opaque `pageAt` would only rename `bytesPointsto` and
   cost every client a conversion at the mmap and at each buffer. The decoders are transparent
   because they are the file format bbolt's own model (4c's `boltImage`, `fileHolds`) is written
   in; clients use the laws, not the definitions.
2. *(Reversed in round 1.)* Each freelist method's contract is written once at a receiver
   (`Interface.<M>.contract fl f`); the canonical specs are the concrete instances
   (`array.<M>.spec`, `hashMap.<M>.spec`), and the interface spec bbolt uses is the instance at
   `flCall`, proved from them with `flOwn_dyn`/`flReaders_dyn`.
3. **`ReleasePendingPages` leaves open which releasable pages beyond `mustRelease` it frees**
   (margin): the exact set depends on `lastReleaseBegin`, an optimization no client needs.
4. **Local bound `flMaxIds = 2^59`** on the freelist methods that count or sort (and
   `R.length < 2^62` on `ReleasePendingPages`, Perennial's sort): bbolt meets the first from its
   high-water mark (`≤ 2^36` pages); the second is Perennial's `sort.Sort` limitation
   (`notes/perennial-changes.md`, "`sort.Sort`'s size premise").
5. **`DefaultPageSize` trusted to be 4096** (round 1, the coordinator's decision: the linux/amd64
   constant the old development trusted; 4c is written at 4096; `init.spec`, `req/os.md`).

## Finding (already filed: `nonissues/bbolt-txid0-reader-release.md`; mechanism corrected in round 1)

**A read transaction at txid 0 lets `ReleasePendingPages` release the pages it reads.**
`shared.ReleasePendingPages` (`internal/freelist/shared.go:141-158`) computes `tid - 1` for each
reader `tid`: with a reader at txid 0 (the oldest), `releaseRange(0, 2^64-1)` covers every pending
page; a fresh entry is skipped once (`lastReleaseBegin = 0`), so the second call with the reader still
open releases them all, including pages freed by txid 1 that
the txid-0 reader still reads; the next writer may reallocate and overwrite them. A reader has
txid 0 only when `db.meta()` picks meta 0 at txid 0, i.e. meta 1 (txid 1, written by `init`) does
not validate: a file whose meta page 1 is corrupt before the first commit. Code reading only;
bbolt's `init` writes both metas and syncs before the file is used, and 4c's `fileHolds` keeps the
txid at least 1, so the spec's premise `readersOk` (no reader at txid 0 or `2^64-1`) is met.
`blocks-proof: no` (a premise 4c discharges).

## `req/` sections written

- `hash_fnv.md`: `New64a`/`Write`/`Sum64` computing `fnv64a` (`Meta.Sum64`).
- `os.md`: `Getenv` returns some string (`Verify`); `Getpagesize` is 4096 (`init.spec`).
- `strings.md`: `ToLower` returns some string (`Verify`).
- `sort.md`: `sort.Sort` (with its bound), `sort.Search`, `sort.SliceIsSorted` (the hash map's
  `Init`).
- `reflect.md`: `DeepEqual` on two `map[Pgid]struct{}` (the hash map's `mergeSpans` check).
- `go_etcd_io_bbolt_errors.md`: the error variables hold non-nil values, read-only
  (`Meta.Validate`).

## Open questions

- 4c's needs (`req/go_etcd_io_bbolt_internal_{common,freelist}.md`, `## from 4c`) did not exist when
  this report was written; the vocabulary follows bbolt's own calls (`tx.go`, `db.go`, `node.go`,
  `bucket.go`, `cursor.go`, `tx_check.go`) and 4c's `Api.lean` header (which names `metaOf`,
  `pageItems`). To re-check against them at repair time.
- `Pages.Less`/`Swap` take every page's bytes at one share (`[∗list] p;bs ∈ ps;bss`): enough for
  `Tx.write`'s dirty pages (owned by the writer); a client sorting pages it holds at different
  shares would need a per-page share.

## Round 1 repairs (review `reviews/4d-review-1.md`)

- **F1 (unsound: the hash map's empty `Init`).** `Interface.Init`, `Read`, `Reload` and
  `NoSyncReload` take again the old premise: the new free pages are not empty, or no page was
  free (`ids ≠ [] ∨ F.free = GMap.empty`; for `NoSyncReload` the ids left once the pending ones
  are dropped; for `Read`/`Reload` the page's ids), with the reason in each docstring and in the
  `Api.lean` header. 4c told what it must keep (`req/go_etcd_io_bbolt_internal_freelist.md`,
  "from 4d (round 1)": the in-memory free pages are among the last commit's freelist ids or the
  unreachable pages). `nonissues/bbolt-hashmap-init-empty-stale-cache.md`'s Proof section now
  names the four specs. Snippet `ReqReloadEmpty`.
- **F2 (`DefaultPageSize`).** `init.spec` is `globalAddr DefaultPageSize ↦□ W64 4096`;
  `req/os.md` updated.
- **S1 (canonical concrete specs).** `array__<M>.lean`, `hashMap__<M>.lean` for the 17 methods,
  each `Interface.<M>.contract` at `arrayIface l`/`hashMapIface l` with the type's method (own or
  promoted from `*shared`); `Interface.<M>.spec` the instance at `flCall`, proved from them; new
  `arrayIface`, `hashMapIface`, laws `flOwn_dyn`, `flReaders_dyn`; the constructors return
  `arrayIface l` / `hashMapIface l`.
- **S2.** `freelistPage_read`'s room is `Write`'s: `16 + 8 * (n + [n ≥ 0xFFFF])`.
- **S3.** References to `ReqFreelistPageRoundTrip`/`ReqEstimate` now name `ReqWriteReload`.
- **S4.** New snippets `ReqPageSortWrite` (`Tx.write`'s sort and chunks), `ReqWriteToMeta`
  (`WriteTo`'s metas in place), `ReqVerify` (bucket.go:889).
- **S5.** `Page.Typ.spec` (returns some string; reads the header).
- **S6.** `Assumes:` lines: page id ≥ 2 and a header-sized buffer (`ReqReleaseSafe`,
  `ReqRollback`), txid 7 freed nothing (`ReqRollback`), `ReqElementKeys`' id and held key bytes.
- **S7.** `Reload` no longer takes `F.count < flMaxIds`.
- **S8.** The txid-0 finding: mechanism corrected to two calls (in
  `nonissues/bbolt-txid0-reader-release.md`, with the `2^64-1` mirror case and the spec premise),
  and this report.
- **S9** (`0 < l.addr` beside typed points-tos of `Meta`): kept: Perennial gives positivity from a
  byte points-to (`PointstoPos` for scalars), not from a struct's typed points-to; every caller has
  it (an allocation or `metaLoc p` of a page's bytes).
- **4c's `## from 4c` (common)**: item 1's sector fact is now a law (`meta_in_sector`); items 2-5
  are served by `writeNode_read`, `inBucket_view`, the element specs, `UnsafeByteSlice`, and the
  total decoders. **(freelist)**: items 1-6 served; item 5's counts keep `F.count < flMaxIds`,
  which item 6 meets.

Rebuilt: `etc/specs-build.sh --dir` both directories, 145 modules OK; snippets gofmt-clean and
`go vet`-clean in a copy of the pinned packages.
