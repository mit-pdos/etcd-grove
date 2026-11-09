# Batch 4d: bbolt's internals (`internal/common`, `internal/freelist`)

Author's report (round 0). The Go code is the main tree's bbolt (project `bbolt` of `etc/goose.py`,
`upamanyus/bbolt` at `743299d8`, with bodies: `Code/go_etcd_io/bbolt/internal/{common,freelist}.lean`);
the `Bbolt/` part is the older bank-test tree and is not this batch's.

## Files

- `Spec/go_etcd_io/bbolt/internal/common/Api.lean` (namespace `BboltCommon`) and 89 spec files
  (`Page__*`, `Meta__*`, `InBucket__*`, `Inode__*`, `leafPageElement__*`, `branchPageElement__*`,
  `Pgids__*`, `Pages__*`, `Mergepgids`, `ReadInodeFromPage`, `WriteInodeToPage`, `NewInBucket`,
  `Assert`, `Verify`, `Unsafe{Add,Index,ByteSlice}`).
- `Spec/go_etcd_io/bbolt/internal/freelist/Api.lean` (namespace `Freelist`) and 19 spec files
  (`NewArrayFreelist`, `NewHashMapFreelist`, `Interface__{Init,Allocate,Count,FreeCount,
  PendingCount,EstimatedWritePageSize,AddReadonlyTXID,RemoveReadonlyTXID,ReleasePendingPages,Free,
  Freed,Rollback,Copyall,Read,Reload,NoSyncReload,Write}`).
- Snippets: `examples/specreq/bboltinternal/{common,freelist}.go` (`//go:build ignore`, written as
  if in the packages; gofmt-clean; checked to `go vet` cleanly when dropped into a copy of the
  pinned bbolt's `internal/common` and `internal/freelist`).
- `req/`: `hash_fnv.md`, `os.md`, `strings.md`, `sort.md`, `reflect.md`,
  `go_etcd_io_bbolt_errors.md` (all new files, `## from 4d`).

Both directories build (`etc/specs-build.sh --dir`: 90 and 20 modules).

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
  read-only, between 4096 and 65536).

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
2. **The freelist's specs are stated at the interface** (`Interface__<M>`, over the bundle
   `flOwn`), not per concrete type: bbolt only calls through `db.freelist`, and one spec per
   method serves both implementations (PRINCIPLES, "an interface value gets a bundle"). The
   concrete methods' specs stay internal to the realization.
3. **`ReleasePendingPages` leaves open which releasable pages beyond `mustRelease` it frees**
   (margin): the exact set depends on `lastReleaseBegin`, an optimization no client needs.
4. **Local bound `flMaxIds = 2^59`** on the freelist methods that count or sort (and
   `R.length < 2^62` on `ReleasePendingPages`, Perennial's sort): bbolt meets the first from its
   high-water mark (`≤ 2^36` pages); the second is Perennial's `sort.Sort` limitation
   (`notes/perennial-changes.md`, "`sort.Sort`'s size premise").
5. **`DefaultPageSize` trusted between 4096 and 65536** (`init.spec`, from `os.Getpagesize`;
   `req/os.md`).

## Finding (for `nonissues/`, not filed: outside this batch's paths)

**A read transaction at txid 0 lets `ReleasePendingPages` release the pages it reads.**
`shared.ReleasePendingPages` (`internal/freelist/shared.go:141-158`) computes `tid - 1` for each
reader `tid`: with a reader at txid 0 (the oldest), `releaseRange(0, 2^64-1)` releases every pending
page whose allocator is in `[0, 2^64-1]`, i.e. all of them, including pages freed by txid 1 that
the txid-0 reader still reads; the next writer may reallocate and overwrite them. A reader has
txid 0 only when `db.meta()` picks meta 0 at txid 0, i.e. meta 1 (txid 1, written by `init`) does
not validate: a file whose meta page 1 is corrupt before the first commit. Code reading only;
bbolt's `init` writes both metas and syncs before the file is used, and 4c's `fileHolds` keeps the
txid at least 1, so the spec's premise `readersOk` (no reader at txid 0 or `2^64-1`) is met.
`blocks-proof: no` (a premise 4c discharges). A coordinator may file it as
`nonissues/bbolt-freelist-reader-txid-zero.md`.

## `req/` sections written

- `hash_fnv.md`: `New64a`/`Write`/`Sum64` computing `fnv64a` (`Meta.Sum64`).
- `os.md`: `Getenv` returns some string (`Verify`); `Getpagesize` in `[4096, 65536]` (`init.spec`).
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
