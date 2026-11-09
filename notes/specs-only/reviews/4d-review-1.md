# Batch 4d, review 1 (provability and completeness)

Reviewer: independent of the author. Targets: `Spec/go_etcd_io/bbolt/internal/common/` (Api + 89
specs), `Spec/go_etcd_io/bbolt/internal/freelist/` (Api + 19 specs), the snippets
`examples/specreq/bboltinternal/{common,freelist}.go`, and the `## from 4d` requests in `req/`. Go
code: `.lake/src/bbolt/internal/{common,freelist}/` (upamanyus/bbolt@743299d8). Callers: bbolt's
`db.go`, `tx.go`, `node.go`, `bucket.go`, `cursor.go`, `tx_check.go`, and batch 4c's
`Spec/go_etcd_io/bbolt/` as of this review. Batch 4c is still being written and has no
`req/go_etcd_io_bbolt_internal_*.md` yet.

Line numbers are those of the pinned files. I checked the Go behaviour with two throwaway tests in
a copy of the module under `/tmp/rev4d/b`, outside the repository.

## First tier

### F1. `Init`, `Read`, `Reload` and `NoSyncReload` are false for the hash-map freelist when the new ids are empty (unsound; this is a regression)

`hashMap.Init` returns early when there are no ids (`internal/freelist/hashmap.go:30`), before
`f.reindex()` (`hashmap.go:58`). So `shared.cache` still holds the ids that were free before.
Three things follow:

- `Freed(x)` (`shared.go:52`) returns true for a page that is neither free nor pending.
- `Free` of such a page panics: "page N already freed" (`shared.go:80`).
- The `Freed` spec, read with `canFree` and the `Free` spec, says this cannot happen.

The specs take no premise against it:

- `Interface.Init.spec`: any `F`, with `ids = []` allowed.
- `Interface.Read.spec`: an empty freelist page reaches `t.Init([]common.Pgid{})` (`shared.go:266`).
- `Interface.Reload.spec`: the same, through `Read`. The second `Init` is then empty as well.
- `Interface.NoSyncReload.spec`: when every id is pending, `t.Init(a)` with `a = []` (`shared.go:239`).

From `F.free = {3}`, each of these specs gives `F.free = ∅` with page 3 neither free nor pending,
so `canFree` holds for page 3. Checked with a test: `NewHashMapFreelist(); Init([3]); Init([])`,
then `Freed(3) = true` and `Free(5, page 3)` panics "page 3 already freed". The realization of
`flOwn` ("`cache` the free and pending ids") cannot hold after these calls.

The old specs had the premise:

- `specs-ref/.../Interface__Reload.lean:47`: `flIds pg ≠ [] ∨ fl.free = []`.
- `Interface__NoSyncReload.lean:41`: `(fl.noSyncReload ids).free ≠ [] ∨ fl.free = []`.
- The old `Init` and `Read` only applied to `FLState.empty`.

The new specs, generalized "from any state", dropped it. The recorded nonissue
`nonissues/bbolt-hashmap-init-empty-stale-cache.md` says that "the freelist's `Reload`/`NoSyncReload`
specs take the premise". On this branch they do not, so the nonissue is now false as well.

Callers affected:

- 4c's `Tx.rollback` (tx.go:343, 346).
- `loadFreelist` (db.go:457, 460). It meets any form of the premise trivially, because its freelist
  is fresh.

Fix: add the premise back:

- `Init`: `ids ≠ [] ∨ F.free = ∅`.
- `Read`: `freelistIdsOf bs ≠ [] ∨ F.free = ∅`.
- `Reload`: `freelistIdsOf bs ≠ [] ∨ F.free = ∅`. A non-empty page whose ids are all pending is
  fine: `Read`'s `Init` reindexes first.
- `NoSyncReload`: `ids.filter (· ∉ F.pending) ≠ [] ∨ F.free = ∅`.

Write in each spec's comment that the hash map needs it, and tell 4c through `req/` what it must
keep: "the in-memory free pages are among the last commit's freelist ids (synced) or the
unreachable pages (`freepages`)". This is the argument the nonissue makes.

### F2. `init.spec` gives `DefaultPageSize ∈ [4096, 65536]`, but 4c is written at 4096 (the caller is not served)

`init.spec` (common `Api.lean`, last law) and `req/os.md` trust `os.Getpagesize()` only to lie in
`[4096, 65536]`. Every 4c statement that depends on it fixes 4096:

- `fileHolds` ("valid metas recording page size 4096", `Spec/go_etcd_io/bbolt/Api.lean:73`).
- `DB__Info.lean:14` ("`PageSize` is `4096`").
- `Tx__Size.lean:6` ("times `4096`").
- `Open.lean:28` (D13, the default page size).

A new file's page size is `common.DefaultPageSize` (db.go:266-268). From the range alone, 4c's
`Open` cannot establish `fileHolds` after `init`. The old development trusted exactly 4096: the
platform its models assume, where `syscall.Getpagesize` on linux/amd64 is the constant 4096
(`specs-ref/Spec/os/Getpagesize.lean`, `Proof/.../common/Init.lean:5-8`). D9's meta-page rule (one
aligned OS page) also ties the bbolt page to the OS page.

Fix, either of:

- Restate `init.spec` (and `req/os.md`) as `sint.Z n = 4096`, the amd64 fact, written as such.
- Make 4c generalize `fileHolds`, `Info` and `Size` to a named `osPageSize` in `[4096, 65536]`.

Decide with 4c. As things stand the two batches disagree.

## Second tier

- **S1. The freelist specs are on interface calls, with no per-concrete-type spec files**
  (PRINCIPLES, "Canonical specs are per (concrete type, method); an interface value gets a
  bundle"). `flOwn` is the bundle, which is correct for bbolt, which only calls through
  `db.freelist`. But the canonical (type, method) entries are missing: `array.Allocate`,
  `hashMap.Allocate`, `array.Init`, `hashMap.Init`, `shared.Free` promoted, and the rest. The
  report lists this as decision 2 for the user. The principle's own remedy is "write each
  interface method's contract once at a receiver `(ty, v)` and make each concrete spec its
  instance". Leaving it to the user is acceptable; I note it as a departure, not a defect of the
  statements.
- **S2. `freelistPage_read.spec` asks for 8 more bytes than `Write` uses when there are fewer than
  0xFFFF ids.** Its premise is `16 + 8 * (ids.length + 1) ≤ bs.length`, but `freelistReadable` of
  the result needs only `16 + 8 * (n + [n ≥ 0xFFFF])`, i.e. `estimatedSize`. `ReqWriteReload`
  assumes only "pageSize is positive", so with a page size that is not a multiple of 8 its `g.Read(p)`
  cannot use the law. 4c's 4096-byte pages do give the slack, but state the law at `Write`'s own
  bound, `estimatedSize` over `ids.length`, so that `Write`'s post and the law compose without
  arithmetic.
- **S3. Snippets that are named but do not exist.** `ReqFreelistPageRoundTrip` (common `Api.lean:54`,
  `Page__FreelistPageIds.lean:4`) and `ReqEstimate` (freelist `Api.lean:60`,
  `Interface__Write.lean:4`, `Interface__EstimatedWritePageSize.lean:4`) are not in
  `examples/specreq/bboltinternal/`. `ReqWriteReload` covers both. Rename the references or add
  the snippets.
- **S4. Patterns no snippet covers** (a completeness gap; the specs exist):
  - `Tx.write` sorts its dirty pages with `sort.Sort(common.Pages)` (tx.go:529-535), then writes
    each page's bytes in chunks through `UnsafeByteSlice` (tx.go:549, 588). Specs:
    `Pages.Len/Less/Swap` and `UnsafeByteSlice`.
  - `WriteTo` builds the meta in place (tx.go:440-455): `*page.Meta() = m`, `DecTxid`,
    `SetChecksum(Sum64())`. `ReqMetaRoundTrip` covers only the `init` half of this.
  - `Verify` around a closure (bucket.go:889).
- **S5. `Page.Typ` has no spec, yet bbolt calls it.** Callers: `Tx.Page` (tx.go:697), whose
  `Freed` call the batch did spec for; `tx_check.go:173`, an error path reached from `freepages`,
  which is etcd's `NoFreelistSync` load; `shared.Read`'s panic message (`shared.go:259`). The
  last two are excluded by premises. `Tx.Page` is not excluded. Add a trivial spec ("returns some
  string, reads the header"), or drop `Freed`'s claim to serve `Tx.Page` if 4c leaves `Tx.Page`
  out.
- **S6. Snippet `Assumes` lines are incomplete.** `ReqReleaseSafe` and `ReqRollback` free a page
  that is only "in use", but `Free` needs `id ≥ 2` (meta pages 0 and 1 are in use too) and a `buf`
  of at least a header. `ReqRollback` also needs "txid 7 has freed nothing yet", or `canRollback`
  can fail on its earlier frees. `ReqElementKeys` needs `id` to be the page's id and its `items`'
  key bytes held. Each is a one-line `Assumes:` addition.
- **S7. A premise the code does not need.** `Interface.Reload.spec` takes `F.count < flMaxIds`.
  `Reload` sorts only the page's ids (bounded by the other conjunct) and counts nothing. Drop it,
  or say why it is there (PRINCIPLES, "No unneeded premise").
- **S8. The batch report's "Finding" is stale and imprecise.**
  - It is already filed as `nonissues/bbolt-txid0-reader-release.md` (2026-11-04).
  - Both texts say that a reader at txid 0 makes `releaseRange(0, 2^64-1)` release everything at
    once. In fact a fresh `txPending` has `lastReleaseBegin = 0`, so that call skips it
    (`shared.go:183`). Only a second `ReleasePendingPages` with the reader still open releases the
    page: the first call's `releaseRange(1, Max)` has set `lastReleaseBegin = 1`.
  - Checked with a test: reader 0, `Free(1, page 3)` with `alloc` 0, two `ReleasePendingPages`
    calls, then `Allocate(2, 1)` returns 3.
  - So the bug is real, and `readersOk` is the right premise. Its other half, no reader at
    `2^64-1`, is also needed: `tid+1` wraps to 0 and the final `releaseRange(0, Max)` releases
    everything.
  - It is reachable only from a current meta at txid 0, i.e. meta page 1 damaged before txid 2's
    commit. The fork's `init` is crash-safe, and 4c's `fileHolds` keeps txid at least 1.
  - Suggest correcting the mechanism in the nonissue (two calls), and removing "not filed" from
    the report.
- **S9. Nit.** `Meta.Validate`, `Meta.Sum64` and `Meta.Write` take `0 < l.addr` beside a typed
  points-to. Callers have it, but if Perennial's `PointstoPos` gives it from the points-to, the
  premise is noise.

## Provability

### (a) Decoders and encoders against the unsafe layout: correct

I checked every offset against the Go structs (page.go:31-36, 225-266; meta.go; bucket.go;
inode.go). Perennial's `ByteEncoding` for `w16`/`w32`/`w64` is little-endian (`natBytes`,
`Theory/Unsafe.lean`).

| Item | Layout | Matches |
|---|---|---|
| `Page` | `id` 0..8, `flags` 8..10, `count` 10..12, `overflow` 12..16 | yes |
| leaf element | `flags`, `pos`, `ksize`, `vsize`, 4 bytes each | yes |
| branch element | `pos`, `ksize`, `pgid` (8) | yes |
| `Meta` (64 bytes) | `magic`, `version`, `pageSize`, `flags`, `root` (`InBucket` 16..32), `freelist` 32, `pgid` 40, `txid` 48, `checksum` 56 | yes |

- Key and value offsets are relative to the element (`elemOff i + pos`, value after the key), as in
  `UnsafeByteSlice(n, 0, pos, pos+ksize)`. The returned slices have cap = len (`[i:j:j]`), which
  matches `bslice`.
- `nodeElems`' `pos = dataOff ms i - elemOff i` matches `WriteInodeToPage`'s
  `off - (16 + elemsz*i)` (inode.go:84). The return value `16 + 16 n + data` matches.
- Branch items' values are copied (inode.go:104) but not recorded. `nodeData` includes them and
  `readBack` drops them, which is correct.
- `freelistCount` and `freelistIdsOf` match `FreelistPageCount`/`FreelistPageIds`, including the
  count in the first `Pgid` at `0xFFFF` and the `int` sign check (`< 2^63`).
- `freelistPage` matches `shared.Write` in its three branches. Only `flags` and `count` are written
  in the header.
- `metaSum` is FNV-1a over the first 56 bytes, which is `Offsetof(checksum)`. The basis and prime
  are right.
- `metaErr`'s order matches `Validate`.
- `Meta.Write`'s post (header `id = txid % 2`, flags meta, `metaSummed v` after the header) matches
  meta.go:448-464.
- Overflow pages: the page is its whole extent's bytes, so items in overflow pages are inside `bs`.
- Alignment is not modelled by Perennial. bbolt's unaligned path copies (bucket.go:119-136), so
  nothing depends on it.

The address premises the old specs carried are implied by the bytes: `heapPointsto` carries
`0 < addr < maxAddr` (`GooseLang/Lifting.lean:126`), so a non-empty `bytesPointsto` lies in
`(0, maxAddr]`.

The round-trip and view laws are true:

- `hdr_withHdr`, `meta_withMeta` and `meta_withHdr` follow from `replaceBytes` on disjoint ranges.
- `writeNode_read` holds under `nodeFits`, `count = |ms|` and the room premise: spans increasing,
  after the elements, keys non-empty.
- `freelistPage_read`: see S2 for its premise.
- `meta_view` and `inBucket_view` hold at any `dq`. The wand holds the header and tail bytes, and a
  typed `↦{dq} m` gives back the bytes encoding `m` (`bytesPointsto_view`).
- `pageKV_access` holds: `pageLaidOut` makes the spans disjoint and keeps them off the header and
  elements.

### (b) Freelist model against both implementations

Correct except F1:

- **`Allocate`.** The array scans strictly increasing ids for a run of `n` and removes exactly that
  run; this needs `idsOk`/`wf` for `id ≥ 2` and strictness. The hash map takes an exact span or
  splits a larger one. Both record `allocs[r] = txid` and delete the run from `cache`. `canAlloc`
  (`r ≠ 0`, `r+n ≤ 2^64`, the run free) holds of both, and `r = 0` changes nothing.
- **`Free`.** `canFree`'s bound `id + n < 2^64` with `n = overflow+1` is exactly what keeps
  `id <= p.Id()+overflow; id++` from wrapping (shared.go:77). The `allocs` check is `Verify`'s
  (default 0), which `Verify.spec` makes either branch of.
- **`Rollback`.** The model matches `shared.Rollback` (shared.go:89-118):
  - `alloc = 0` entries are skipped.
  - `allocs` is restored for overflow pages too.
  - With a left-biased union, the panic case is excluded by `canRollback`.
  - The early return when `txid` freed nothing leaves `allocs` alone, as the model's `else F` does.
  - `txp ≠ nil` iff some page is pending for `txid`: `releaseRange` and `release` delete empty
    entries, and `Free`'s loop always runs at least once.
- **`ReleasePendingPages`.** The relational post holds:
  - `release(minid-1)` releases exactly the pages freed before every reader (`mustRelease`, and
    with no readers `freer ≤ 2^64-2`).
  - Each `releaseRange(r_i+1, r_{i+1}-1)` and the final one release only pages whose allocator and
    freer both lie in a gap between sorted readers, so no reader `r` has `a ≤ r < t`
    (`releasable`).
  - Duplicate readers give empty ranges.
  - `lastReleaseBegin` only releases fewer, which the existential `S` absorbs.
  - `readersOk` is needed: see S8.
- **`Reload`.** `Read`'s `Init` (ids may overlap pending for a moment), then `NoSyncReload`
  filters, giving `free = ids \ pending`, with `allocs` and `pending` unchanged. That is correct
  given F1's premise.
- **`Write`, `Copyall`, `EstimatedWritePageSize`, `Count`.** Correct. `F.ids = sortPgids(free ++
  pending)` equals `Mergepgids`' output because the two sides are disjoint (`wf`).
- **Readers.** `flReaders` apart from `flOwn` is realizable. `readonlyTXIDs` is touched only by
  `Add`, `Remove` and `ReleasePendingPages`, all under `metalock` (db.go:896, 944, 957). The
  writer's other calls touch the other fields.

### (c) Bounds

- `flMaxIds = 2^59` covers `16 + 8(n+1) < 2^63` and Perennial's `sort.Sort` bound (`≤ 2^62`,
  `Perennial/Spec/sort/Sort.lean`).
- bbolt meets it through its high-water mark (amd64 `maxMapSize / 4096 = 2^36`).
- `R.length < 2^62` comes from the reader slots.
- `DefaultPageSize`: F2.

### (d) Snippets

- All are `//go:build ignore` and gofmt-clean. Dropped into a copy of the pinned package, `go vet`
  passes on both.
- Under the specs, with the S6 additions, every snippet is provable:
  - `ReqNodeRoundTrip`: setters, `writeNode_read`, `ReadInodeFromPage`, `pageKV_access` for
    `bytes.Equal`.
  - `ReqElementKeys`: `elemsSlice_index` in the `sort.Search` closure, the element specs at the
    page's share, `pageKV_access`.
  - `ReqMetaRoundTrip`: `meta_withMeta` with `hdr_withHdr` for the header; `meta_view`;
    `metaValid_summed` for `Validate = nil`; `Copy`. Then the `init` half: setters through
    `meta_view`, `Sum64`, `metaErr`.
  - `ReqInlineBucket`: `inBucket_view` over the value via `ownSlice_byte_view`, `bytesPointsto_app`
    at 16, `WriteInodeToPage`.
  - `ReqMergePgids`.
  - `ReqAllocFree`: `canAlloc` and `wf`, then `canFree` since `allocs[r] = txid ≠ txid+1`, then
    `Freed`.
  - `ReqReleaseSafe`: page 3, pending (5, a ≤ 4), is not releasable with `R = [4]`, so it stays
    pending and `wf` keeps it from being allocated. After `Remove`, `mustRelease` releases it.
  - `ReqRollback`.
  - `ReqWriteReload`: `freelistPage_read`, which needs pages that are multiples of 8 (S2); `Read`
    into a fresh hash map; `reload` of `free ∪ pending` gives `free`; `Copyall` output satisfies
    `idsOk`.
- None of the snippets exercises F1's case. That is why the gap was missed: no snippet reloads or
  re-inits a freelist with a non-empty free set and empty ids. A snippet should, as its negative
  `Assumes:`.

## Completeness: bbolt's calls into the two packages, by file

All are served by a spec unless noted.

- **db.go**
  - `Page.Meta` (396, 436, 579-580, 695).
  - `Meta.Validate` (396, 436, 585-586, 1226-1228), `Meta.PageSize`.
  - The `init` meta setters: `SetMagic`/`SetVersion`/`SetPageSize`/`SetFreelist`/`SetRootBucket`/
    `NewInBucket`/`SetPgid`/`SetTxid`/`SetChecksum`/`Sum64`; `Page.SetId/SetFlags/SetCount`.
  - `allocate`: `SetOverflow`, `SetId`, `Id`, `freelist.Allocate` (1246-1250).
  - `newFreelist` (`NewArrayFreelist`/`NewHashMapFreelist`).
  - `loadFreelist`: `Init`, `Read`, `FreeCount` (454-467).
  - `beginTx`: `AddReadonlyTXID` (896). `beginRWTx`: `ReleasePendingPages` (944). `removeTx`:
    `RemoveReadonlyTXID` (957).
  - `DefaultPageSize` (268): F2.
- **tx.go**
  - `Meta.Copy` (53), `RootBucket`, `IncTxid`, `Txid`, `Pgid`, `Freelist`, `SetFreelist`.
  - `freelist.Free` (217), `EstimatedWritePageSize`/`Write` (289, 295), `Rollback` (318, 336),
    `NoSyncReload`/`Reload` (343, 346), which are F1's callers.
  - Stats: `FreeCount`/`PendingCount`/`EstimatedWritePageSize` (359-361).
  - `WriteTo` meta: `SetFlags`, `Meta`, `SetId`, `DecTxid`, `SetChecksum`, `Sum64` (440-455).
  - `Tx.write`: `Pages.Len/Less/Swap` (535), `UnsafeByteSlice` (549, 588).
  - `Meta.Write` (609), `FastCheck` (639, 646).
  - `Tx.Page`: `Freed` (694), `Typ` (697): S5.
- **node.go**
  - `Id`, `IsLeafPage`, `ReadInodeFromPage`, `Inode.Key` (161-170).
  - `Count`, `Flags`, `SetFlags`, `SetCount`, `WriteInodeToPage` (180-200).
  - `Inode` getters and setters, and `freelist.Free` (325, 502).
- **bucket.go**
  - `InBucket` getters and setters (`RootPage`, `SetRootPage`, `InSequence`, `SetInSequence`,
    `IncSequence`), and the casts at 132-140, 763-764, 844-849 (`inBucket_view`, inline page bytes).
  - Stats: `LeafPageElement`/`BranchPageElement`, `Pos`/`Ksize`/`Vsize`, `Flags`, `Value`
    (638-676).
  - `Verify` (889), `freelist.Free` (915).
- **cursor.go**: `IsLeafPage`/`IsBranchPage`, `Count`, `LeafPageElement(s)`/`BranchPageElement(s)`,
  `Key`/`Value`/`Flags`/`Pgid`, `Id`, `Flags` (286).
- **tx_check.go**: `Count`/`Copyall` (49-50); element walks; `IsBucketEntry` (110); `NewInBucket`
  (111); `Typ` (173): S5.
- **Out of scope:** `internal/surgeon`, `internal/guts_cli` and `cmd/bbolt`. They are tools and no
  etcd path reaches them.

What 4c needs, from `Spec/go_etcd_io/bbolt/Api.lean`, `Internal.lean`, `Tx__commitFreelist.lean`
and `Open.lean`:

- `metaOf`, `pageItems` and the file decoders: present.
- The rollback reloads (F1).
- `DefaultPageSize` (F2).
- `readersOk` is met by `fileHolds`' "txid at least 1 and below the receipts' bound".

Note for 4c: `Open.lean:18` says `loadFreelist` uses `NoSyncReload`; it calls `Init` (db.go:457).

## What is good

- **Offsets are out of the clients' statements.** Page methods take the page's bytes and answer
  in decoded terms, element methods are relative to their page, and view and access laws replace
  every typed-header/tail split and address premise of the old specs.
- **The file format is transparent pure functions.** 4c's file model can be written in them, with
  the round trips as laws.
- **The freelist is over an abstract `FLState`.** The specs serve both implementations, with the
  readers as a separate exclusive resource, which matches bbolt's locking.
- **`ReleasePendingPages` is characterized by what clients need** (released implies releasable, and
  `mustRelease` is released), instead of replaying `lastReleaseBegin`. This is a real improvement.
  The `readersOk` premise is necessary and correctly justified.
- **Panics are premises in the pre**, each tied to the code line that panics.

## Ranking (need of revision)

1. **`internal/freelist`.** F1 makes four specs unsound and the nonissue's claim false. S1, S2,
   S6-S8 are minor.
2. **`internal/common`.** F2 is a cross-batch mismatch with 4c that one line fixes. S2, S3, S4, S5
   and S9 are minor. The decoders and laws themselves are right.

## Verdict

Not done: two first-tier findings.

- F1 is a regression. Restore the hash map's premise on `Init`, `Read`, `Reload` and
  `NoSyncReload`, and hand 4c the invariant it must keep.
- F2 is a mismatch with 4c over `DefaultPageSize`: 4096 against a range. Settle it with 4c.

Everything else is second tier. The layout, the codecs, the `Allocate`/`Free`/`Rollback` model, the
`ReleasePendingPages` characterization and the snippets otherwise check out against the code.
