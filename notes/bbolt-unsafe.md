# What `unsafe` must be modeled to verify bbolt

**Date:** 2026-10-10. **Subject:** `go.etcd.io/bbolt` v1.5.0 (etcd's dependency, in etcd's
`go.mod`); upstream main (2026-09-15, `4dc08f7`) is the same in every respect below.
**Perennial:** `lean` at `6ffd21fce` (the pin).

## Summary

bbolt is not goosable as it stands, and the reason is not a missing Goose feature at the
edges. The database works by using `unsafe` directly:

- Pages are `[]byte` buffers: the read-only `mmap` of the file, or heap buffers from `make`
  or the page pool.
- The code reads and writes those buffers as Go structs (`Page`, `Meta`, `InBucket`, the page
  elements, arrays of `Pgid`) through `(*T)(unsafe.Pointer(&buf[i]))`.
- It moves around inside them with `uintptr` arithmetic.
- It hands out `[]byte` slices that alias the struct memory: keys and values, and whole pages
  for `WriteAt`.

Perennial's Go model has a **typed heap**: a location holds a value of one Go type, and there is
no rule that says what the bytes of a `Page` are. It defines `*T ↔ unsafe.Pointer` as the
identity on locations (`Golang/Defn/Predeclared.lean`, `convert_unsafe_to_pointer`). It
deliberately leaves `uintptr ↔ pointer` stuck ("a program using one cannot be verified",
`UintptrSemantics`). So even with every Goose error fixed, nothing could be proved about a page.

Verifying bbolt as written needs, in order of how much they change Perennial:

1. **Layout constants** (`unsafe.Sizeof`/`Offsetof`/`Alignof`). This is a Goose change: fold
   them to constants for one target.
2. **A byte-level view of pointer-free ("plain old data") structs.** Typed memory and its
   bytes must be the same memory, in both directions, with a fixed encoding. This is the core
   change: it changes what the heap is.
3. **Byte-offset pointer arithmetic within one allocation**, pointer differences, and an
   alignment test on addresses: the `uintptr` patterns.
4. **Slices built over raw memory** (`unsafe.Slice`, and conversion to a pointer to a huge
   array followed by slicing). These alias typed memory, so they rest on 2.
5. **A file-backed, read-only `mmap` region**, coherent with `WriteAt` and invalidated by
   `munmap`. This is not `unsafe` but `syscall`/`x/sys/unix`. Every page read goes through it,
   so it cannot be separated from 2–4.

The rest (hashing struct bytes, an `int64`/`time.Duration` pointer cast, a debug dump) follows
from 2 or is trivial. Some useful facts make the job smaller:

- Every type bbolt puns is pointer-free fixed-width integers. Bytes never have to carry
  pointers, so the model needs no pointer provenance in memory.
- No punned struct has padding.
- Every pun stays inside one allocation.

The alternative is a **bbolt fork**, as `upamanyus/etcd` (`goose-lean`) is for etcd. It would
encode and decode pages explicitly with `encoding/binary.LittleEndian` (which Perennial models)
instead of punning. That removes 1–4. 5 stays, unless the fork also replaces the mmap with
`ReadAt`, which changes the zero-copy behaviour of `Get`.

## Inventory

Every non-test use in the packages a proof would cover (`.`, `internal/common`,
`internal/freelist`; Linux files only for the OS layer). "Kind" refers to the numbered list
above.

| Site | What it does | Kind |
|---|---|---|
| `internal/common/page.go:10–16`, `bucket.go:8` | `PageHeaderSize = Sizeof(Page{})` (16), `Branch/LeafPageElementSize` (16, 16), `pgidSize` (8), `BucketHeaderSize = Sizeof(InBucket{})` (16) | 1 |
| `internal/freelist/shared.go:284`, `bucket.go:762`, `inode.go:73,108`, `page.go:87,102,118,142,163` | `Sizeof(*p)`, `Sizeof(Pgid(0))`, `Sizeof(InBucket{})` in expressions | 1 |
| `bucket.go:119` | `Alignof(struct{InBucket; Page}{}) - 1`: the alignment mask (8 on 64-bit) | 1 |
| `internal/common/meta.go:63` | `Offsetof(Meta{}.checksum)` (56) | 1 |
| `internal/common/utils.go:11,15,19` (`LoadBucket`, `LoadPage`, `LoadPageMeta`) | `(*InBucket)/(*Page)/(*Meta)(unsafe.Pointer(&buf[k]))` | 2 |
| `db.go:1132` (`DB.page`), `db.go:1137` (`pageInBuffer`) | `(*Page)(unsafe.Pointer(&db.data[id*pageSize]))`: a page of the **mmap**, or of a buffer | 2, 5 |
| `db.go:1173` (`allocate`), `tx.go:432` (`writeMeta`) | a `*Page` over a fresh `make([]byte, n*pageSize)` or a page-pool buffer | 2 |
| `bucket.go:132–139` (`openBucket`) | an `*InBucket` over a bucket **value** (in the mmap, or in a page buffer), and the inline root `*Page` 16 bytes into it | 2 |
| `bucket.go:763,842–846` (`spill`, `write`) | `*InBucket` and an inline `*Page` over a fresh value buffer, written through | 2 |
| `internal/common/bucket.go:49` (`InlinePage`) | `(*Page)(unsafe.Pointer(&v[BucketHeaderSize]))` | 2 |
| `internal/common/unsafe.go:7–13` (`UnsafeAdd`, `UnsafeIndex`) | `unsafe.Pointer(uintptr(base) + offset [+ n*elemsz])` | 3 |
| `page.go:87` (`Page.Meta`), `page.go:102,118` (`Leaf/BranchPageElement(i)`), `page.go:142,163` (freelist ids) | the struct after the page header, the `i`-th 16-byte element, the `Pgid`s: all through `UnsafeAdd`/`UnsafeIndex` | 2, 3 |
| `internal/common/inode.go:87,93` (`WriteInodeToPage`) | `elem.pos = uintptr(&b[0]) - uintptr(elem)`: a **pointer difference** stored on the page | 3 |
| `bucket.go:123` (`openBucket`) | `uintptr(unsafe.Pointer(&value[0])) & mask != 0`: an **absolute-address** alignment test | 3 |
| `db.go:1126` (`DB.Info`) | exports `uintptr(&db.data[0])` (debugging) | 3 (a value only) |
| `internal/common/unsafe.go:15` (`UnsafeByteSlice`) | `(*[MaxAllocSize]byte)(UnsafeAdd(base, off))[i:j:j]`: a `[]byte` over struct memory | 4 |
| `page.go:257,313,320` (`branch/leafPageElement.Key/Value`) | the key/value bytes at `elem + pos`: a `[]byte` aliasing the page, which `Get`/`Cursor` **return to the user** | 2, 3, 4 |
| `inode.go:81` (`WriteInodeToPage`) | a `[]byte` window into the page to `copy` keys and values into | 4 |
| `page.go:112,128,164`, `shared.go:301,306` (freelist `Write`) | `unsafe.Slice((*leafPageElement/*branchPageElement/*Pgid)(data), n)`: typed slices over a page | 4 |
| `page.go:171` (`Page.hexdump`, debug), `tx.go:543,582` (`Tx.write`) | the bytes of a heap `*Page`, for `WriteAt` and to zero it back into the pool | 2, 4 |
| `bolt_unix.go:57–71` (`mmap`), `:84` (`munmap`) | `unix.Mmap(fd, 0, sz, PROT_READ, MAP_SHARED)`, `Madvise`; `db.data = (*[MaxMapSize]byte)(unsafe.Pointer(&b[0]))` | 5 (+4) |
| `bolt_linux.go:9`, `bolt_unix.go:18–51`, `mlock_unix.go` | `Fdatasync`, `Flock`, `Mlock` | 5 (OS, not unsafe) |
| `internal/common/meta.go:63` (`Meta.Sum64`) | FNV-64a of the first 56 bytes of a `*Meta`, which is **typed** (`tx.meta = &common.Meta{}`, `tx.go:52`) or in the mmap (`db.meta0 = db.page(0).Meta()`) | 2 (struct → bytes) |
| `tx.go:898,902` | `(*int64)(unsafe.Pointer(*time.Duration))` for `sync/atomic` | trivial (same representation) |
| `node.go:515` (`node.dump`, debug) | `(*bucket)(unsafe.Pointer(&item.value[0]))` | 2 (debug only) |

Goose itself rejects (`[unsupported]`) only `unsafe.Sizeof`/`unsafe.Slice` calls and the
constants built from them, and, outside `unsafe`, the labeled `continue retry` in `DB.Batch`
(`db.go:1034`) and the anonymous-struct field `DB.ops` (`db.go:38`). It translates the casts
silently to `Convert`. Those are the errors you get by running the pinned translator over the
whole package with bodies (`translate = ["*"]`).

## Layouts (linux/amd64 and arm64)

Measured with `unsafe.Sizeof`/`Offsetof` (the same on 386, except the alignment):

| Type | Size | Fields (offset) |
|---|---|---|
| `Page` | 16 | `id` 0, `flags` 8 (u16), `count` 10 (u16), `overflow` 12 (u32) |
| `branchPageElement` | 16 | `pos` 0, `ksize` 4, `pgid` 8 |
| `leafPageElement` | 16 | `flags` 0, `pos` 4, `ksize` 8, `vsize` 12 |
| `InBucket` | 16 | `root` 0, `sequence` 8 |
| `Meta` | 64 | `magic` 0, `version` 4, `pageSize` 8, `flags` 12, `root` 16, `freelist` 32, `pgid` 40, `txid` 48, `checksum` 56 |

None has padding, and all fields are fixed-width unsigned integers. The file format is the
machine's byte order (native endian), so a model fixes one target, little-endian. A page on
disk is: the header, then `count` 16-byte elements, then the keys and values, each element's
`pos` counting from the element itself. Branch elements carry the child page id. A freelist
page carries `count` `Pgid`s, or a count in the first `Pgid` if there are 65535 or more. A meta
page is the header followed by a `Meta`.

## What each kind requires

### 1. Layout constants

`Sizeof`, `Offsetof` and `Alignof` are compile-time constants in Go (`go/types` computes them,
`types.SizesFor("gc", "amd64")`). Goose can fold them when it translates, for one fixed target,
just as it already folds other constants. The proof then states the target: 64-bit and
little-endian. This is a small change to the translator.

### 2. The byte view of plain-old-data structs (the core)

bbolt treats one region of memory both as `[]byte` and as `Page`/`Meta`/elements, in **both
directions**:

- **bytes → struct.** A `*Page` is read from a fresh `make([]byte)`, a pool buffer, the mmap, or
  a bucket value. Its fields are stored through (`p.SetOverflow`, `SetId`,
  `*page.Meta() = *tx.meta`) and loaded back.
- **struct → bytes.** `Tx.write` hands the bytes of a `*Page` to `WriteAt` and zeroes them.
  `Meta.Sum64` hashes the bytes of a typed `*Meta` (`tx.meta`, allocated as `&common.Meta{}`, not
  as bytes). Keys and values are `[]byte` windows into the page.

What has to hold: for a pointer-free fixed-layout type `T` (an integer, or an array or struct of
such types, with no pointers, slices, strings, maps or interfaces) with an encoding
`encode : T → List byte` of length `Sizeof(T)` for the target,

```
l ↦* encode v   ⊣⊢   l ↦ v        (and a field of v at its byte offset)
```

as an equivalence of ownership: the same memory, owned once. A store through either view must
be visible through the other.

Perennial today: a typed points-to `l ↦ v` holds a `val` of the right shape. A struct is laid
out field by field over cells, and a `[]byte` is an array of byte cells. A load of `Page.ty` at
a location holding byte cells is not defined. The conversion `(*Page)(unsafe.Pointer(p))`
already exists and is the identity on locations, so the gap is entirely in what memory is.

The ways to close it:

- **Byte-granular memory for POD.** The heap holds bytes for these types. A load or store of a
  fixed-width integer at a byte offset is a multi-byte access that decodes or encodes, and
  `l ↦ v` for a POD `T` is defined as `l ↦* encode v`. The equivalence is then true by
  definition, in both directions, so `Sum64` over a typed `Meta` is covered too. This is the
  honest model, and the large change: the GooseLang heap and the field-offset arithmetic
  (`structFieldRef`, `arrayIndexRef`) move to byte offsets for POD types.
- **Restricting it to byte blocks.** Make only memory allocated as `[]byte` (by `make`, the page
  pool, `mmap`) reinterpretable, by a ghost re-typing between `l ↦* bs` and `l ↦ decode bs`.
  Every bytes → struct pun in bbolt targets such a block. But `Meta.Sum64` goes the other way
  (over `tx.meta`), so this needs a one-line fork (allocate `tx.meta` in a byte buffer, or hash
  an explicit encoding) or the first option.

Alignment: Go requires a `*T` to be aligned for `T`, and bbolt keeps it so. Page buffers start
page-aligned or at 8-byte alignment from the allocator. The elements sit at offsets that are
multiples of 8 from the page start. `openBucket` copies a value that is not 8-aligned. So a
model can require alignment for typed accesses, as long as it knows that heap and mmap blocks
start aligned (see 3).

### 3. `uintptr` arithmetic, differences and alignment tests

Go's rules for `unsafe.Pointer` (pattern 3) let `unsafe.Pointer(uintptr(p) + off)` be written
in one expression, if the result stays inside the allocation `p` points into. bbolt uses:

- **Offset**: `UnsafeAdd`/`UnsafeIndex`, for the struct after the header, the `i`-th element,
  and `elem + pos` for keys and values. A model needs `p +ₗ n` in **bytes** within one
  allocation, with typed accesses at the result (by 2). Goose could translate the pattern as
  `unsafe.Add(p, off)` (a primitive) and not as two conversions. Perennial's semantics must not
  give a `uintptr` that came from a pointer an arbitrary value in general.
- **Difference**: `uintptr(&b[0]) - uintptr(elem)` in `WriteInodeToPage`. Both point into the
  same page buffer, and the result is stored as `pos`. It needs "the difference of two
  addresses in one block is the difference of their offsets".
- **Absolute alignment**: `uintptr(&value[0]) & 7` in `openBucket`. It needs the address modulo
  8, which is `base(block) + offset` modulo 8 when blocks start 8-aligned. Since both branches
  are safe (the unaligned one copies), a model could also leave it nondeterministic. `DB.Info`
  only exports an address.

The model: a `uintptr` taken from a pointer is `base(block) + offset`, with `base` fixed,
unknown and aligned. Converting back is allowed only to the same block, within bounds, which is
what Go's `checkptr` accepts. Since pointers are never stored in bytes, this provenance never
has to be in memory.

### 4. Slices over raw memory

- `UnsafeByteSlice(base, off, i, j)` is `(*[MaxAllocSize]byte)(base + off)[i:j:j]`. It converts
  to a pointer to a 2 GiB array that is never materialized, then slices it. It is in effect
  `unsafe.Slice((*byte)(base+off+i), j-i)` with capacity `j-i`.
- `unsafe.Slice((*T)(p), n)` is used for elements, `Pgid`s and freelist ids.
- `db.data` is `(*[MaxMapSize]byte)` (256 TiB) over the mmap, indexed by page offset.

A model needs the slice of `n` `T`s at `p`, `{ptr := p, len := n, cap := n}`, owned as
`n·Sizeof(T)` bytes at `p` (by 2). It also needs the pointer-to-huge-array-then-slice pattern
treated as that, not as an array of `MaxAllocSize` elements. The slices must alias the typed
view: a key that `Get` returns is bytes of the page that `elem.pos` points into.

These slices also **escape**: `Bucket.Get`, `Cursor.First/Next/...` return keys and values that
point into the mmap (or into a page buffer of a write transaction). They are valid only while
the transaction is open. A spec needs read-only ownership of those bytes for the transaction's
lifetime, which ties into 5.

### 5. The mmap (not `unsafe`, but inseparable)

- `unix.Mmap(fd, 0, sz, PROT_READ, MAP_SHARED)` returns `[]byte` whose contents **are the
  file's**. It stays coherent: a page written with `file.WriteAt` (`Tx.write`) is seen through
  the mapping by later readers, through the unified buffer cache (OpenBSD needs `msync`,
  `bolt_openbsd.go`). Writes through it fault (`PROT_READ`).
- `munmap` (in `DB.mmap`, when the file grows) invalidates every slice into it. bbolt makes this
  safe with a protocol: every read transaction holds `mmaplock.RLock()` from `beginTx` to
  `removeTx`. Remapping takes `mmaplock.Lock()`, and before it the write transaction copies
  every key and value its nodes reference out of the mmap (`Bucket.dereference`,
  `node.dereference`).
- Durability: `fdatasync` after the data pages, then the meta page, which carries the
  checksum of 2/`Meta.Sum64` (FNV-64a, `hash/fnv`, not modeled in Perennial). Recovery picks the
  newer meta whose checksum validates.

A model needs a mapped region whose read-only points-to follows a ghost file state: `WriteAt`
updates the file and what the mapping shows. `munmap` consumes the region's ownership. It also
needs a crash model for the file (which writes survive, page by page, around `fdatasync`).
Perennial has `DiskPrelude`/`GrovePrelude` but no file + mmap model, and no `syscall`,
`golang.org/x/sys/unix` or `hash/fnv`.

### Trivial cases

- `tx.go:898,902`: `(*int64)(unsafe.Pointer(&d))` for `d : time.Duration` (underlying `int64`).
  A pointer conversion between types of the same representation: one rule, or a fork that
  uses `atomic.Int64`.
- `node.go:515`: a debug dump. Leave it unverified.

## The alternative: a fork

A fork in the style of `upamanyus/etcd` `goose-lean` would make 1–4 unnecessary:

- `internal/common`'s accessors read and write the page bytes explicitly
  (`binary.LittleEndian.Uint64(buf[8:])`, ...), which Perennial models. Keys and values become
  plain subslices (`buf[off+pos : off+pos+ksize]`), `pos` an integer offset with no pointer
  difference, `Sum64` over an explicit encoding, and the alignment test disappears.
- Pages become `[]byte` plus an offset, not `*Page`.

The cost: the verified code is no longer upstream's, in its most performance-sensitive part. The
format stays bit-compatible on little-endian targets only. 5 remains unless the fork also reads
pages with `ReadAt` instead of the mmap, which changes `Get`'s zero-copy semantics (values would
be copies) and the remap protocol.

Upstream bbolt as written needs 1–5 in Perennial. 1 is a translator change. 2 is the real one,
and it decides the cost. 3 and 4 are small once 2 exists. 5 is a new OS model, needed either
way.

## What is verified now

Only the code that touches none of this: `internal/common`'s page-id helpers (`Pgids.Merge`,
`Mergepgids`), translated with bodies (`Code/go_etcd_io/bbolt/internal/common.toml`), with
`Mergepgids` specified and proved (`{Spec,Proof}/go_etcd_io/bbolt/internal/common/`). Most of `internal/freelist`
(`array`, `hashMap`, `shared` except `Read`/`Write`/`EstimatedWritePageSize`) and the `errors`
package are equally goosable.

## Where Perennial stands (2026-10-10, `lean` at `6ffd21fce`)

Looking at Perennial's Go semantics to place the models turned up three facts that come
before any bbolt-specific model.

1. **Allocating an array diverges.** `ArraySemantics.alloc_array`
   (`Perennial/Golang/Defn/Array.lean:31`, marked `-- TODO`) steps
   `GoAlloc (ArrayType n elem)` to `AngelicExit`, which steps to itself forever. A `make` with
   non-zero capacity goes through it (`InternalDynamicArrayAlloc`, `Defn/Slice.lean:85`), so
   every Hoare triple holds vacuously from the first non-empty slice or array allocation on.
   `wp_alloc` for arrays is proved by `wp_AngelicExit` (`Theory/Array.lean:342`), and
   `wp_slice_make3` gets its array from that `wp_alloc`. This affects proofs in this repository
   as well, not only bbolt: 31 files under `Proof/` use `wp_slice_make*` or `wp_slice_append`
   (whose reallocating branch allocates), e.g. `raft__campaign`, `unstable__shrinkEntriesArray`.
   `etc/tcb-report.py` does not show it, because it is a field of a semantics class, not an
   axiom.
2. **No byte-level memory.**
   - A heap cell holds one `val`.
   - `structFieldRef`/`arrayIndexRef` are uninterpreted functions, indexed by the Lean
     representation type (`GoSemanticsFunctions`, `Defn/PostLang.lean:80-105`).
   - No type has a size.
   - The only layout fact is that a byte array occupies consecutive cells
     (`arrayIndexRef_add_loc_add : arrayIndexRef w8 i l = l +ₗ i`, added for the disk FFI).

   So a `w64` in memory is one cell, and nothing can make it also be 8 byte cells. A byte view
   cannot be added downstream (as a trusted model here) consistently with the existing classes.
   The `[]Pgid` that `unsafe.Slice` makes over a freelist page (`FreelistPageIds`,
   `shared.Write`) is read and written as ordinary `Pgid`s by generic code (`copy`,
   `Mergepgids`), so even lowering the punned *struct* types in the translator would leave it
   unmodeled.
3. **No crash semantics.** `GooseLang/Lang.lean` has none (its header says so). The disk FFI
   (`GooseLang/Ffi/DiskFfi`) is a block map with read/write/size. A file + mmap model can be
   stated (as an FFI, or as trusted Go-level code), but bbolt's crash safety (`fdatasync`, the
   meta page's checksum, recovery from the newer valid meta) cannot be stated until Perennial
   has crash semantics.

What this means for "verify bbolt":

| Piece | Where | Size |
|---|---|---|
| Real array allocation (fix 1) | Perennial core, `ArraySemantics` and `wp_alloc` for arrays | moderate; needed by everything |
| Byte-level integers: `wN` = N byte cells, little-endian; `arrayIndexRef V i l = l +ₗ i·size V`; `structFieldRef` at gc's offsets; `Convert` pointer ↔ `uintptr` within a block | Perennial core (`GoSemanticsFunctions`, `PredeclaredSemantics`, the `heapTypedPointsto` instances and their `wp_load`/`wp_store`) | large; changes the memory model every Perennial proof sits on |
| `unsafe.Slice`, `unsafe.Add`, `(*[N]T)(p)` over raw memory, pointer differences | Goose plus `unsafe.Semantics` | small, after the previous row |
| File + mmap (coherent with `WriteAt`, `munmap`, `flock`, `fdatasync`) | a new FFI (Goose's `ffiMapping`, a prelude, `FfiSemantics`, adequacy) or trusted code | moderate without crashes |
| Crash semantics | Perennial core (`Lang.lean`, recovery WP) | large |
| bbolt itself (~5,600 Go lines: freelist, page codec, node split/rebalance, cursor, bucket, tx, DB, remap protocol, MVCC through pending pages) | here | large; tens of thousands of proof lines by this repository's ratios |

Done so far toward the translation (Perennial branch `goose-bbolt`, `ff60796`, pushed): Goose
folds `unsafe.Sizeof`/`Offsetof`/`Alignof` to gc's values, translates `uintptr` constants, and
supports labeled loops whose branches target the loop directly (`DB.Batch`'s
`continue retry`). The goose tests pass with new cases in `testdata/examples/unittest`. What is
left for bbolt to translate in full is `unsafe.Slice` (4 sites) and the anonymous-struct field
`DB.ops`. Both need the byte-level memory first to mean anything: the field is a test hook for
`WriteAt`.
