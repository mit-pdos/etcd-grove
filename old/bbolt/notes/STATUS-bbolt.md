## bbolt: the read path, the writer's beginning and its buckets verified, sequential use (2026-10-12)

**Branch.** etcd-grove branch `bbolt`, pinned to Perennial branch `goose-bbolt` (`793297d`,
not merged into Perennial's `lean`; builds here use `.lake/perennial-dev`). Merging needs
Perennial's branch merged first and the repository rebuilt against it.

**The models** (`notes/bbolt-unsafe.md`, "The models"): integers are little-endian byte
cells, gc's sizes and layouts, real array and struct allocation, `unsafe.Add`/`unsafe.Slice`;
the file and the memory map are `Proof/os/FileModel.lean` (axioms for the `os`, `syscall`,
`unix` functions bbolt calls). No crash semantics. The plan: `notes/bbolt-proof-plan.md`.
Linux (`Proof/runtime/GOOS.lean`, an assumption class), `Mlock` off.

**Goose fix** (Perennial `f553888`): a `return` in a function with named results and a
`defer` did not assign the named results, so a deferred closure saw stale values and its
assignments were lost (`DB.mmap` skipped its rollback `munmap`; `safelyCall`'s recovered
error was dropped). Such a function now allocates its results around `with_defer:`, a
`return` stores into them, and it returns them after the deferred calls (13 bbolt functions
retranslated, nothing else in this repository or Perennial's translations changed; semantics
tests `testNamedResultDefer`, `testNamedResultShadowed`).

**The database predicate** (`Proof/go_etcd_io/bbolt/DBPred.lean`), sequential use (one
goroutine uses the database; any number of read transactions open; at most one writer):
`ownDB` holds the DB's fields (the logger and `pageSize`, never written after `Open`,
persistent; `data` shared with the transactions at fractions; `freelist` shared with the
writer), the file and mapping, every mapped slot at the fraction no transaction holds
(`FilePages`, `SlotsCarve`) and the tail after the whole slots (`mapTail`, for a remap's
`munmap`), the freelist (`ownFL` of an implementation of the freelist interface), the page
pool (`isPool` of zeroed page buffers), `metalock`, `rwlock` (held while a writer is open),
`mmaplock`'s unused read handles and each reader's ghost token (so the write lock knows no
reader is open), and a ghost map of the readers. `dbOK`: the metas (one valid), the current
tree (well-formed, inside the mapping, its pages ending below the high-water mark; pending
only for the open writer, which frees them), the readers' and the writer's views the file's,
bbolt's MVCC rule (a slot a view covers is no meta, not free, pending only from a newer
transaction), the views agreeing where they overlap and no reader newer than the current
tree (`viewsAgree`: a page the writer frees has the allocation any reader seeing it saw),
the accounting of the fractions, and the freelist (`flBelow`: below the high-water mark,
every pending transaction committed or the writer's, the txid not wrapping, ids below
`2^62`). `ownReadTx`: a reader; `wtxInit`:
what `beginRWTx` hands the writer (its object graph's predicate is the write agent's work,
`WriteTxPred.lean`, in progress).

**Proved** (no `sorry`; each package's `Results.lean` prints its axioms):
- `internal/common` (117 results, `gen-link.py --bbolt`): all but `Meta.Print`,
  `Page.hexdump` (an `io.Writer`) and `CopyFile` (filesystem); `hash/fnv`, `os.Getenv`/
  `Setenv`/`Unsetenv`, `strings.ToLower` are trust-boundary axioms.
- `internal/freelist` (44, `--bbolt-freelist`): the array freelist, all of `shared` (also
  `Rollback`, `release`, `releaseRange`, `ReleasePendingPages`: Perennial's map range does
  allow deleting), the interface contract (`Iface.lean`, `ArrayIface.lean`), `hashMap.addSpan`;
  `sort.Sort` an axiom.
- the root package (237, `--bbolt-root`): statistics, accessors, `mmap`/`munmap`,
  `mmapSize`, `db.page`, `db.meta`, `Tx.page`, `Tx.init`, `beginTx`, `beginRWTx` (the
  freelist's pending pages no reader sees released), `removeTx`, `Begin` (both kinds),
  `Tx.close`/`Rollback` (read), `View`, the logger (`DB.Logger`, the default logger's
  `Errorf`; `log.Logger.Output` an axiom), `fileSize`, `grow`, the cursor read path, the
  bucket read API (`Bucket.Get`, `Tx.Bucket`, `ForEach`, ...), `node.go` but the
  graph-shaped parts. `sync.Pool` (`Proof/sync/PoolModel.lean`) and `os.FileInfo`
  (`Proof/os/FileInfoAlias.lean`) are trust-boundary models.
- the mapping and the allocator: `db.mmap` (for `Open` and for a remap: the readers'
  tokens show none is open, the writer is dereferenced, the metas are read out of the new
  mapping, the deferred rollback `munmap`s), `db.allocate` (the page pool or a new buffer; a
  freelist run, or the high-water mark with the mapping grown), over `DBRemap.lean`
  (`remap_gather`, `remap_carve`, `dbOK_remap`), `DBAlloc.lean` (`dbOK_allocate`, ...),
  `AllocPage.lean`; `Open`'s leaves `flock`, `funlock`, `fdatasync`, `hasSyncedFreelist`,
  `getPageSizeFromFirstMeta`, `init` (a fresh database's file, `initBytes`); `close` and
  `Close` (the locks show no transaction is open; the file is given back to the file system
  under its path); `getPageSize` and `getPageSizeFromSecondMeta` (the probes at
  `1024 << i`; a short read at the end of the file is compared with `io.EOF`).
- the writer (the write agent's, then mine): its cursor, `Cursor.node`, `Bucket.Put`,
  `Bucket.Delete`, `SetSequence`, `NextSequence`, `Bucket.Bucket` (`openBucket`), `Bucket.write`,
  `CreateBucket`, `CreateBucketIfNotExists`, `Bucket.dereference`, `node.dereference`,
  `Tx.allocate`, `node.splitTwo` (`WriteSplit.lean`); `DBFree.lean`: the writer frees a page
  of its view (`dbOK_free`, `ownDB_free`, for `node.free`: `Free` does not panic, MVCC kept).
  A writer `Begin` returns is `ownWriteTx` (`ownWriteTx_begin`, from `beginRWTx`'s `wtxOK`: the
  current tree is `treeStrict`, now a `currentOK` fact). Its `Rollback` (`Tx.Rollback.wspec`,
  `nonPhysicalRollback`, `close`; `DBRollback.lean`: the freelist's `Rollback` does not panic,
  the writer's pending pages having been allocated before its view, and the writer's view is
  given back): a writer's life without `Commit` is verified.
- `Open` of an existing well-formed file (`DBOpen.lean`: `fileWF`, the current tree strict and
  inside the file, the freelist synced, below the high-water mark; `pageSizeOK`: `getPageSize`
  finds the file's page size, also through its probes after an I/O error, the forged-meta
  finding as an assumption; the options: no logger, the array freelist, the file's page size,
  read-write). Every error path closes the database and gives the file back; on success the
  database's predicate (`openState`, `dbOK_open`), its freelist read from the freelist page
  (`loadFreelist`: its `sync.Once` run fresh, `Proof/sync/OnceFresh.lean`; the page's ids as a
  `uint64` slice, `FLPage.lean`, `U64Bytes.lean`; a meta's bytes determine it, `MetaInj.lean`),
  its locks, ghost state and page pool set up. Not yet: a new (empty) file (`init`'s file
  `fileWF`).
- The writer's shape (`WriteTxShape.lean`, design in `notes/bbolt-proof-plan.md`, "The spill
  and `Commit`"): the B+tree's keys (`TreeKeys.lean`, now in `treeStrict`), opened buckets tied
  to their entries, ghost page tokens for disjointness. Proved with it (`sspec`s, `_s` files):
  `Bucket.node`, `Cursor.node`, the cursor's descent by a key (`Cursor.seek`/`search`: Perennial's
  `sort.Search` spec restated with the index it last evaluated), `Put`, `Delete`,
  `Bucket.Bucket`, `CreateBucket(IfNotExists)`, `Set`/`NextSequence`, the `Tx` wrappers, the shape
  at `Begin`; the rebalance (`Rebalance*.lean`: its post `txShapeR`/`rblTxOK`, weaker key bounds,
  acyclic parents, uniform leaf depth). In progress: the spill.
- `Commit`'s database side: `Tx.write` (dirty pages through `db.ops.writeAt`, `ownDB`'s `%Hops`;
  `dbOK` kept by writes to unseen slots, `DBWrite.lean`), `writeMeta`, `commitFreelist`, the
  writer's `rollback` (`dbOK` now records the current freelist page, `flCurOK`, and readers'
  high-water marks); a failed remap keeps the transaction, the database lost (`DBLost.lean`).
- `Open` of a new (empty) file too (`DBOpenInit.lean`: `fileWF (initBytes ps) ps`).
- The hashMap freelist (every function, its interface contract; `hashMap.Init([])` keeps a stale
  cache, so not `InitSpec`); `Reload` of a page holding pending ids; the logger's methods,
  `DB.Stats`, `DB.Sync`, `panicked.Error` (new trust-boundary axioms: `fmt.Sprint`, `os.Exit`,
  `log.Logger.Flags`/`SetFlags`, `sort.SliceIsSorted`, `reflect.DeepEqual` of page-id sets,
  `sort.Sort` of page slices; the
  TCB baseline is not updated yet). `safelyCall` needs `recover`, which Perennial does not model.
- Coverage (bbolt v1.5.0's non-test files): 323 of 378 functions, 3485 of 4811 lines; the freelist
  complete; left in the root package mostly `Commit` and its pieces (`tx.go`), the spill and
  rebalance (`bucket.go`, `node.go`), `Update`/`Batch`, `Check` (`tx_check.go`), `Compact`.
- the errors bbolt compares with its error variables are well-formed (`Proof/os/ErrWF.lean`:
  an error holds a pointer of a pointer type or is a `syscall.Errno`, so comparing it with
  another does not panic; `ErrShape.lean`: `errors.New`, `fmt.Errorf` return pointers):
  `Stat`, `ReadAt`, `Mmap` say so of theirs.
- `wip/` holds the write agent's unfinished `WriteTxClean.lean`.

**Safety findings** (preconditions that rule out a reachable panic or a false spec):
`Rollback` inside `View` panics (`managed`); an empty branch page would make the cursor read
garbage (branches need an element); `mmapSize` overflows for a page size of 2^32 or more;
`node.put` needs `pgId < meta.pgid` and non-empty keys; `node.write` fewer than 65535
inodes (with a page size above about 1 MiB a leaf of that many fits one page:
`Options.PageSize`); more than 2^30 - 1 open readers overflow `mmaplock`;
`recursivelyInspect` dereferences nil when `seek` misses; `openBucket` needs an inline
bucket's value longer than 16 bytes; `grow` needs the file no longer than the mapping. The
file must be well-formed: a nested bucket inside an inline one, a page shared by two
parents (freed twice), an empty first key (`node.read`), a freelist id at the high-water
mark or above (`node.spill` panics), a page running past the high-water mark. A failed
remap (the `mmap` system call) leaves `db.data` nil: the next `Begin` dereferences it. If the
first meta page cannot be read (an I/O error), `getPageSize` probes the file at `1024 << i`
for any valid meta: a value holding a forged one (a valid checksum) at such an offset sets
the page size (`Open` will assume the file's valid metas agree on it). `Tx.write` panics for a page size
above `MaxAllocSize` (2^31 - 1; `UnsafeByteSlice` when it gives single pages back to the pool).
If `writeMeta`'s write reaches the file and then fails (a short write past the meta's 80 bytes,
or `fdatasync` failing), `Commit` rolls back over a database whose newest valid meta is the new
one: `Reload` frees the pages the transaction freed while open readers may still see them.

**Perennial** (`goose-bbolt`, `793297d`): `delete` and `clear` take any type whose underlying
type is a map, as `len` does (`hashMap`'s `pidSet` was stuck); `io`'s initialization gives
`EOF`, an `errors.New` pointer (`errors.wp_New_ptr`). Still gaps: float conversions
(`node.splitTwo`, `rebalance`; `FloatConv.lean` a class meanwhile); a package's
`Assumptions` should include the types it reaches through others (`hash.Hash64`);
`os.FileMode`'s underlying type (an `OsFileInfoAssumptions` field: Perennial's `os` keeps it
opaque);
`runtime.GOOS` constants, the `os.FileInfo` alias; moving `SliceWithin` into Perennial.

**TCB.** `etc/tcb-baseline.txt` has bbolt's model axioms (`--check --update`, 2026-10-12).

**Model changes this round.** bbolt's package initialization gives `discardLogger`
(`bboltRootInit`, assumed as `errors`' is); the `os` axioms: `OpenFile`'s file is null exactly
on an error, `File.Close` takes the file whatever its mapping (on Linux a mapping outlives its
file: `mmap`'s `Madvise` failure leaks one, which `close` then cannot unmap).

**Next.** `Open` of a new file (`fileWF (initBytes ps) ps`); `node.split`, `node.spill`, `Bucket.spill`, `node.free` (over `ownDB_free`),
the rebalance, `DeleteBucket` (`Bucket.free`); the hashMap freelist (now that `delete` on
`pidSet` steps); `Commit` (freelist write, page writes, `writeMeta`, `grow`; the written tree
`treeStrict`); `Batch`.

