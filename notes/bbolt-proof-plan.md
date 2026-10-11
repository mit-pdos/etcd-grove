# bbolt: the plan of the proof

How the verification of bbolt (v1.5.0, branch `bbolt`) is organized, on the provisional
memory model of Perennial `goose-bbolt` (`notes/bbolt-unsafe.md`, "The models"). No crash
safety: `Sync`/`Fdatasync` are no-ops, recovery is not modeled.

## What the specs say

Bottom-up, every Go function gets a spec and a proof (no `sorry`). The specs are of two
strengths:

- **Functional** where the state is small: `internal/common` (accessors, page views, inode
  read/write against `PageModel.lean`), the freelist (`FLState`: free ids, pending pages per
  transaction, allocations, read-only transactions), the statistics, the file and mapping
  (`mmap`, `munmap`, `grow`, `mmapSize`).
- **Safety and structure** for the B+tree (node, cursor, bucket, tx, db): the code does not
  panic and every unsafe access is in bounds, given the database invariant; operations
  preserve it. What a key maps to is not tracked (yet): a functional key-value spec on top is
  later work.

## The database invariant

- **The file and its mapping** (`Proof/os/FileModel.lean`): `fileBytes fd bs`, the mapping
  `fileMap fd (some (data, sz))`, and the caller's half of the mapped cells.
- **Pages** (`Proof/go_etcd_io/bbolt/PageModel.lean`): page `id` is the `pageSize` bytes of
  `bs` at `id * pageSize` (`1 + overflow` pages for an overflowing one); every page reachable
  from a valid meta (the root bucket's tree, inline buckets' trees, the freelist page) is
  well-formed (`leafWF`, `branchWF`: elements, keys and values inside the page; children
  below the meta's high-water mark `pgid`), and below the high-water mark, inside the file
  and the mapping.
- **Readers and writers**: the mapped cells of a page are shared among the read
  transactions that can see it (fractions of the caller's half); a writer writes (through
  `WriteAt`) only pages no open transaction can see: the freelist's free pages and the pages
  it allocated, never pending ones (bbolt's MVCC). The freelist state records exactly this
  (`FLState.pending`, `readonly`).

## A transaction's objects

A writable transaction materializes nodes (`node`) for the pages it changes; nodes point to
their parent, children and bucket, buckets to their transaction and a node cache: a graph.
It is owned as one predicate over finite maps (location ↦ node value, location ↦ bucket
value) whose invariant ties the pointers together (each cached node's `bucket`, its
`parent`'s `children` containing it, ...). Node keys and values are slices into the mapping
(fragments of the reader's half, from `ReadInodeFromPage`) or into heap copies (`Put` clones
its arguments; `dereference` copies on a remap).

## Order

1. `internal/common`: the rest (freelist pages, `Meta` checksum through `hash/fnv`,
   `ReadInodeFromPage`/`WriteInodeToPage`, `InlinePage`, `verify.go`).
2. `internal/freelist`: `shared` + `array`, then `hashMap`.
3. The root package's leaves: statistics (atomics), errors, logger, options.
4. Pages in the DB: `db.page`, `db.meta`, `pageInBuffer`, `allocate`, `grow`, `mmapSize`,
   `db.mmap`, `init`, `Open`, `close`.
5. Nodes, cursors, buckets, transactions (`Commit`: spill, freelist write, `write`,
   `writeMeta`), `Update`/`View`/`Batch`.
