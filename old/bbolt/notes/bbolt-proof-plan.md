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

## The write path (design, 2026-10-12)

Sequential use, as for the read path (`DBPred.lean`): the caller holds `ownDB` and passes it to
every call. A writer is a reader of the current tree too (it reads its pages through the
database's slots, at a fraction it carves like a reader, `SlotsCarve`), plus heap objects.

**Two layers.**
- *The transaction's objects* (the `Tx` struct, its meta copy, `tx.pages`, the bucket/node
  graph): an agent's predicate `ownWriteTx` (in its own files). Nodes are a finite map from
  location to node record (entries as `NodeModel.lean`'s `NodeEntry`s, parent, children,
  pgid), with the structure invariant (each node's `bucket` is its bucket, its `parent`'s
  `children` hold it, `b.nodes` maps a node's page id to it, `b.rootNode` the root). It
  *refines* a page tree: the tree the transaction would write is the file's current tree
  with each materialized node's page replaced by the node's entries; that tree stays
  well-formed (`treeWF`-like, over node entries and file pages) through `Put`/`Delete`/
  `CreateBucket`, and `spill` turns it into page buffers (`tx.pages`) whose bytes are
  `treeWF` pages, the old pages of spilled nodes freed (`freelist.Free`: pending for this
  transaction).
- *The database* (mine): `ownDB` with a writer open (`rwtx`, `rwlock`), `beginRWTx`,
  `Tx.allocate`/`DB.allocate` (a free run from the freelist, or the high-water mark moved;
  `grow` and the remap under `mmaplock`'s write lock: the write lock's token shows no reader
  is open, so the mapping's cells are all the database's), `Tx.write` (the dirty pages
  through `WriteAt`: they are free or new slots, which no reader sees, so the database holds
  their whole half), `commitFreelist`, `writeMeta` (the meta slot `txid % 2`, no reader's),
  and `Commit`'s accounting: the new meta's tree is the current one, the freed pages go
  pending, readers keep their pages (MVCC).

**The interface** between them is the callee specs the graph needs from the database:
`Tx.allocate` (a buffer of `count` pages, its id new: free or at the high-water mark), the
freelist's `Free` (`Iface.lean`), `Tx.page` for a writer (a page of `tx.pages`, or of the
current tree through the writer's view). The graph's agent states the specs it needs;
they are proved on the database's side.

**Simplifications** (each an `ownDB` fact, to lift later): the default logger;
`StrictMode` off (`Check` runs goroutines); `NoFreelistSync` off; no `Batch`.
`node.splitTwo` and `rebalance` convert between integers and `float64`, which Perennial does
not model: `FloatConv.lean` adds the conversions as uninterpreted functions, as a typeclass
of step facts taken as a hypothesis (to move into Perennial with its next batch).

## The spill and `Commit` (design, 2026-10-12)

What `Commit` must re-establish is `dbOK` of the state with the new meta current: its tree
`treeStrict` (now with `treeKeys`, `TreeKeys.lean`), its pages disjoint, none free or pending,
the readers' views untouched. Three things the clean invariant does not state are needed:

- **Keys** (`treeKeys`; the transaction's side `bktKeys`, `WriteTxShape.lean`). `node.spill`
  re-keys a child's entry in its parent with `put(n.key, firstKey, ...)`: if the entry's key is
  not `n.key`, `put` inserts a second entry and the first keeps pointing at the freed page (a
  later reuse of that page corrupts the tree). The parent's page stays sorted only if every
  child's keys are within its entry's bounds (a B+tree's invariant, which `Put` keeps because
  the cursor routes a key by the branches' keys). `rebalance` asserts a node's parent has two
  children (branches have two entries) and sorts children by their first key (they are not
  empty); its merges join siblings of one kind.
- **Nested buckets** (`bktNested`): an opened child bucket is its parent's entry (root, and its
  header while it has not changed).
- **Disjointness**, as ghost page tokens (`txShape`): one exclusive token per page id, each with
  one position of the logical tree (a node's own page, an unmaterialized child's subtree, an
  unopened nested bucket's tree, an opened bucket's tree but its own opened children). Spill
  assembles a written subtree from a fresh page (its token from the authority, the id being
  new) and its children's separately held trees, so `viewUnique` holds by separation; freed
  pages' tokens go to a stash, so the new tree shares no page with the pending ones.

**Layers.** `txShape γ W T` is a second conjunct next to `ownWriteTx` (the existing proofs of
`ownWriteTx` stay as they are); each write operation's spec gains it: materialization
(`Bucket.node`, `Cursor.node`) splits a position's tokens, `openBucket` moves an entry's tree
to the child, `Put`/`Delete` keep the keys (the cursor's search gives the routing facts),
`CreateBucket` adds an inline entry (no pages). Then: `rebalance` (keeps `txShape`, frees
merged pages), the spill (`node.spill`, `Bucket.spill`: from `txShape` to a written tree,
`wtree`), and `Commit`'s database side (`commitFreelist`, `grow`, `Tx.write`: dirty slots, no
view covers them, written through `db.ops.writeAt`, which `ownDB` now states is the file's
`WriteAt`; `writeMeta`; `dbOK` of the committed state).

**Safety finding** (to state as a precondition): if `writeMeta`'s write reaches the file (a
short write after the meta's 80 bytes, then an error, or `fdatasync` failing after it), `Commit`
calls `rollback()`, which reloads the freelist from `db.meta()`: the new meta, valid and newer.
`Reload` then makes the pages this transaction freed free (its pending entry was rolled back),
while open readers may still see them; the next writer can overwrite them under a reader.
