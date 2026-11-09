# Repair: group `bbolt` (2026-11-09)

Reports: `A11-bbolt-provability.md` (F1-F10), `A11-bbolt-completeness.md` (F1-F5, S1-S4); the
backend group's "Requests to bbolt" in `repair-backend-schema.md` (1-4, all handled below).
Files: `Spec/go_etcd_io/bbolt/{Model,Api,Internal,Options,Open,Tx__Commit,DB__Update,DB__Stats,
Cursor__node,Bucket__node,node__rebalance,node__spill,node__free,Bucket__free,Tx__allocate,
DB__allocate}.lean`, sketches in `Bucket__{Put,Delete,CreateBucket,CreateBucketIfNotExists,
DeleteBucket,SetSequence,NextSequence,rebalance,spill}.lean`, `Cursor__Delete.lean`,
`Tx__commitFreelist.lean`; snippets `examples/specreq/bbolt/{backend,bank,nested}.go`,
`examples/specreq/bboltinternal/freelist.go`; `nonissues/bbolt-create-dir-not-synced.md` (new).
4d (`internal/common`, `internal/freelist`) passed both reviews and is unchanged.

## Provability findings

- **F1 (crash law false for a file created this generation): fixed, a user decision (below).**
  `BoltSt` gains `named : Bool` (the file's name is durable); `BoltSt.init D` has `named = true`,
  the new `BoltSt.fresh` (empty) `named = false`; `BoltSt.recovers` also admits `Data.empty` while
  `named = false`. `fileHolds` now means an existing file whose name is durable: `fileHolds_new`
  takes only an empty file with `named = true` (option iii for `fileHolds`), and a new law
  **`boltFresh_alloc`** starts a generation from no file, or from an empty file whose name may not
  be durable, with `BoltSt.fresh` (etcd's first boot and defrag's `os.CreateTemp` stay provable).
  `boltCrash`'s conclusion: `fileHolds γ.path D`, or (`σ.named = false`, `D = Data.empty`) no file
  (`osMeta … none` in the next generation, from which `boltFresh_alloc` starts again). Nonissue
  filed: `nonissues/bbolt-create-dir-not-synced.md` (`blocks-proof: no`). `ReqCrashAtomicDurable`'s
  Assumes now say the file was created empty and its directory synced before the first boot.
- **F2 (`init`'s first write past the durable size): fixed in the text of 4c-D1** (still open):
  `Api.lean`'s header states the sector rule's second clause (a sector past the durable size
  written by one `pwrite` since the last sync holds zeros or that write's bytes; ext4
  `data=ordered`/xfs, excluding `data=writeback`), and why `init`'s crash case then closes.
- **F3 (`fileHolds_new` lacks `m.hi = 0`): fixed**: `m.hi = 0` (and `named`, F1) in
  `fileHolds_new`; `m.hi = 0` in `boltFresh_alloc`'s empty-file case.
- **F4 (`openFileOk` persistent): fixed**: one-shot (no `□`), with a caller-chosen `R` the closure
  can return to from its file's handle (or keeps on its own error); `Open.spec` takes it only for a
  non-nil option and gives `R` back on its error (bbolt's `db.close()` has closed the file; etcd
  closes it again and removes it). Completeness F2 (second part) is this too.
- **F5 (commit and settle laws from one state): fixed differently.** Instead of one law realized
  with an invariant, the two updates are **nested** (`commitAU` in `Api.lean`): the commit update's
  commit gives the settling update. bbolt fires the commit update first on every path, so this is
  true of the code, and a holder of the whole state builds both from its one copy
  (`boltState_commit_au`, restated: ends with `((σ.commit|attempt) D ns).settle …`); invariant
  holders build them from the invariant as before. `Tx.Commit.spec`, `DB.Update.spec` take
  `commitAU … S` with one client predicate `S ok synced failed brk` (was `Q ok` and `S`).
  `boltState_settle_au` kept as the generic update (a sync's). Why differently: no invariant, no
  ghost agreement between `Q` and `S`, and the client learns `ok` in `S`.
- **F6 (no size bounds on stored data): fixed**: `Ent.wf` now also bounds every key by
  `maxKeySize` and every plain value's key plus value by `bboltEntryMax`, recursively; so
  `boltTx_wf`/`boltImage_wf` give them (the size bounds moved above `Ent.wf` in `Model.lean`).
  Completeness F1 and backend request 2 are this.
- **F7 (no keyed-literal spec for `Options`): fixed differently**: no translated code has a keyed
  `bolt.Options` literal (the backend's is `&bolt.Options{}` then field stores; etcd's only keyed one,
  `boltOpenOptions`, is an untranslated package initializer, `boltOpenOptions.init`, so its value is
  the backend's assumed fact). The snippets now build options from `{}` and field stores;
  `Options.lean`'s header says why there is no keyed spec. (Request to backend-schema below.)
- **F8 (`optsAt_*` wands joined by `∗`): fixed**: the two ways back are joined by `∧` in all five
  field laws.
- **F9 (the internal layer does not carry the abstraction): fixed.** `Internal.lean`:
  - `TxCore` gains `bufs` (allocated pages' buffers), `bkts` (cached handles' paths), `snap` (the
    snapshot's pages) and the view's non-physical parts `managed`, `noSync`, `base`, `gen`. **A
    further bug found here**: without them `physRep T C` could not distinguish views differing only
    in `managed`/`noSync`/`gen`, so `wtxCore_view` would have identified a managed transaction with
    an unmanaged one (whose `Commit` panics on one but not the other): `wtxCore_view` was not
    realizable. `physRep_meta` pins them.
  - New vocabulary: `keyLeaf C p k n` (opaque: the cached leaf of `p`'s tree where `k` belongs;
    stable under `node.put`/`del`), `repKept C C'`, `curKey`, `bktDropped`, `newEnt`/`emptyBktVal`,
    `freshPage`, `TxCore.setNode`/`gens`.
  - Laws: `physRep_meta`, `physRep_set` (Put, CreateBucket*), `physRep_del` (Delete,
    Cursor.Delete), `physRep_delBkt` (DeleteBucket), `wtxCore_buf` (a page buffer lent and back),
    `wtxCore_seq` (Set/NextSequence through the handle's `InBucket`).
  - Posts: `Cursor.node` (`repKept`, `keyLeaf` of the cursor's key), `Bucket.node` (`repKept`, root
    materialized for a nil parent), `node.rebalance`, `node.spill`, `node.free`, `Bucket.free`
    (`repKept`; `Bucket.free` now needs `C.bkts b = none`, which `DeleteBucket` has: on a cached
    handle `SetRootPage(0)` would make it read as inline), `Tx.allocate` (the run's buffer in
    `C'.bufs`, `freshPage`), `DB.allocate` (the buffer's points-to, `freshPage`).
  - **A second further bug**: `DeleteBucket`'s post `T.dropBkt p kb` bumped only `p.child kb`'s
    generation, but its recursion (each nested bucket's own `DeleteBucket`) bumps the nested paths
    too, so the post's exact view was unreachable. `TxView.dropBkt` now resets the generations
    strictly below `p.child kb` to `0`; sound because a handle below has `p.child kb`'s generation in
    its list, which only grows until an ancestor's is bumped (argument in the docstring).
  - `DeleteBucket`'s three in-body cache writes (`delete(b.buckets, …)`, `child.nodes = nil`,
    `child.rootNode = nil`) are a realization step of bbolt's own proof (stated in its sketch and in
    `physRep_delBkt`'s docstring); every call boundary now gives its caller's next step.
  - Sketches added (each with a verify-round line) to `Bucket.{Put,Delete,CreateBucket,
    CreateBucketIfNotExists,DeleteBucket,SetSequence,NextSequence,rebalance,spill}`,
    `Cursor.Delete`, `Tx.commitFreelist`.
- **F10 (`boltCrash`'s text differs under (a) and (b)): fixed in the text**: the header and the
  law's docstring say the statement written is option (a)'s (over `crashRest`, whose `CrashRel`
  then carries the writes since the last sync) and under (b) it is over `crashRestQ`; the
  conclusion is the same under both.
- Minor (provability snippets): `ReqBackendRead` Assumes adds `k`'s bounds; `ReqNested` adds "no
  other writer" and "the root holds only buckets"; `ReqWriteReload` bounds `pageSize ≤ 2^16`.

## Completeness findings

- **F1** (size law): = provability F6, fixed.
- **F2** (`openFileOk` one-shot, `Open`'s error returns the file): = provability F4, fixed;
  `ReqDefrag` now covers the error path (close again, remove).
- **F3 (no law releases a closed file): fixed**: **`boltRelease`** (`boltFile γ ∗ boltClosed γ ∗
  boltState γ 1 σ ⊢ |={E}=> …`): the file's OsFs resources at whole fractions (no file only if
  `σ.data` is empty), its name durable if `σ.named`, and, when `σ.dur = some []`, `σ.busy = false`
  and the data is non-empty, all bytes clean, `lo = hi = size`, and `boltImage` of the data
  (`fileHolds_image`'s premise but for the name). `ReqDefrag` extended: `os.CreateTemp`, custom
  `OpenFile`, copy, close the source, `Sync`, `Close`, `os.Rename(tmp, path)`, reopen at `path` and
  check the copy is there; the cleanup path (`Close` twice, `RemoveAll`). OsFs's `rename` is still
  missing (batch-4c I7 item 6), named in the snippet's Specs.
- **F4 (`Stats` after `Begin(true)`): fixed**: `statSlot (some (tx, T))` is any transaction's
  whole `boltTx`; law **`statSlot_wtx`** (`T.rw = true → boltTx tx γ 1 T ⊣⊢ statSlot γ (some (tx,
  T))`), realized by a spare `statlock` reader slot in `isBolt` for the writer. `DB.Stats`'s sketch
  and `ReqBackendBatch` (`db.Stats()` after `Begin(true)`) updated.
- **F5** (`beSnap`): the backend's, fixed by backend-schema.
- **S1: fixed**: new snippet `ReqDeleteReturned` (delete the keys the same write transaction's
  range returned, using the returned slices).
- **S2** (non-blocking defrag variant): not added (optional; the specs serve it given F1).
- **S3**: `ReqDefrag`'s Assumes and the copy's panic on a `Put` error now rest on `Ent.wf`'s
  bounds.
- **S4**: filed by backend-schema (`nonissues/etcd-backend-defrag-rollback-nil-tx.md`).

## Backend group's requests

1. `statSlot_wtx`: done (completeness F4), and `ReqBackendBatch` calls `db.Stats()` after
   `Begin(true)`.
2. Size law: done (`Ent.wf`, provability F6).
3. One-shot `openFileOk`, file back on `Open`'s error: done (provability F4; the file comes back as
   the caller's `R`).
4. Release law: done (`boltRelease`; it gives the raw OsFs resources with the image facts, not
   `fileHolds`, because defrag's temporary file's name is not durable until the rename's directory
   sync).

## Requests to backend-schema

1. `Durable.lean`'s header (`beFile_of`: "`fileHolds_new` for a fresh path or a deleted file"): a
   path with no file is no longer a `fileHolds`: a generation starts there by
   **`Bbolt.boltFresh_alloc`** (state `BoltSt.fresh`, `named = false`); `fileHolds_new` takes only an
   empty file whose name is durable. `beCrash` (realized by `boltCrash`): its conclusion now also
   has the case "no file, `σ.named = false`, `D = Data.empty`" (a first boot's database may vanish
   at a crash: etcd recovers it from its WAL); `beFile`'s realization must cover it (`beFile p none`
   or the empty image).
2. Sketches citing bbolt's commit (`batchTxBuffered__Unlock.lean`, `backend__ForceCommit`,
   `backend__Snapshot`, defrag): `Tx.Commit.spec` now takes one nested update `commitAU γ T.base
   T.cur T.noSync S` (with `S ok synced failed brk`), built from the batch lock's whole
   `boltState` by `boltState_commit_au` (no invariant needed).
3. `backend__Defrag.lean`: the laws it names now exist: `Ent.wf`'s bounds (through `boltTx_wf`),
   one-shot `openFileOk f path R` with `Open`'s error giving `R`, `boltRelease` (the raw resources
   with `boltImage` once synced; then OsFs's `rename`, still missing, and `fileHolds_image` after
   the directory sync), `boltFresh_alloc` for the `os.CreateTemp` file.
4. `boltOpenOptions` (`config_linux.go:29-32`): its initializer is untranslated
   (`boltOpenOptions.init`); the value `newBackend` copies (`MmapFlags = MAP_POPULATE`,
   `NoFreelistSync`) is the backend's assumed fact (its `PkgInit` law, `optsAt … o` with
   `o.mmapFlags = mapPopulate`), since bbolt states no keyed-literal spec (A11 F7).

## New decisions (for the user)

**A database file bbolt creates may vanish at a crash (A11 F1).** bbolt opens its path with
`O_CREATE` and never syncs the directory, so on POSIX (and in OsFs, which follows it) the new
file's name is not durable: after a crash the whole file can be gone, with every commit `Update`
acknowledged. On ext4 and xfs this does not happen in practice (the file's sync commits its
creation), and etcd survives it anyway (its WAL rebuilds the database). The options were: (i) make
OsFs say a file's sync makes its name durable (true of ext4/xfs, false of POSIX; a change to the
shared OsFs model); (ii) record it in bbolt's client state (chosen: `BoltSt.named`, false for a
generation that starts from no file, and then `recovers` admits the empty database); (iii) forbid
starting from no file (would make etcd's first boot unprovable). With (ii), a client that wants
durability from the very first commit creates the file and syncs its directory itself
(`fileHolds_new` then requires a durable name), as the bank snippet now assumes. Filed as
`nonissues/bbolt-create-dir-not-synced.md`.

**The sector rule (4c-D1, still open) now has a second clause (A11 F2, F10).** Besides "a
rewritten clean sector holds its old or its new bytes", the rule must say a sector past the file's
durable size holds zeros or the written bytes (ext4 `data=ordered`, xfs; not `data=writeback`), or
`init`'s crash safety fails. Under option (a) (in OsFs's crash relation) `boltCrash` is stated as
written; under (b) (a crash premise) it is restated over `crashRestQ`.

**A commit's two updates are nested (A11 F5).** `Tx.Commit` and `DB.Update` take one atomic update
whose commit yields the settling update, instead of two independent ones. It is what bbolt does
(commit point first, settle after, on every path), lets a client holding the whole state supply
both, and gives the client the commit's outcome with the settled state. Every client changes shape
(one predicate `S` with four flags instead of `Q` and `S`).

**`DeleteBucket` resets the generations below the deleted bucket (A11 F9).** Its exact post was
unreachable through its own recursion; the generations strictly below `p.child k` are now reset to
`0` (`TxView.dropBkt`). Clients see no difference: those handles were stale already and stay stale.

**No keyed `Options` literal spec (A11 F7).** No translated code builds one; the snippets use `{}`
and field stores, and etcd's one keyed literal is an untranslated initializer whose value is the
backend's assumed fact.

## Build

`etc/specs-build.sh --dir Spec/go_etcd_io/bbolt`: **OK (149 modules)**. Importers in another group
rebuilt to check nothing broke: `--dir Spec/go_etcd_io/etcd/server/v3/storage/backend
Spec/go_etcd_io/etcd/server/v3/storage/schema`: OK (174 modules). Snippets: `go vet
./specreq/bbolt/` clean; `gofmt -l` empty for `specreq/bbolt` and `specreq/bboltinternal`.
`etc/issues-status.py --index` regenerated, `--check` clean.
