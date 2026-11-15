# Batch 4c (bbolt's public API), review round 1: provability and completeness

Reviewer: separate agent, 2026-11-09, at `7acafe721b` ("4c bbolt public API draft"). Targets:
`SpecPlan/Spec/go_etcd_io/bbolt/{Model,Api,Internal}.lean` and the 51 specs, `examples/specreq/bbolt/`, the
`## from 4c` sections of `notes/specs-only/req/`. Go: `.lake/src/bbolt` (upamanyus/bbolt@743299d8),
`.lake/src/server/storage/backend` (etcd `a4d2bb17`), `GooseLang/Ext/OsFs/Impl.lean`,
`TrustedCode/os.lean`. Old work: `specs-ref` (`bbolt-api.md`, `Proof/go_etcd_io/bbolt/Link.lean`).

## What is good

* **The durability design holds together.** Client-owned `BoltSt` with `dur`/`busy`/`lost`, a
  commit update with two outcomes plus a settling update, a sync update, and the crash law as the
  bridge between generations. It answers the old spec's open question (what a crash leaves)
  without a bbolt-owned witness, which a later `NoSync` commit could not invalidate (4c-D3 is
  right). `busy` is needed and is enough against a concurrent `DB.Sync`: OsFs's `Fsync` is one step
  (`Impl.lean:414-417`) that excludes in-flight bytes, so the sync update fires at that step.
* **Generations per path** (`TxView.gens` over every prefix) make a deleted ancestor stale all of
  its descendants' handles in one stroke (`nonissues/bbolt-deleted-bucket-handle.md`). I checked
  the cursor positions against both nonissues (`bbolt-cursor-prev-after-next-end`: `Seek` past the
  end then `Prev` returns the last key, `Last`/`Next`/`Prev` returns the one before it), and the
  specs state them exactly.
* **The relaxations are real**: mutations on read transactions return `ErrTxNotWritable`
  (`bucket.go`'s order checked for `Put`, `NextSequence`, `Delete`, `Commit`, `CreateBucket*`);
  nested buckets; `nil` options; a second `Close` (`db.close()` returns nil once `!opened`,
  `db.go:781-784`); `DeleteBucket("")` on an empty bucket stated exactly.
* **The model is readable and transparent.** `Data`/`Ent`, `modAt`, `curEnts`, `seekIdx`. The
  error identities (`isErr`, `errIs_init`, `errIs_distinct`) answer 4d's request cleanly.
* `Tx.WriteTo` is stated over `T.base` (the right thing for a write transaction, whose changes
  stay in nodes until `Commit`, `tx.go:399-474`) and keeps D21's meta parity.
* The commit path's internal specs (`wtxAt` stages) are a sound pattern for the rest of the
  internals (finding C8).

## Answers to the brief's provability questions

**(a) `boltCrash` under OsFs's crash model.** Confirmed false today, and for a broader reason
than 4c-D1 gives. `CrashImage` (`Impl.lean:462-468`) leaves every dirty, lost or in-flight byte
**arbitrary**. A crash during or after the meta write can therefore leave the slot holding *any*
80 bytes, including a meta with a **correctly computed** checksum that describes a state that
never existed (a high txid, a root at a page of user bytes). No FNV collision is needed. The gap is
in the crash relation, not in the hash, and the user's decision text should say so ("Explain a
finding in plain terms", D22's lesson).

D22's rule does **not** suffice. It constrains `PWriteFinish` (the page cache, in-process,
`Impl.lean:381-387`), not `CrashImage`.

The proposed sector rule would make `boltCrash` true for bbolt's meta write. The meta is
`Page` (16 bytes) plus `Meta` (64 bytes) at offset 0 of its page (`internal/common/page.go:31-36`,
`meta.go:12-22`), so all 80 bytes lie in the first 512-byte sector. `writeMeta` writes the whole
aligned page in one `pwrite` (`tx.go:607-613`). But **the rule as worded in 4c-D1 is false in
general**: "each aligned 512-byte sector holds its durable bytes or a version the page cache held
since the last sync". Linux does not wait for writeback before copying into a page unless the
device needs stable pages (`folio_wait_stable` only for `stable_writes` mappings). So a `pwrite`
into a page that is already dirty and under writeback can be DMA'd half-copied: the sector reaches
the disk mixed, a version the cache never held. That breaks the hard rule "never a universal that
is false somewhere", and the case is reachable. Under `NoSync` the meta slot is rewritten every
second commit while it may still be under writeback.

What bbolt actually relies on is narrower and true. In sync mode the meta page is **clean and not
under writeback** when its `pwrite` begins: it was last written two commits ago and synced then,
and `tx.write`'s `fdatasync` just ran and waited for writeback. A copy into such a page completes
before the page is dirtied, so any later writeback sees one whole version. A candidate rule:

> if, since the file's last successful sync, a sector has been changed by at most one `pwrite`
> (finished or in flight), it holds after a crash either its durable bytes or the bytes that write
> gave it.

It must also cover in-flight writes (`InflightAt`, the `attempt` window) and lost bytes (taking
the last *successful* sync). Large folios do not break this, because in sync mode nothing in the
file is dirty when the meta write starts. These claims come from memory of `mm/filemap.c` and
`folio_wait_stable`, as `Impl.lean`'s own D22 note does, and are uncertain to that degree. Option
(b) (a visible crash premise, `CrashP1`) avoids the kernel argument but puts a premise in every
statement.

**(b) The two commit updates, the flags, the three transitions.** The commit/attempt/settle/sync
split is sound in shape, and `busy` is necessary and sufficient against a concurrent `DB.Sync`.
**`lost` is not conservative enough** (finding P1): a commit after a failed sync can make the
recoverable set claim states whose pages are gone. The model also needs the sketches to record a
failed `grow` sync (S2). Minimality: three updates plus `busy` and `lost` is the least I can find.
Folding the data change into the settle update fails because readers that begin between
`metalock`'s release and the settle see the new meta.

**(c) The prophecy on `writeMeta` (4c-D2).** It is necessary for a two-update design. Without it,
the design needs three updates: an attempt at `PWriteStart`, a commit-or-not at `PWriteFinish`
(still under `metalock`), and the settle. But **the resolution 4c-D2 proposes, `ResolveBool(err ==
nil)`, is wrong** (finding P2): in the model the page can be written while `WriteAt` returns an
error.

**(d)** Read transactions concurrent with a writer are fine: a remap waits on `mmaplock`, and a
self-deadlock is no counterexample to a Hoare triple. The freelist readers (`AddReadonlyTXID`
under `metalock`, `db.go:895-896`; release at `beginRWTx`, `:944`) and `freepages`' spare slot
match the sketches. Nested buckets and cursor repositioning are fine. `ErrTxNotWritable` is fine
except `Commit` (C6). `Close` twice is fine.

**(e)** Snippets: see C1, C2, C4, C6, C7 and S5. `ReqNested`, `ReqCursorDelete`,
`ReqDeleteBucketNotFound` and `ReqCrashAtomicDurable` are provable, given the boltState note in
S5 and P1's fix, which they survive because the bank stops at the first error.

## First tier

### P1. A commit after a failed sync makes `boltCrash` false (Model.lean `BoltSt.commit`/`sync`/`settle`)

**Principle.** Sound: true of the code.

**Evidence.** OsFs's D2 (`Impl.lean`, `OsFile.lost`): a failed `fdatasync` marks the dirty pages
clean, and no later sync writes them unless they are rewritten. Two runs:

1. **A concurrent `DB.Sync` fails.** It fails while commit N+1's data pages are dirty (between
   `tx.write`'s `pwrite`s and its `fdatasync`, `tx.go:551-574`). `σ.sync false` sets `lost`.
   `tx.write`'s own `fdatasync` then succeeds (the error was reported once), the meta is written
   and synced, and `Commit` returns **nil**. The disk's newest valid meta is N+1, and it points at
   pages whose writeback was lost. The model says `σ.recovers` is `D_{N+1}` or `D_N` (because
   `lost` blocks the reset, `dur = ds ++ [D_N]`), yet a crash recovers a tree of stale pages.
2. **The meta's own `fdatasync` fails.** It fails at `tx.go:621`; settle sets `failed`/`lost` and
   leaves `dur = ds ++ [D_N]`. The fork's `rollback` keeps the commit (`tx.go:332-334`). The next
   writer's `ReleasePendingPages` (`db.go:944`) frees `D_N`'s replaced pages and reuses them, while
   the disk's slot `(N+1)%2` may still hold meta N-1 (writeback lost), so the newest valid meta on
   disk is N. A crash after N+2's data sync and before its meta reaches the disk recovers meta N
   over overwritten pages, while `dur` claims `D_N`.

**Caller affected.** Every crash-safe client (the bank, 4a's crash clause). etcd itself exits on
any commit error (`batch_tx.go:302`) and syncs only the defrag `tmpdb`, fatally on error
(`backend.go:578-581`).

**Restatement.** Once `σ.lost`, a later commit promises nothing: in `BoltSt.commit` and
`BoltSt.attempt`, `dur := if noSync || σ.lost then none else …`. `sync` and `settle` stay as
they are. The bank snippet survives, because it stops at the first error and makes no further
commit in that generation.

**Go.** This is a bbolt durability bug when a client keeps using the `DB` after a failed sync. Run
1 is the sharper case: `Commit` returns nil and a crash then corrupts the file. Not in `issues/`
or `nonissues/`; `bbolt-commit-meta-error-frees-reader-pages` is about readers, not crashes. It
belongs in `nonissues/` (etcd meets the precondition by exiting; a Go test needs fdatasync fault
injection plus a crash), `blocks-proof: no`. The author should file it; this review does not edit
the repository.

### P2. 4c-D1's sector rule is false as worded; 4c-D2's prophecy resolves the wrong fact

**Principle.** An assumption states the physical fact, never a universal false somewhere; explain
a finding in plain terms (bbolt-api.md D22).

**Evidence (D1).** See (a) above: a write into a page under writeback can reach the disk mixed.

**Evidence (D2).** `PWriteFinish` (`Impl.lean:386-387`) allows "all of it or none, **whatever the
errno**" within one aligned page, so `k = len` with `e ≠ 0` is a model step. `File.WriteAt.impl`
(`TrustedCode/os.lean:309-318`) then returns `(0, err)`. On `EINTR` it also retries from `nn`
without adding `k`, so a first attempt can write the page and a retry can then fail. Either way
the meta is current (`rollback` sees `db.meta().Txid() == tx.meta.Txid()`, `tx.go:332`), yet
`err ≠ nil`. A prophecy on `err == nil` would fire `attempt` (data unchanged) while every later
reader sees the new data, which breaks `DB.Begin.spec`'s read update.

`Tx.writeMeta.spec`'s post survives only because the prover can set `failed := true` in that case
(sound but lossy: it sets `lost`). Its docstring ("`synced` ... `failed`: an fdatasync failed") and
`Tx.Commit.spec`'s sketch say otherwise.

**Restatement.** For D1, give the narrow rule from (a), with its kernel argument, and present it to
the user as "the crash relation lets the slot be any bytes; a disk writes a sector whole, and the
meta's page is idle when bbolt writes it". For D2, resolve on "the page was written", read before
`metalock.Unlock` (for example the mapped meta page's txid). Check that `etc/prophcheck` admits the
expression; I could not verify which expressions it allows. In `writeMeta`'s docstring, let
`failed` also cover "the write reported an error after the page was written".

### C1. `Bucket.Put` takes `value ↦*□ vb`: defrag's copy cannot meet it, and `ReqDefrag` is unprovable

**Principle.** Complete: sufficient for every caller.

**Evidence.** Defrag puts bytes it got from another transaction: `b.ForEach(func(k, v) { …
tmpb.Put(k, v) })` at `backend.go:849, 930, 1012, 1026`. `v` is a `txBytes` of `odb`'s read
transaction, valid only while it lives: `txBytes_acc` lends `∃ dq, s ↦*{dq} b` and takes it back
to restore `boltTx`. A persistent points-to of mapped memory cannot be had: a later remap removes
the cells (`HeapRendered`). Go's contract is "the value must remain valid for the life of the
transaction" (bbolt's doc on `Put`). That is a borrow until the writer ends, not forever.

`ReqDefrag` (`examples/specreq/bbolt/backend.go`, `_ = b.ForEach(func(k, v) { return tmpb.Put(k, v)
})`) is unprovable. It also calls `tx.Rollback()` before `tmptx.Commit()`, the reverse of etcd's
deferred order (`backend.go:816, 855`): with a by-reference value that order is exactly the unsafe
one.

**Restatement.** `Put` takes `value ↦*{dv} vb` and returns a one-shot receipt for it, redeemable
once the writer is done, for example `(txDone tx ={E}=∗ value ↦*{dv} vb)` backed by an exclusive
token, so that the borrowed fraction comes back by `Commit`/`Rollback`. Fix the snippet's order to
etcd's.

### C2. No well-formedness law: key order cannot be proved, which breaks the backend's range and the snippets' order guards

**Principle.** Laws for what clients would otherwise unfold; complete.

**Evidence.** The model's header says data "reached from `Data.empty` or from a file is sorted",
but no statement gives it: `grep sorted SpecPlan/Spec/go_etcd_io/bbolt` finds only comments. A client
cannot derive it either. `fileHolds_image`'s `D` comes with an opaque `boltImage`, and the client
is not supposed to prove model lemmas. 4a's range (`batch_tx.go:206-228`'s `unsafeRange`, which
stops at the first key ≥ `endKey`) needs `T.ents` sorted: 4a's `Api.lean` uses `sortedEnts`. The
guards "range out of order" (`ReqBackendBatch`) and "ForEach out of order" (`ReqHash`) are
unprovable.

**Restatement.** Add a transparent `Ent.wf` (entries strictly sorted by `go.GoStringLt`,
recursively), a law `boltTx_wf : boltTx tx γ q T ⊢ ⌜T.cur.wf ∧ T.base.wf⌝`, and `wf` in
`fileHolds_image`'s premise or in `boltImage`'s meaning.

### C3. Opaque contracts with no way in: `boltLogger`, `openFileOk`, `writerPlain`, `optsAt`. etcd cannot call `Open` or `WriteTo`

**Principle.** Every premise has a source the caller sees (README); complete.

**Evidence.**
* `boltLogger` is opaque, with only `boltLogger_nil`. `newBackend` passes a `*zapBoltLogger`
  (`backend.go:229`), so 4a cannot establish `Open`'s pre. 4a's request item 2
  (`req/go_etcd_io_bbolt.md`) asks exactly this. The old D20/D20′ made it a method contract for
  this reason; opaque is a regression.
* `openFileOk` is opaque with no introduction. The docstring says "the caller proves it from the
  file it already opened", but nothing lets it (`backend.go:522-526`; `ReqDefrag`).
* `writerPlain` is an opaque `Prop` with no introduction, so no client can produce `writerOk`
  (`Tx.WriteTo`; etcd's `*io.PipeWriter`, `maintenance.go:147-152`; `ReqSnapshot`).
* `optsAt` has no law to create or change it. `Options` is axiomatized (`Code/go_etcd_io/
  bbolt.toml:11`), yet the backend allocates it and writes its fields (`backend.go:216-230`,
  `521-531`, and the `boltOpenOptions` global, `config_linux.go:29`). The old tree had
  `wp_optsLit`/`wp_optsAlloc`/`wp_optsLoad`/`wp_optsStore` and per-field laws
  (`specs-ref/Proof/go_etcd_io/bbolt/Options.lean:46-73`). None survive. `ReqBackendOpen` and
  `ReqDefrag` (which build `&bolt.Options{...}` and set fields) are unprovable.

**Restatement.**
* `boltLogger l` transparent: the method contract over the four methods, as D20′.
* `openFileOk f path` transparent: `□ ∀ …, WP f(path, flag, mode) {{ an os.File fd of path's OsFs
  file ∨ error }}`, in terms of the `os` specs Open's sketch uses.
* `writerPlain` defined from the method set (`methods wi.ty go!"ReadFrom"` absent), or a law per
  type the clients use.
* `optsAt`'s construction, load, store and per-field laws restated as `.spec` obligations
  (trust-boundary specs: their block comment says why they are true of an axiomatized type). A
  store to a field `OptsM` does not track (`InitialMmapSize`, `Timeout`, `FreelistType`,
  `NoFreelistSync`, `NoGrowSync`) leaves `o` unchanged.

### C4. `Tx.Size` is not tied to `WriteTo`'s image, so the snapshot's length cannot be proved

**Principle.** Complete; snippet provable.

**Evidence.** `Tx.Size.spec` returns some `n < 2^48`, and `Tx.WriteTo.spec` writes `img` with
`boltImage img T.base`. No statement says `|img| = Size`. The maintenance service streams exactly
`snap.Size()` bytes and reports `RemainingBytes` from it (`maintenance.go:164-198`; an image
shorter than `Size` would loop forever on `ReadFull`'s EOF). `snapshot_merge.go:53` puts
`dbsnap.Size()` in the raft snapshot message. 4a's request item 7 asks for it ("`Size()` is their
length"). `ReqSnapshot`'s "short image" guard is unprovable.

**Restatement.** Give both specs a common term. For example, `Begin` (or a law) gives a persistent
`txImgLen tx n`; `Size` returns `n`; `WriteTo`'s post adds `img.length = uint.nat n`.

### C5. `Rollback` on a finished transaction, and `Begin(true)` failing after a successful commit (defrag)

**Principle.** Complete: every caller's pre and post.

**Evidence.**
* `defragdb`'s deferred `tmptx.Rollback()` (`backend.go:807`) runs after `tmptx.Commit()` failed
  (`:836-838`) or after the final `Commit` failed (`:855`). The same holds at `:875` and `:975`.
  Go returns `ErrTxClosed` (`tx.go:304-307`; `close` sets `tx.db = nil`). `Tx.Rollback.spec`
  takes a live `boltTx` only.
* If the reopen `tmpdb.Begin(true)` (`:840`, `:1004`) fails, `tmptx` is nil and that deferred
  `Rollback` dereferences nil (`common.Assert(!tx.managed)`): a panic. Unlike
  `defragdbAndTrackLastKeys` (`:875`), these paths do not guard with `tmptx != nil`. In bbolt,
  `Begin(true)` on an open database fails only after a remap failed inside a failed commit
  (`db.go:929-938`, `ErrInvalidMapping`), and defrag returns on that commit's error first. So the
  panic is unreachable in Go, but `DB.Begin.spec`'s unconditional error disjunct leaves 4a's
  defrag unprovable.

**Restatement.**
* Add to `Tx.Rollback.spec` a `txDone tx` case returning `isErr ErrTxClosed`. `txDone` must then
  own a persistent read of `tx.managed` and `tx.db`.
* Make `Begin`'s error excludable by a caller that holds the close right and has seen no failed
  commit. For example, the error post gives `dbClosed db ∨ boltBroken db`, a failed `Commit` is
  the only producer of `boltBroken`, and a law excludes `boltBroken db` against an exclusive
  "healthy" token that `Open` hands to the database's sole writer. Also add
  `boltOpened db γ ∗ dbClosed db ⊢ False`.

### C6. `Commit` on a read transaction requires the two commit updates; `ReqReadOnlyPut` is unprovable

**Principle.** No unneeded premise; snippet provable.

**Evidence.** `Tx.Commit.spec` asks for both AUs over `boltState γ 1 σ` whatever `T.rw` is. A read
transaction's `Commit` returns `ErrTxNotWritable` without touching them (`tx.go:188-189`). A
read-only client holds no `boltState γ 1` and cannot build an AU over it. `ReqReadOnlyPut`'s
Assumes ("db open; the bucket exists; the thread token") does not give one.

**Restatement.** Make the pre's AUs `if T.rw then (AU ∗ AU) else emp`, and drop them from the
read branch of the post.

### C7. `ReqBackendBatch`'s "range does not start at the next key" guard is false

**Evidence.** After `Put k1`, `Put k2`, `Delete k1`, `Seek(k1)` returns the first existing key ≥
`k1`. Any key already in `keyBucket` between `k1` and `k2` comes first. Assumes says only `k1 <
k2`.

**Restatement.** Assume "no key of `keyBucket` lies strictly between `k1` and `k2`", or check that
`k2` is in `keys`. The Assumes should also say the caller holds `boltState γ 1 σ` (the backend's
batch lock) to build `Commit`'s updates.

### C8. About 94 previously proved package-`bbolt` functions have no spec, and the batch's list of them is incomplete

**Principle.** A smaller API is not a narrower scope (PRINCIPLES, Scope).

**Evidence.** The old `specs-ref/Proof/go_etcd_io/bbolt/Link.lean` links proofs of these
functions (package `bbolt` only; `internal/*` is 4d's), none of which has a spec here:

* `Bucket.{node, openBucket, pageNode, write, free, dereference, inlineable, maxInlineBucketSize}`
* `Cursor.{first, last, next, prev, seek, search, nsearch, keyValue, node,
  goToFirstElementOnTheStack}`
* `DB.{Logger, allocate, beginTx, beginRWTx, close, fileSize, freepages, getPageSize,
  getPageSizeFromFirstMeta, getPageSizeFromSecondMeta, grow, growSize, hasSyncedFreelist, init,
  loadFreelist, meta, metasZero, mmap, mmapSize, mmapUnlocked, munmap, page, pageInBuffer}`
* `Tx.{allocate, close, forEachPage, page, rollback, checkInvariantProperties,
  recursivelyCheckBucket, recursivelyCheckPageKeyOrder, recursivelyCheckPageKeyOrderInternal}`
* `TxStats.{GetRebalance, IncCursorCount, IncNodeCount, IncNodeDeref, IncPageAlloc, IncPageCount,
  IncRebalance, IncRebalanceTime, IncSpill, IncSpillTime, IncSplit, IncWrite, IncWriteTime}`
* `node.{childAt, childIndex, del, dereference, free, nextSibling, numChildren, pageElementSize,
  prevSibling, put, read, rebalance, removeChild, root, size, sizeLessThan, split, splitIndex,
  splitTwo, write, spill}`
* package functions `fdatasync`, `flock`, `mmap`, `munmap`, `newFreelist`, `splitThreshold`
  (trusted, D17), `compareKeys`, `verifyKeyOrder`, `verifyPageReachable`, and `Options.String`

The batch's "Left out" list omits about 35 of these:

* `node.{rebalance, split, splitIndex, splitTwo, sizeLessThan, pageElementSize, dereference,
  spill}`
* `Bucket.{inlineable, maxInlineBucketSize}`
* every `DB.mmap*`, `DB.munmap`, `DB.getPageSize*`, `DB.init`, `DB.loadFreelist`, `DB.allocate`,
  `DB.beginRWTx`, `DB.close`, `DB.fileSize`, `DB.growSize`, `DB.Logger`
* `Tx.rollback` and the four check helpers
* `flock`, `mmap`, `munmap`, `splitThreshold`, `compareKeys`, `verifyKeyOrder`,
  `verifyPageReachable`

`Commit`'s and `Open`'s sketches already lean on several of them (`Tx.rollback`, `DB.init`,
`getPageSize`, `freepages`' check goroutine).

**Restatement.** Restate them as 4c-Q5 recommends, mirroring the code over `wtxAt`-style internal
vocabulary (the scope note allows that). Until then, list all of them under 4c-Q5 so that the user
decides on the true count.

### C9. 4a's request (`req/go_etcd_io_bbolt.md`, "from 4a") was not answered

**Evidence.** The batch report says "no `req/go_etcd_io_bbolt.md` yet at this writing". The file
exists at HEAD (committed in `8371ab0480`, before this batch).

* Unanswered: item 1 (name `Open`'s success condition, or say there is none), item 2 (the logger
  contract, C3), item 7 (`Size` = image length, C4).
* Item 3: 4a counts its readers as `beRdToks` up to `2^30 - 2`, while `Begin` takes a `threadTok`
  under `ThreadBoundLe 2^29` (D3). The two need reconciling.
* Item 8: 4a expects `Close` to give back `fileHolds`. 4c gives `boltClosed γ` with the state
  living on; that answer suits 4a's round trip better, but it must be said.

**Restatement.** Add "## from 4c (answer)" covering each item. For item 1, in OsFs every system
call may fail with an errno, so no file premise makes `Open` succeed: `dbOpenOk` stays an
environment premise, as with the closed-theorem convention for environment failures.

## Second tier

* **S1. `DB.Update.spec`'s error post ends in `∨ True`** (`DB__Update.lean`): a disjunct that
  always holds. Its purpose is `Begin`'s error, where `fn` is not called, but the client then
  loses everything it lent `fn`'s contract, its AUs' resources included. Return the unused
  contract instead (`∨ ⌜begin failed⌝ ∗ (∀ tx D Φ, … WP fn …)`), as `DB.View` returns its update.
  (examples/put.md: no vacuous disjunct.)
* **S2. `Commit`'s sketch fires neither update when `grow`'s sync fails.** `grow`'s
  `file.Sync()` (`db.go:1321`) runs under `NoSync` whenever `NoGrowSync` is off. That is etcd's
  defrag database: `bopts.NoGrowSync = UnsafeNoFsync` (default false, `backend.go:228`), then
  `options.NoSync = true` (`:531`), and also `ReqDefrag`'s options. Its failure loses earlier
  `NoSync` commits' pages. If neither update fires, `lost` stays false, and a later successful
  `DB.Sync` sets `dur := some []` over pages that are gone. The spec's error disjunct already
  admits the right proof: fire both updates, `ok = false` (attempt) and settle with
  `failed = true`. The sketch should say so for every failed `fsync`/`fdatasync` on the error
  paths.
* **S3.** `Tx.write.spec`'s sketch says "a failure only loses these bytes, unreachable". That is
  true in sync mode only, and only for this transaction's pages: a failed `fdatasync` loses every
  dirty page of the file.
* **S4. `Open`'s error post says nothing of the custom `OpenFile`'s file.** etcd closes `temp`
  again after a failed `Open` (`backend.go:536`), when bbolt's error path has already closed it
  (`db.close()`). The caller needs the file's state back (closed, or its fd resource).
* **S5. Snippet coverage.**
  * `ReqBackendRead` claims "read concurrently through per-goroutine cursors" but uses one
    goroutine. etcd's shared read transaction is read by many goroutines, each with its own cursor
    from a cached shared `*Bucket` (`read_tx.go:95-118`): one snippet should split `boltTx` across
    goroutines.
  * `ReqBackendRead`, `ReqNested` and `ReqBackendBatch` should say in Assumes that the caller (or
    its invariant) holds `boltState` for the commit updates.
  * `ReqDefrag`'s `path == ""` guard needs `γ.path ≠ ""` assumed.
* **S6. `boltCrash` and `fileHolds_alloc`.** Fine, but `boltCrash` is stated for any fraction `q`.
  Its sketch should say why the file invariant's half agrees with that fraction at the crash step
  (`boltState_frac`'s agreement), since `crashed` is taken after the old generation's
  invariants stop.
* **S7. Locality.** `Commit`'s AU texts are repeated four times in its post. A local `abbrev`
  for "the commit updates of `T`" would make the statement and its clients shorter, without new
  vocabulary.

## Targets ranked by need of revision

1. **`Model.lean` (`BoltSt.commit`/`attempt`) and `Api.lean`**: P1; C2's `wf` law; C3's
   contracts and the `Options` laws; C4's size term; `boltCrash` restated with the corrected
   4c-D1 rule (P2).
2. **`Bucket__Put.lean`** (C1).
3. **`Tx__Commit.lean`, `Tx__writeMeta.lean`, `DB__Update.lean`** (P2's resolution, C6, S1, S2).
4. **`Tx__Rollback.lean`, `DB__Begin.lean`** (C5).
5. **`Tx__Size.lean`, `Tx__WriteTo.lean`** (C4, C3's `writerPlain`).
6. **`examples/specreq/bbolt/backend.go`** (C7, `ReqDefrag`'s order, S5), then **`nested.go`**'s
   Assumes.
7. **The missing internals** (C8), and the report's answer to 4a (C9).
8. The rest (`Cursor__*`, `Bucket__{Get,Bucket,Delete,DeleteBucket,ForEach,…}`, `Tx__{Bucket,
   CreateBucket*,DeleteBucket,ForEach,Cursor,Stats,ID,DB,Writable}`, `DB__{Close,Path,Stats,
   Info,Sync,View}`, `Open.lean`'s statement): sound as far as I checked; no change needed beyond
   the vocabulary fixes above.

## Verdict

Not done: nine first-tier findings. Two are soundness problems in the durability core: P1, a
commit after a failed sync, and P2, the sector rule's wording and the prophecy's resolution. The
rest are completeness gaps that leave etcd's backend unable to call `Open`, `WriteTo` and the
defrag copy, and leave the backend's range order unprovable (C1-C6, C9), plus a false snippet guard
(C7) and the dropped internals (C8). The design itself (client-owned `BoltSt`, the commit, settle
and sync updates, per-path generations) is sound in shape and worth keeping. A second round is
needed after the repairs.
