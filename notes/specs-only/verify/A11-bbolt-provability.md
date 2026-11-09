# A11-bbolt: provability (verification round, 2026-11-09)

Reviewer kind: **provability**, with the `axiom` skill's mindset on the crash law against OsFs
(`GooseLang/Ext/OsFs/`, `Proof/OsFsPrelude.lean`). Area: batches 4c (`Spec/go_etcd_io/bbolt/`:
`Model`, `Api`, `Internal`, `Options`, every `<T>__<M>.lean`; `errors/Api.lean`, added at I7) and
4d (`internal/common/`, `internal/freelist/`); snippets `examples/specreq/{bbolt,bboltinternal}/`.
Commit under review: `1aa6fc1337` (HEAD of `specs-only`). Go: bbolt fork `743299d`
(`.lake/src/bbolt`), etcd `a4d2bb17` (`.lake/src/server`). Findings were written before reading
`batch-4c.md`/`open-questions.md`, then checked against them (each marked).

## Verdicts

| Batch | Verdict |
|---|---|
| **4c** (bbolt public API, internals, Options, errors) | **FAIL**: 9 first-tier findings (F1-F9), besides the recorded open decision 4c-D1 |
| **4d** (`internal/common`, `internal/freelist`) | **PASS** (two minor notes, below) |

The recorded open decision **4c-D1** (the sector rule: (a) OsFs's crash relation or (b) a crash
premise) counts as open; F2 and F10 sharpen it (what it must also cover, and that `boltCrash.spec`'s
text is not the same under (a) and (b)).

## Counts

- Specs checked: 145 function specs of package `bbolt` (the 149 files minus `Model`, `Api`,
  `Internal`, `Options`), 4 assumed `Options` triples, 90 of `internal/common`, 53 of
  `internal/freelist`: **292**. Close: 4d's 143 all; 4c's public read path, transaction lifecycle,
  `Sync`/`Close`/`Stats`/`Info`/`Path`/`Size`/`WriteTo`/`Logger`/`TxStats` (about 40) close; the
  write path through the internal layer (`Put`, `Delete`, `CreateBucket*`, `DeleteBucket`,
  `Cursor.Delete`, `Set/NextSequence`, `Commit`'s `rebalance`/`spill`/`commitFreelist`, about 15
  public and 30 internal) does **not** close from the internal specs as stated (F9); `Open` does
  not close for a custom `OpenFile` (F4).
- Laws checked: **60** (`Api` 25, `Internal` 4, `Options` 6 laws, `errors` 2, `common` 13,
  `freelist` 6, plus `Options`' 4 assumed triples counted above). Plausible: 53; not provable as
  stated: `boltCrash` (F1, F2; 4c-D1), `fileHolds_new` (F3), `optsAt_bool`/`_int`/`_freelist`/
  `_openFile`/`_logger` (F8, one defect five times); unusable together: `boltState_commit_au` with
  `boltState_settle_au` (F5).
- Snippets checked: **24** (`bbolt/` 11, `bboltinternal/` 13). Panic-free from the specs under their
  Assumes: 17. Not provable: `ReqCrashAtomicDurable` (F1), `ReqDefrag` (F4, F5, F6, F7),
  `ReqBackendOpen` (F7), `ReqBackendBatch` (F5 as its Assumes route it). Close with an extra
  assumption (minor): `ReqBackendRead`, `ReqNested`, `ReqWriteReload`.

## First-tier findings (4c)

### F1. The crash law is false for a database file created in the current generation (OsFs D4)

- **Evidence.** bbolt opens with `O_CREATE` (`db.go:234`, `243`) and never syncs the parent
  directory. OsFs: an `open` that creates gives `newMeta` with `named = false`
  (`Specs.lean:1392`, `openMeta`); nothing in OsFs sets `named` again (`OsFile.synced`,
  `Impl.lean:300-309`, keeps it); at a crash a file with `¬ f.named` may vanish
  (`OsCrash`, `Impl.lean:472-481`; D4, `notes/osfs-ext-plan.md:156`). `fileHolds_new`
  (`Api.lean:491-497`) accepts the absent path (`mo = none`) and any empty file (no `m.named`), and
  `fileHolds` counts "no file" as `Data.empty`.
- **The run.** `fileHolds_new` (no file) → `fileHolds_alloc` (`BoltSt.init Data.empty`) → `Open`
  creates the file → `Update` commits `D₁ ≠ empty` with `NoSync` off → `settle true false false`
  sets `dur := some []` → crash: the file is gone. `boltCrash.spec` (`Api.lean:523-531`) must give
  `σ.recovers D` for the `D` the next generation finds, `Data.empty`, but `σ.recovers` admits only
  `D₁`. No realization of `boltFile` can keep "every crash image is a database `σ.recovers`" across
  that settle. Independent of 4c-D1 (no sector is involved).
- **Caller.** `ReqCrashAtomicDurable` (`bank.go`): its first boot has no file; after an
  acknowledged transfer, the model's crash can take the file, and the panic "an acknowledged
  transfer is lost (the bank is gone)" is reachable in the model. etcd's first boot (the backend
  creates `member/snap/db`) is the same.
- **Not recorded** (4c-D3/D4 and open-questions 4.3 speak of names per generation, not of the
  directory entry; only `fileHolds_image` requires `m.named`).
- **Fix (a user decision, like 4c-D1).** Either (i) OsFs: a successful `fsync`/`fdatasync` of a
  file makes its name durable (a physical fact of journaled ext4 and xfs, where the file's sync
  commits the transaction that created it; it would go in `Impl.lean`'s environment with that
  argument), or (ii) `BoltSt` gains `named : Bool` (`init` from a created file sets it false;
  `recovers` admits `Data.empty` while it is false; no operation clears it), and the bank snippet's
  Assumes says the file pre-exists, or (iii) `fileHolds_new` requires `m.named = true` (no first
  boot from an absent path). A candidate `nonissues/` record ("bbolt never syncs the directory of a
  database file it creates"), not filed here (read-only round).

### F2. `init`'s first write extends an empty file; neither OsFs nor 4c-D1's rule as worded covers it

- **Evidence.** The fork's crash-safe `init` writes four pages with zero metas over a size-0 file
  (`db.go:722-731`), syncs, then the metas (`:733-740`), and `Open` reruns `init` when the meta
  bytes are zero (`metasZero`, `:748`). Its crash argument needs "a crash before the first sync
  leaves zero metas". OsFs: bytes past the durable image are arbitrary (`CrashImage`,
  `Impl.lean:463-468`, the `hd : i < f.durable.length` guard), and the size may be anywhere up to
  the write's target. So a crash there may leave 16 KiB of arbitrary bytes, including two valid
  metas (correct checksums: no collision needed) over a well-formed tree of any `D'`;
  `boltCrash` must then give `σ.recovers D'` with `σ = BoltSt.init Data.empty`: false.
- **Relation to 4c-D1.** Recorded decision, but its text covers a clean, idle page's rewrite ("its
  durable bytes or that write's", `batch-4c.md:129-141`); past the durable size there are no
  durable bytes, and the meta-page argument in the header (`Api.lean:37-44`) is about commits.
- **Fix.** State in 4c-D1 (either option) that a sector past the durable size written by one
  `pwrite` since the last sync holds zeros or that write's bytes (true of ext4 `data=ordered` and
  xfs, which never expose unwritten blocks; false of ext4 `data=writeback`, which the environment
  hypothesis must then exclude).

### F3. `fileHolds_new` is not provable together with `boltCrash`: it lacks `m.hi = 0`

- **Evidence.** `fileHolds_new` (`Api.lean:494-497`) takes `m.size = 0 ∧ m.maps = ∅` only. OsFs's
  crash relation lets the size come back anywhere in `[m.lo, m.hi]` with unknown bytes
  (`FileCrashed`, `Crash.lean:47-58`): an empty file whose `hi > 0` (a truncation not yet synced, a
  state OsFs's ghost state admits) may come back as an old database. `fileHolds` promises "all of it
  durable"; the law's prover cannot derive `hi = 0` from `osMeta`.
- **Fix.** Add `m.hi = 0` (true of every empty file reachable through OsFs's proved specs:
  `newMeta`, and `initMeta` of an empty boot file); with F1(iii), `m.named = true` too.

### F4. `openFileOk` is persistent, so etcd's defrag closure cannot meet it

- **Evidence.** `openFileOk` (`Api.lean:311-317`) is `□ ∀ flag mode Φ, …`, and each call must hand
  out `osFileOf fl fd ∗ osFd fd (own 1) …`, exclusive. etcd's closure returns the one file it
  created, every time (`backend.go:522-526`: `return temp, nil`); a persistent contract cannot hand
  out that exclusive file (a second call would need a second copy). `Open` calls `OpenFile` once
  (`db.go:243`; `Tx.WriteTo` reopens only with `WriteFlag ≠ 0`, `tx.go:413`, which `boltTx` fixes
  at 0).
- **Caller.** `ReqDefrag`'s `bolt.Open(tmpPath, …, opts)`; 4a's defrag.
- **Fix.** Drop the `□`: a one-shot contract (`∀ flag mode Φ, ▷ … -∗ WP …`), which the closure meets
  from the file's resources.

### F5. `boltState_commit_au` and `boltState_settle_au` cannot both be built from one state

- **Evidence.** Each law (`Api.lean:478-488`) consumes `boltState γ 1 σ`; `Tx.Commit.spec` (and
  `DB.Update.spec`'s callback) needs both atomic updates in its precondition, before the call. A
  holder of the whole state (the use the laws are documented for, `Api.lean:470-471`) has one copy.
  Moreover the settle law's update is built at `σ` and commits only at `σ` (`COMM ⌜σ' = σ⌝`), while
  the commit update fires first and moves the state to `σ.commit …`.
- **Callers.** `ReqBackendBatch` (its Assumes routes `Commit`'s updates through these two laws);
  `ReqDefrag` ("the caller holds tmpdb's boltState whole"). Clients that keep `boltState` in an
  invariant (`ReqBank`, `ReqNested`, `ReqBackendRead`) are unaffected.
- **Fix.** One law giving both: `boltState γ 1 σ ⊢ |={E}=> AU_commit(Q) ∗ AU_settle(S)` with
  `S synced failed brk := ∃ ok, boltState γ 1 ((if ok then σ.commit D ns else σ.attempt D ns).settle
  synced failed brk)` (realized with an invariant outside `γ.ns` holding the state between the two
  commits); drop `boltState_settle_au`, or keep it for `DB.Sync` only. Or rewrite the snippets'
  Assumes to an invariant and drop both laws.

### F6. No law gives clients the size bounds of stored keys and entries; defrag's copy cannot meet `Put`'s premises

- **Evidence.** `Bucket.Put.spec` requires `kb.length + vb.length ≤ bboltEntryMax`,
  `CreateBucketIfNotExists` requires `kb.length ≤ maxKeySize`. `Ent.wf` (`Model.lean:124`) states
  only sorted, non-empty keys, so `boltTx_wf` gives no bound; `fileHolds`' docstring lists "entries
  within `bboltEntryMax`, bucket names within `maxKeySize`" but nothing exports it.
- **Caller.** `ReqDefrag` (and etcd's `defragdb`, `backend.go:827, 849, 905, 930`): it copies
  names and entries read from the source transaction, with no premise of its own on them.
- **Fix.** Add to `Ent.wf`: every key `≤ maxKeySize`, every value entry's key plus value
  `≤ bboltEntryMax` (every operation keeps it: `Put` refuses longer keys and takes the entry bound,
  `CreateBucket*` take the name bound; `fileHolds` already has it).

### F7. `Options` has no spec for a keyed literal

- **Evidence.** `optsLit.spec` (`Options.lean:44-48`) covers `Options{}` (`LiteralValueV []`) only.
  etcd's `boltOpenOptions = &bolt.Options{MmapFlags: syscall.MAP_POPULATE, NoFreelistSync: true}`
  (`config_linux.go:29-32`), copied into every backend's options (`backend.go:216-219`), and the
  snippets `ReqBackendOpen`, `ReqDefrag` use keyed literals.
- **Fix.** A keyed-literal spec (the tracked fields set, the untracked ignored), or the snippets
  rewritten as `&bolt.Options{}` plus field stores and the backend's initializer given its own
  assumed fact.

### F8. The `optsAt` field laws give two restoring wands with `∗`: false in the intended model

- **Evidence.** `optsAt_bool.spec` (`Options.lean:100-110`, likewise `_int`, `_freelist`,
  `_openFile`, `_logger`): `optsAt l dq o ⊢ ∃ dq' x, F ↦{dq'} x ∗ ⌜…⌝ ∗ (F ↦ x -∗ optsAt l dq o) ∗
  (⌜dq = own 1⌝ -∗ ∀ y, F ↦ y -∗ optsAt l dq o')`. With `optsAt` the struct's points-to (the
  realization the header promises, "they become lemmas of the struct"), both wands need the other
  fields' points-to; `∗` splits them, so the entailment fails for `dq = own 1`. These are assumed
  statements (trust boundary). No derivation of a duplicate points-to was found (each wand eats the
  field's only points-to), but an assumption false in the model is unsound by the hard rule.
- **Fix.** `∧` between the two wands, or one wand `∀ y, ⌜dq = own 1 ∨ y = x⌝ -∗ F ↦ y -∗ optsAt l dq
  (set o y)`.

### F9. The internal layer does not carry the abstraction: the write path's sketches do not close

- **Evidence.** `physRep` (`Internal.lean:160`) is an opaque `Prop` with no law; `wtxCore_view`
  (`:186-188`) is the only bridge, `boltTx tx γ 1 T ⊣⊢ ∃ C, wtxCore tx γ C ∗ ⌜physRep T C⌝`. The
  internal posts lose it: `Cursor.node.spec` returns `∃ C', wtxCore tx γ C'` and some leaf node,
  not physRep of `T` nor that the leaf is the key's (`Cursor__node.lean:30`); `node.put`/`node.del`
  give the new node but no physRep for the updated view; `node.rebalance`, `Bucket.free`,
  `node.spill` return `∃ C', wtxCore tx γ C'` (and a flag); `DB.allocate`/`Tx.allocate` return no
  page buffer (`bytesPointsto pg …`) and do not tie `pg` to an id, while `node.write` and
  `freelist.Write` need one. So `Bucket.Put`'s sketch (seek, `Cursor.node`, `node.put`, "the
  abstraction relation then maps the nodes to `T.cur` with the key set") has no step that gives
  `physRep (T.setCur …) C''`; the same for `Delete`, `CreateBucket(IfNotExists)`, `DeleteBucket`,
  `Cursor.Delete`, `SetSequence`/`NextSequence`, and `Bucket.rebalance` (from `node.rebalance`),
  `Bucket.spill` (from `node.spill` → `Tx.allocate` → `node.write`), `Tx.commitFreelist`
  (`Tx.allocate` → `freelist.Write`).
- **Relation.** `batch-4c.md` 4c-Q5 records the 94 internal specs as "done, mirroring the code";
  the scope rule lets internal specs mirror the code, but each must still give its caller's next
  step. The public specs themselves look true of the code (checked against `bucket.go:434-493`,
  `149-194`, `cursor.go:95-280`, `tx.go:171-310`).
- **Fix.** Laws on `physRep` (pure obligations): materializing nodes keeps it; `node.put`/`del` at
  the key's search leaf (`curPath`'s leaf, which `Cursor.node` must return) give physRep of the view
  with the key set/removed; rebalancing and spilling keep it (with `TxCore.pages`). `Tx.allocate`
  and `DB.allocate` return `bytesPointsto pg (own 1) bs` with `hdrOf bs` = the new id and overflow
  and an empty count/flags (what `node.write`'s `nodeWritable` and `Write` need), or an access law
  for `C.pages` from `wtxCore`.

## The recorded open decision and its sharpening

- **4c-D1 (open, counts).** Checked with the axiom mindset: without a sector rule, a crash during
  or after a commit's meta write may leave any bytes in the slot, including a correctly summed meta
  of a state that never existed; with the rule as worded, every meta-page case I tried closes (a
  synced commit's next meta write is onto a clean idle page; a meta write lost by a failed sync is
  still per-sector old or new; `NoSync` and `lost` promise nothing). Attacks tried and blocked:
  concurrent `DB.Sync` during a meta write (`busy`), a failed `DB.Sync` racing a commit (`lost`
  set before or after the commit update, either way recorded), an attempted meta write that wrote
  nothing (`attempt` over-approximates), pages released at the next `Begin(true)` that the older
  on-disk meta still reaches (the newer meta is durable whenever `dur ≠ none`), `grow` without
  `NoGrowSync` (the data sync covers the size, D3), `WriteTo` racing a writer on free pages (they
  are outside the image's tree).
- **F10 (sharpening).** `boltCrash.spec` is written over `crashRest`, whose `CrashRel` knows only
  bytes marked clean (`Crash.lean:35-58`). Under (b) the law must be over `crashRestQ`
  (`CrashP1.lean`); under (a) `CrashRel`/`crashRest` must carry the new rule's facts (ghost state of
  the writes since the last sync). So "`boltCrash.spec` is true under either" (`Api.lean:522`) holds
  of the intended law, not of this text: its statement changes with the choice.

## Proof plans

### 4c public API (`Spec/go_etcd_io/bbolt/`)

- **`Open`**: alloc `db`; `optsArg` read through `Options`' laws (F7, F8); `os.OpenFile` over OsFs
  (no `Spec/os` on this branch: `osFileOf` provisional, recorded at I7) or `openFileOk` (F4); trivial
  `flock`; open `boltFile γ` with `boltClosed γ` for the file's halves; `Stat`, `metasZero`, `init`
  (crash fact: F2) or `getPageSize`/`mmapUnlocked` (4d decoders, `Meta.Validate`), `loadFreelist`
  (4d `Read`/`Init` on a new freelist: premises trivially met); allocate `isBolt`'s invariants. Error
  paths give `boltClosed` back. Closes but for F2, F4, F7.
- **`DB.Begin`** read: `metalock`, a reader slot for `threadTok`, `opened`/`data` checks (else
  `dbClosed ∨ dbBroken`), meta copy = linearization point (fire the read AU), `AddReadonlyTXID`
  (4d: `readersOk` from `Internal.lean`'s freelist side), `statlock` (the slot pair). Write:
  `rwlock`, `metalock`, `t.init` (txid + 1, receipts bound), `ReleasePendingPages` (4d, `readersOk`,
  count bounds). Closes. (`DB.beginTx`, `DB.beginRWTx`: the same, internal.)
- **`DB.View`/`DB.Update`**: `Begin`, mark managed, the callback's contract, `Rollback` /
  `Commit`. Close given `Commit`.
- **`Tx.Commit`**: read tx: logger calls, `ErrTxNotWritable`, still live: closes. Write tx:
  `rebalance` → `spill` → `freelist.Free` of the old freelist page (`canFree` from the freelist
  invariant) → `commitFreelist` → `grow` → `write` → `writeMeta` (commit AU at the `pwrite`'s
  first step, prophecy 4c-D2) → settle AU → `close`; every error path fires both AUs then
  `rollback`. The stage chain (`wtxAt` nodes/spilled/flushed) closes at its level, but its internal
  callees do not give what it needs (F9).
- **`Tx.Rollback`**, **`Tx.close`**: `removeTx` (slot back = `threadTok`; `RemoveReadonlyTXID`) or
  4d `Rollback` (`canRollback`); finished: `ErrTxClosed` through `txDone`. Close.
- **`Bucket.Get`, `Bucket.Bucket`, `Tx.Bucket`, `Bucket.Cursor`, `Tx.Cursor`, `Cursor.First/Next/
  Seek/Last/Prev`, `Bucket.ForEach/ForEachBucket`, `Tx.ForEach`, `Bucket.Sequence`**: over
  `boltTx` at any fraction and the internal cursor specs (`seek`, `first`, `next`, `keyValue`,
  `curPath`, `seekRaw`), which are adequate for reads (they relate the stack to `T.ents p`). Checked
  against Go's edge cases: `Prev` at the first entry stays there (`cursor.go:260-268`, the #733 fix),
  `Next` past the end stays, `Get` of the empty key in an empty bucket returns nil, `Last` on an
  empty bucket. Close.
- **`Bucket.Put/Delete/CreateBucket(IfNotExists)/DeleteBucket/SetSequence/NextSequence`,
  `Tx.CreateBucket(IfNotExists)/DeleteBucket`, `Cursor.Delete`**: error order matches Go
  (`bucket.go:464-474`, `160-183`; `DeleteBucket`'s empty-name case exact); the success arm does not
  close (F9).
- **`DB.Sync`**: OsFs `Fdatasync` at the update; closes. **`DB.Close`**: three locks, the file's
  halves back to `boltFile`'s closed state, `dbClosed`; closes. **`DB.Stats`** (`statSlot`),
  **`DB.Info`** (needs the mapping: `boltTx` keeps it), **`DB.Path`**, **`DB.Logger`**,
  **`Tx.DB/ID/Size/Writable/Stats`**, **`Bucket.Tx/Writable`**, **`Options.String`**
  (`loggerPtrOk`), **`TxStats.*`** (atomics in an invariant): one step each; close.
- **`Tx.WriteTo`**: `WriteFlag = 0` → the db's fd; metas built in place (4d, `ReqWriteToMeta`);
  `io.CopyN` of a section reader (Perennial's `io`: a recorded need) through `writerOk`; pages of the
  transaction's tree are pending under it (not reused). Closes given Perennial's `io` specs.
- **Internal (94 files)**: the read-side ones (`Cursor.search/nsearch/seek/first/last/next/prev/
  keyValue`, `Bucket.pageNode/openBucket`, `node.read`, `Tx.page`, `DB.page/meta/pageInBuffer/
  getPageSize*`, `mmap*`, `munmap`, `fileSize`, `metasZero`, `hasSyncedFreelist`, `freepages`,
  `loadFreelist`, `newFreelist`, `cloneBytes`, `compareKeys`, the check helpers): plausible as
  stated. The write side: F9.

### 4d (`internal/common`, `internal/freelist`)

- **`common`** (90): each getter/setter is a `decode`/`replaceBytes` over `bytesPointsto` (one line
  each); `WriteInodeToPage` (loop invariant: `nodeBody` prefix; branch `Assert` from the premise;
  the fork's `UnsafeByteSlice` is `unsafe.Slice`, no `MaxAllocSize` bound, `unsafe.go:24-26`);
  `ReadInodeFromPage` (`pageReadable`); `Meta.Write` (panics excluded by premise), `Meta.Validate`
  (`metaErr`, error values by `errIs_init`/`errIs_distinct`), `Sum64` (`fnv64a`); `Pgids.Merge`/
  `Mergepgids` (matches `len(a)==0`/`len(b)==0` early returns); `Verify` (`WP f ∧ Q`); `Assert`.
  All close.
- **`freelist`** (53): `Interface.<M>` from the two concrete specs by `flOwn_dyn` and
  `method_interface_ok`; `Allocate`, `Free` (`canFree`: meta pages, double free, `Verify`'s
  `allocs` check), `Rollback` (matches `shared.go`'s "nothing freed: return before forgetting
  `allocs`"), `ReleasePendingPages` (`release(minid-1)` gives `mustRelease`, `releaseRange` gaps give
  `releasable`; `readersOk` excludes the wrap), `Read`/`Init`/`Reload`/`NoSyncReload` (the hash map's
  empty-`Init` premise), `Write`/`EstimatedWritePageSize`/`Copyall`/`Count`. All close.

## Snippets

| Snippet | Verdict | Sketch / gap |
|---|---|---|
| `ReqBackendOpen` | no (F7) | the keyed literal; then `optsAt_bool`, `Open` |
| `ReqBackendBatch` | no as routed (F5) | `Begin(true)`; `CreateBucketIfNotExists` (needs "the root has no value at `key`": minor); `Tx.Bucket`; `boltTx_fill`; `Put`×2, `Delete` (but F9); `Seek`/`Next` loop with `txBytes_acc` (txLive) and `boltTx_wf`'s order; `Get`; `Commit`'s two AUs from the laws: F5 |
| `ReqBackendRead` | yes, minor | invariant-held `boltState`; snapshot by `TxView.ro`; reader goroutines on fractions; `Size` `< 2^48`; `Stats` on `statSlot (some (tx,T))`; `Rollback`. Missing in Assumes: `k`'s length bound for the writer goroutine's `Put` (`bboltEntryMax` premise) |
| `ReqDeleteBucketNotFound` | yes | `DeleteBucket` arms; `errors.Is` by `isErr`; `Tx.Bucket` nil after `dropBkt` |
| `ReqHash` | yes | `View`; root cursor; `Tx.Bucket` (root only buckets assumed); `ForEach` with `txLive` share in `I` |
| `ReqSnapshot` | yes | `boltTx_size`, `WriteTo`'s `err = nil → ys = img`, length `sz` |
| `ReqDefrag` | no (F4, F5, F6, F7) | otherwise: `putLoan` held until the copy's commit, then the source's `Rollback` (etcd's order); `dbBroken_state`; double `Close` |
| `ReqCrashAtomicDurable` | no (F1; F2, 4c-D1) | with F1 fixed: invariant over `σ.recovers`, both AUs from it, `acked` after `S true false false` |
| `ReqNested` | yes, minor | all arms check out (`ErrBucketExists`, `ErrIncompatibleValue`, nil `Get` of a bucket, sequences, `ForEach` nil values, `Last`/`Prev`); Assumes must add "no other writer" (the `View` and the final `DeleteBucket` panic otherwise) and "the root holds only buckets" (`Tx.ForEach`) |
| `ReqReadOnlyPut` | yes | every mutation's `T.rw = false` arm; `Commit` leaves it live; `Rollback` |
| `ReqCursorDelete` | yes (spec level; F9 below) | `First`; copy `k` (`txLive` in its pre); `Delete`; `Get` nil; `Seek` repositions at the new view to the next key |
| `ReqNodeRoundTrip`, `ReqElementKeys`, `ReqMetaRoundTrip`, `ReqWriteToMeta`, `ReqPageSortWrite`, `ReqVerify`, `ReqInlineBucket`, `ReqMergePgids` | yes | the codec laws (`hdr_withHdr`, `writeNode_read`, `meta_withMeta`, `metaValid_summed`, views); `Validate`'s error on a bad magic |
| `ReqAllocFree`, `ReqReleaseSafe`, `ReqRollback`, `ReqReloadEmpty` | yes | `canAlloc`/`canFree`; `releasable` excludes the page under reader 4 (`a ≤ 4 < 5`), `mustRelease` releases it after; `rollback` drops it; empty-`Init` premise from "no free page" |
| `ReqWriteReload` | yes, minor | `freelistPage_read`; `wf` gives `Nodup` and `≥ 2`; Assumes "pageSize positive" should bound it (`(est/ps+1)*ps` overflows `int` for `ps` near `2^62`, and `make` panics) |

## Laws (judged)

- Plausible from the stated realization and not vacuous: `persistent`, `timeless`,
  `boltState_frac`, `excl`, `boltOpened_closed`, `boltTx_wf`, `boltImage_wf`, `boltTx_size`,
  `putLoan_done`, `dbBroken_state`, `boltTx_later`, `boltTx_frac`, `boltTx_base` (the writer holds
  `rwlock`), `bktH_live`, `txBytes_acc` (nodes never written in place; no remap before the commit),
  `txLive_frac`, `boltTx_fill` (non-NaN), `boltState_read_au`, `fileHolds_image` (requires
  `named`, `lo = hi`, clean bytes), `fileHolds_alloc`, `boltLogger_nil`; `wtxCore_view`,
  `txPage_persistent`, `wtxCore_keys`, `bktVal_persistent`; `optsAt_laws`; `errIs_init`,
  `errIs_distinct`; all of `common`'s (pure round trips true by the encodings; `meta_in_sector`
  `16 + 64 ≤ 512`; `init.spec` 4096 on linux/amd64, trusted); all of `freelist`'s.
- Not provable as stated: `boltCrash` (F1, F2, 4c-D1, F10), `fileHolds_new` (F3), the five
  `optsAt_*` field laws (F8). Unusable together: `boltState_commit_au` + `boltState_settle_au` (F5).
- Vacuity: every opaque predicate is pinned by at least one law or spec that fails at `True`
  (`excl`, `boltState_frac`'s agreement, `boltTx_base`, `bktH_live`, `dbBroken_state`); `physRep`
  is the exception (no law at all: F9).

## Bugs in the Go code

None new in bbolt's or etcd's behaviour. Candidate `nonissues/` record from F1: bbolt creates the
database file and never syncs its directory, so on POSIX a crash may lose a file whose commits were
all synced (on journaled ext4 and xfs the file's sync commits its creation in practice). Not filed
(read-only round); `issues/` and `nonissues/` have no such record.

## First-tier findings, one line each

- F1 `Api.lean:491-531`: crash law false for a file created this generation (OsFs D4, `named =
  false`, bbolt never syncs the directory); breaks `ReqCrashAtomicDurable`. New.
- F2 `db.go:722-731` vs `Impl.lean:463-468`: `init`'s first write past the durable size is
  arbitrary at a crash; 4c-D1's rule as worded does not cover it. Sharpens 4c-D1.
- F3 `Api.lean:491-497`: `fileHolds_new` needs `m.hi = 0`. New.
- F4 `Api.lean:311-317`: `openFileOk`'s `□` makes etcd's defrag closure (`backend.go:522-526`)
  unable to meet it; make it one-shot. New.
- F5 `Api.lean:478-488`: the commit and settle update laws each consume `boltState γ 1 σ`;
  `Commit` needs both up front. New.
- F6 `Model.lean:124`: `Ent.wf` lacks the key/entry bounds; defrag's copy cannot meet `Put`'s and
  `CreateBucketIfNotExists`' premises. New.
- F7 `Options.lean:44`: no keyed-literal spec (`config_linux.go:29`, two snippets). New.
- F8 `Options.lean:100-150`: two restoring wands joined by `∗`, false in the struct model; use `∧`.
  New.
- F9 `Internal.lean:160` and the internal write-path specs: `physRep` has no laws and the posts
  drop it or the page buffer; the public write path does not close. Challenges 4c-Q5.
