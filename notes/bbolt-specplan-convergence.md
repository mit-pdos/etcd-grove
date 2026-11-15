# Plan: real bbolt's proof converging to the spec plan's bbolt API

**Date:** 2026-11-12. **Status:** plan, not reviewed. **Scope:** the real proof
(`Spec/go_etcd_io/bbolt/**`, `Proof/go_etcd_io/bbolt/**`), after its port onto the per-byte file
extension (`notes/bbolt-port-plan.md`), and the spec plan's bbolt (`SpecPlan/Spec/go_etcd_io/bbolt/**`,
batch 4c and the 2026-11-12 handle revision; `notes/specs-only/ledger.md`). CLAUDE.md, "The spec plan
and convergence": new and reworked real specs take the spec plan's statement unless the proof shows it
wrong, and a defect goes to the ledger first.

## 1. Where the two stand

The real proof covers bbolt's in-process API over a **two-level** data model (`Data := GMap GoString
(GMap GoString GoString)`: top-level buckets of key/values) with **no durability** (`fileHolds` is the
page cache's bytes; port plan §0). The spec plan's API is a superset in four directions at once, each
reaching the invariants:

| direction | spec plan | real | reaches |
|---|---|---|---|
| durability | `boltFile γ` (crash invariant), `BoltSt` (`recovers`, `dur`, `busy`, ...), two-phase `commitAU`, `DB.Sync`, `boltCrash` and the file laws | none | the file's resources split between a crash invariant and the open database; every write, sync, grow, init |
| data model | `Ent` tree: nested buckets, root values, sequences; `BPath` | depth 1 | `Inv/Shape*`, `treeData`, `BRec`, `wtxData`, spill/rebalance of inline nested buckets, recursive `DeleteBucket` |
| handles | ownership tokens `bktOwn tx γ p o q` (the parent's cache entry), `bktH`, `bktUse`; `txLive` apart from `boltTx`; cursors repositioned at the current view | generations `T.gen n`, `boltBkt tx γ b n g`, `hdlAuth`; `txBytes` read against `boltTx`; a cursor tied to its view | the writer's handle registry, `txBytes_acc`, `boltCurDef` |
| edges | `boltClosed`/`boltOpened`/`dbClosed`, `dbBroken`, `isBolt db γ ns` (`NoSync`), custom `OpenFile`, nil options, `statSlot_wtx`, `γ.path`, named error values on read transactions, `putLoan`, `txSize` | `Close` returns `True`; one error disjunct; no custom `OpenFile` | `Open`, `Close`, `Begin`, every mutation's error arm |

Counts (the gap map of 2026-11-12, reproducible by diffing the two `Spec` directories): of 60 public
functions, 3 differ by vocabulary only (`DB.Info`, `Tx.DB`, `Options.String`), 36 are strictly
stronger in the spec plan, 21 have no real spec (`DB.Path/Sync/Update/View`, `Tx.Cursor/ForEach/
Writable/WriteTo`, nested `Bucket.*`, sequences, `Cursor.Delete/Bucket`, `Bucket.Tx/Writable`). The 85
internal specs all have a real counterpart of the same function, 7 of similar shape; the other 78 are
over the spec plan's abstract internal vocabulary (`wtxCore`, `physRep`, `dbRaw`, `wtxAt`), which is
not client-facing: converging them is optional (the public API is what clients see).

## 2. The spec plan must first move onto the per-byte extension

The spec plan's bbolt (and backend, WAL, `etcdserver/ApiBoot`) is stated over the v1 extension
(`GooseLang/Ext/OsFs`), which the main tree keeps only for it (port, step 0). Its file-level statements
change, the rest only by the instance binders:
- `fileHolds path D` → by inode with `pathHolds R V path D` at `Open`, as the real `Open.spec` now is
  (its no-file case needs `RootsOk R`, the real proof's finding);
- `osFileOf`, `openFileOk` (custom `OpenFile`): an `*os.File` over an `OsFd` by inode;
- `boltCrash`: v1's `crashRest` → the per-byte extension's restart resources (`GooseLang/Ext/Fs/CrashTok`,
  `Proof/os/CrashSt*`, as minibolt's `BootP1`). Its premise is decision 4c-D1 (the sector rule), still
  the user's: under the per-byte extension the general crash rule allows a torn page in a crash image,
  and minibolt's crash theorem takes its own premise (P1, no checksum collision on a torn meta).
  So 4c-D1 becomes: take P1 (as minibolt) or a sector rule (as the WAL), for real bbolt.
Each change is a ledger entry. It is spec-only work (no proof), about 150 modules to rebuild.

## 3. Stages for the real proof (each leaves the build green, the trust base unchanged)

- **S0, done (2026-11-12):** the port onto the per-byte extension (`notes/bbolt-port-plan.md` §7).
- **S1, shallow, no new invariant:** restate over the spec plan's names what the real invariant already
  carries: `Tx.ID`, `DB.Logger` over `boltTx`/`isBolt` (today internal-shaped); the trivial functions
  `Tx.Writable`, `Bucket.Tx`, `Bucket.Writable`, `Cursor.Bucket`, `Tx.Cursor` (the root bucket);
  read-transaction error arms (`ErrTxNotWritable` for `Put`/`Delete`/`Create*`/`Commit`, `ErrTxClosed`)
  and named `isErr` values; `txSize` (pinning `Size`'s result); `View`/`Update` (a managed transaction
  over `Begin`/`Commit`/`Rollback`), `Tx.ForEach`/`Bucket.ForEach` (top-level only until S3).
- **S2, handles:** ownership tokens in place of generations (the writer's `hdlAuth` becomes a ghost map
  of paths to cache entries, agreeing with `b.buckets`; laws `bktOwn_frac`, `bktOwn_bktH`, `bktH_live`);
  `TxView` loses `gen`, gains `managed`/`noSync`; `txLive` apart from `boltTx` (a writer's returned bytes
  stay valid across its own `Put`/`Delete`: node bytes are never written in place, the mapping is not
  remapped before the commit); cursors repositioned at the current view; `Cursor.Delete`.
- **S3, the data model:** `Data` becomes the spec plan's `Ent` tree (`Model.lean`); nested buckets
  through every shape invariant, inline nested buckets in spill/rebalance, recursive `DeleteBucket`,
  sequences (`InBucket`'s field; its getters are proved), root values. The largest in-process stage.
- **S4, the edges:** `boltClosed`/`boltOpened`/`dbClosed` (`Close` gives the file back; a second `Close`
  is nil), `dbBroken`, `isBolt db γ ns`, custom `OpenFile`, nil options, the writer's spare `statlock`
  slot (`statSlot_wtx`), `γ.path` with `DB.Path`.
- **S5, durability:** the crash invariant `boltFile γ` (a half of each file resource, minibolt's
  `csInv` as the template), `BoltSt` and the two-phase `commitAU` fired at the meta write and at the
  sync, `DB.Sync`, `Open`'s pre-commit sync, the file laws and `boltCrash`; after §2 and 4c-D1.

S1 can start now; but most of it is stated over S2's handle and cursor vocabulary (`Tx.Cursor`, `Bucket.Tx`, `Cursor.Bucket`, the read-transaction arms of the `Bucket` mutations take `bktH`/`bktUse`/`boltCur … b p`), so in practice S1 is `Tx.Writable` (done 2026-11-12: `Spec/go_etcd_io/bbolt/Tx__Writable.lean`, the spec plan's triple over the real `boltTx`), `Tx.ID`/`DB.Logger`, `txSize`, `View`/`Update`, and S2 comes next. S2 before S3 (the handle registry is keyed by path, which S3 generalizes). S5 needs
§2 and the user's 4c-D1.

## 4. Decisions for the user

1. The order above, and whether S3 (nested buckets) is wanted before S5 (durability): etcd uses only
   top-level buckets (`ReqBackendBatch`); `ReqNested` is the spec plan's own requirement.
2. 4c-D1 under the per-byte extension: P1 (minibolt's premise) or a sector rule, for real bbolt's
   crash law.
3. Whether the 78 internal specs over the spec plan's abstract internal vocabulary are a target at all.
