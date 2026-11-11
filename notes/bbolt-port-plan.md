# Plan: real bbolt onto the per-byte Linux file extension

**Date:** 2026-11-12. **Status:** plan, revised after its review
(`notes/axiom-review/bbolt-port-plan-review/README.md` on `fs-bytes`); no proof written yet. **Scope:**
the real bbolt proof of `origin/lean` (`Proof/go_etcd_io/bbolt`, `Spec/go_etcd_io/bbolt`; 1044 `.lean`
files), today over the v1
extension (`GooseLang/Ext/OsFs`: files by path, `(value, clean)` bytes, unsynced bytes arbitrary at a
crash), moved onto branch `fs-bytes`'s extension (`GooseLang/Ext/Fs`: files by inode under a directory
tree, per-byte page cache + stamped crash candidates, at most one change in flight per file). The user's
order: specs first, then invariants, then the expensive proof work once the plan is solid.

Inventory commands: `git archive origin/lean Proof/go_etcd_io/bbolt Spec/go_etcd_io/bbolt ...` into a
scratch directory, then `grep` (the lists below are reproducible from those patterns).

## 0. Summary

- **Real bbolt has no crash theorem.** Its exported results are Hoare specs of the public API (`Results.lean`
  prints the axioms of `Bucket.wp_*`, `Cursor.wp_*`, `DB.wp_*`, `Tx.wp_*`); no `RealCrash*`, no crash spec,
  no `CrashImage` reasoning (`Proof.os.CrashFile` is imported only for `osBytes_halves`). So **P1 is not
  needed** and crash candidates never matter to it: every byte it owns is read through its value
  (`xs.map Prod.fst`). The port is a change of *resource shape and file naming*, not of crash reasoning.
- **463 of the 1044 files touch the OS layer.** 363 carry only the section variable `[hos : HasExt
  osFsExt]` and are handled by a script; 38 more need manual edits of file names (`K.p`, `(p : GoString)`
  binders, `Inv/Ctx`'s `BC.p`); 62 files (20.5k lines) hold or pass file resources (`osMeta`, `osBytes`,
  `osSlot`, `osFd`, `OsMeta`, `pwBytes`, `pwSize`): the real work, concentrated in `Inv/Store.lean` (2,804
  lines), `Open.lean`, `Open/*`, `Mmap/*`, `Commit/*`, `Tx__write*`, `Tx__writeMeta`, `DB__init`,
  `fdatasync` (§1).
- **Three things are not mechanical and need a decision first** (§2.4, §6):
  1. *D22*: `Tx.writeMeta`'s commit point needs a one-page meta write to land all or nothing in-process;
     the new semantics lets a `pwrite` land any prefix. Fix: a trusted `PWriteFinish` rule, *whatever the
     errno, the landed prefix is empty, the whole write, or ends on a 4096-byte file-page boundary*,
     measured on C (§2.4).
  2. *File naming*: v1's `osMeta path none` ("no file here") has no counterpart; `Open` must take the
     directory tree (`osTree`) to look up or create `path`. An API change of `Open.spec` only.
  3. *Durability-free syncs*: bbolt's `fdatasync` spec holds no file bytes; the new `Fdatasync` needs the
     bytes covering every not-yet-durable byte (`Covers`). The byte-less `fsync` spec this forces is a
     program-logic change, no trusted change (§2.3).

## 1. Inventory

Counts as the review re-derived them (`notes/axiom-review/bbolt-port-plan-review/inventory.py`,
`mechanical.py`): 1044 `.lean` files, 463 touching the OS layer.

### (a) Section variable only: 363 files, by script

Only `variable [hos : HasExt osFsExt]` (and `osN`, `osInv`) — most of the readers (`Read/*`), the writer's
tree code (`Write/*`, `Spill/*`, `Rebalance/*`, `Bucket__*`, `Cursor__*`, `node__*`), the freelist,
stats. Edit: `[hos : HasExt osFsExt]` → `[ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]` (the section
variables of fs-bytes' clients, e.g. `Spec/github_com/.../bboltfs/testMinibolt.lean`), `open Fs`, imports
`GooseLang.Ext.OsFs.*` → `GooseLang.Ext.Fs.*`. A `sed` script (§5).

### (a') File names, by hand: 38 files

The file is named by `K.p`/`BC.p : GoString` (the context `BC`, defined in `Inv/Ctx.lean`) or by a binder
`(p : GoString)` threaded to resources; with files by inode these become `K.i`/`BC.i : Ino` and `(i : Ino)`.
`Inv/Ctx.lean` (the definition of `BC.p`); 21 files using `K.p` (`DB__beginRWTx` 16×, `Commit/Step` 11×,
…); 16 files with `(p : GoString)` file binders (`Inv/Bolt` 7×, `Inv/Tx`, `Inv/Txs`, `Commit/TailSlots`,
`Write/Retarget`, …). The script does none of these; the review's `mechanical.py` lists them.

### (b) os specs by name only: 4 files

`Proof/go_etcd_io/bbolt/Link.lean` (links the os/syscall/unix proofs), `internal/common/Init.lean`,
`internal/common/Verify.lean` (package initializers), `Spec/go_etcd_io/bbolt/Options.lean`. Regenerated or
mechanical once §2's specs exist (`etc/gen-link.py --bbolt`, `etc/gen-init.py`).

### (c) File resources: 62 files (20.5k lines)

The 52 below plus 10 the first inventory missed: `Commit/PubOk`, `Commit/PwMeta` (`pwBytes`/`pwSize`, the
D22 lemma), `Commit/TailFPure`, `Commit/TailFWrap`, `Commit/TailPartErr`, `Commit/TailPub`,
`Commit/WriteDefs` (`osSlot`), `Mmap/GrowPure`, `Open/CoreFacts`, `Open/Facts`. Also `DB__grow.lean:282`
builds a v1 `OsMeta` literal positionally, with fields that are gone (`named`, `ok`, `dur`, `durHi`).

| group | files | relies on |
|---|---|---|
| vocabulary / API | `Spec/.../Api.lean`, `Spec/.../Tx__write_ext.lean`, `Spec/.../fdatasync.lean` | `fileHolds path D` (sealed), `osMeta p 1 (some m)`, `osFd ⟨p, true, true⟩`, `osSlot` |
| invariant | `Inv/{FileHolds,Store,Locks,WSlots}.lean` | `osMeta p 1 (some m)` with `m.maps`, `osBytes p off 1 xs : List (w8 × Bool)` read by value (`osSlot p s bs := ∃ xs, osBytes p (4096 s) 1 xs ∗ ⌜xs.map Prod.fst = bs⌝`), `osInv` |
| open | `Open.lean`, `Open/{Carve,Close,Core,FileFacts,Flock,MetasZero,MmapOwn,PageSize,ReadHeld}.lean` | `OpenFile` (0x42, by path), `Stat`/`Size`, `ReadAt` (`readPageSize`), `Flock`, `osMeta path none` for "no file" |
| mmap | `Mmap/{FileSize,GrowEnd,GrowRes,GrowWdb,Map,Munmap,RemapBase,RemapBody,RemapCells,RemapEnd,RemapLost,Unmap}.lean`, `DB__grow.lean` | `Mmap`/`Munmap`/`Madvise` (`m.maps`), `Truncate` (grow: `osGrown`), `Sync` |
| commit / write | `Commit/{MetaBytes,RollbackFacts,RollbackReload,TailAcc,TailMeta,TailWrite,WriteExtDefs,WriteExtRun,WriteLoop,WritePage,WriteRun}.lean`, `Tx__write.lean`, `Tx__writeMeta.lean`, `Tx__rollback_f.lean` | `WriteAt` (`pwBytes`, `pwSize`, D22's `j = 0 ∨ j = len`), `Proof.os.WriteChunks` (chunked writes), `fdatasync` |
| init / freelist / close | `DB__init.lean`, `DB__loadFreelist.lean`, `DB__Close.lean`, `fdatasync.lean` | `WriteAt` (init's 4 pages), `ReadAt`, `Close` |
| transactions | `Txn/{RdReg,WInitH,WJoin,WRoll}.lean` | pass `osMeta`/`osSlot` through |

`osBytes` 138×, `OsMeta` 108×, `osMeta` 83×, `m.maps` 76×, `osSlot` 49×, `osFd` 47×; v1-only fields: none
used for crash facts (`w.lost` in `Mmap/RemapLost.lean` is bbolt's own "lost cells", not v1's `lost`).

### Outside bbolt, also on the v1 extension on `origin/lean`

`ManualProof/{os,syscall}.lean`, `ManualProof/golang_org/x/sys/unix.lean`, `Proof/OsFsPrelude.lean`,
`Proof/runtime/Init.lean`, `Proof/os/{PkgInit,Init,Models,ErrorOk,Getpagesize,WriteChunks}.lean`,
`Spec/os/Getpagesize.lean`, `Proof/syscall/*`, `Proof/golang_org/x/sys/unix/*`, `Code/{os,syscall,
go_etcd_io/bbolt,golang_org/x/sys/unix}.toml`, `etc/{gen-init,gen-link,goose,link_bbolt}.py`, and
`interface/` (139 generated files). These are part of the merge (§5).

## 2. v1 → new: the OS layer bbolt uses

Every new statement below is on `fs-bytes` (file:def). Uniform renames everywhere: `d.path` → `d.ino`;
`osMeta p q (some m)` → `osMeta i q m`; `osBytes p off q xs` with `xs : List (w8 × Bool)` → `osBytes i off q
xs` with `xs : List ByteG` (`ByteG = w8 × Cands`, `GooseLang/Ext/Fs/Ghost.lean:44`); `x.2 = true` ("clean")
→ no counterpart (bbolt never uses it); `syncedBytes m xs` → `xs.map (fun x => durB x.1)`.

| v1 (origin/lean) | new (fs-bytes) | change in bbolt's users |
|---|---|---|
| `os.OpenFile.spec` (path, `osMeta path q mo`, `openMeta`) | `Spec/os/OpenFile.lean`: `os.OpenFile.spec` (existing file: `lookupH R V path = some (.file i)`, takes and returns `osTree (own q) R V`, gives `osFd ⟨i,…⟩`; the client already owns `osMeta i`) and `os.OpenFile.specCreate` (`lookupH R V d = some (.dir j)`, `child d b` absent, `osTree (own 1)`, returns `osMeta i 1 newMeta` and `V.push create`) | `Open` splits on the lookup (§3) |
| `os.File.WriteAt.spec` (fraction `q` of the meta if no growth; any `off`, gap filled; D22 clause; `fmtErrorOkOrNil`) | `Spec/os/File__WriteAt.lean`: whole meta (`own 1`), `off ≤ m.size`, `0 < len ≤ 2^30`, post `os.PwOut` / `pwPost` (`Proof/os/Base.lean:38`) | every `WriteAt` user takes the whole `osMeta` (the writer already does: `fileHolds`/`wdbLive` hold it whole); D22 (§2.4); writes past EOF (§2.5); chunked writes (§2.6); `fmtErrorOk` (§5) |
| `os.File.Sync.spec`, `syscall.Fdatasync.spec` (any bytes, even none; failure: `{m with ok := false}`) | `Spec/os/File__Sync.lean`, `Spec/syscall/Fdatasync.lean`: premise `m.Covers lo xs.length` (`GooseLang/Ext/Fs/Specs.lean:533`), success `m.synced` and `durB` bytes, failure: unchanged | §2.3 |
| `os.File.ReadAt.spec` (error: `n = 0`) | `Spec/os/File__ReadAt.lean` (error: any `n`), plus `specRacy` | `Open/PageSize`'s error branch reads `n` only through `err ≠ nil`: check |
| `os.File.Truncate.spec` (grow only, `osGrown`, `MapsBelow`) | `Spec/os/File__Truncate.lean`: cut or grow, bytes `[min, max)` and their cells, post `os.ftDone`/`ftUndone` | `DB.grow`'s proof (`Mmap/Grow*`) restated over `ftDone` |
| `os.File.Stat`, `fileStat.Size`, `File.Fd`, `File.Name`, `File.Close` | same shapes by inode (`Spec/os/*.lean`); `fmtErrorOkOrNil`/`IsPointerError` missing (§5) | rename |
| `unix.Mmap/Munmap/Madvise` | `Spec/golang_org/x/sys/unix/*.lean`: same, by inode, `osMeta i 1 m` | rename |
| `syscall.Flock` | `Spec/syscall/Flock.lean`: unchanged shape | rename |
| `Proof.os.WriteChunks`, `Proof.os.Init/PkgInit/Models/ErrorOk`, `Spec.os.Getpagesize` | **missing on fs-bytes** (added on lean after the fork) | ported in the merge (§5) |
| `Proof.os.CrashFile.osBytes_halves` | `GooseLang/Ext/Fs/World.lean`'s byte-run splitting (`osBytes` append lemmas) | rename |

### 2.3 Syncs without the bytes

bbolt's `fdatasync` (`Spec/go_etcd_io/bbolt/fdatasync.lean`) holds only `osMeta` (v1's sync of zero bytes:
`lo`, `xs = []`), and promises nothing about durability (bbolt's specs are in-process). The new `Fdatasync`
needs `m.Covers lo xs.length`: the bytes of every byte that may not be durable, so that the ghost can
collapse their candidates. Options:

**Carrying the bytes is not possible**, so the byte-less spec is forced. `Covers` is over the interval
`[dlo, dhi)`, which spans committed pages that the store (not the writer) holds, lying between the
transaction's dirty pages. Under `NoSync` no sync runs at all, so the interval grows across transactions.
`DB.grow` calls `File.Sync` too, so both `Fdatasync` and `File.Sync` need it.

**The byte-less spec** (program logic, no trusted change): `{osMeta i 1 m} fsync {osMeta i 1 m'}`. It
needs the state interpretation to relate a resource to the state by a *superset* relation, field by field:

| field | resource vs state |
|---|---|
| a byte's candidates (`osByte i b dq (x, cs)`) | the resource's `cs` contains the state's candidates of `b` (the page-cache value `x` equal) |
| `[dlo, dhi)` (bytes below the size that may not be durable) | the resource's interval contains the state's |
| `[lo, hi)` (crash-size bounds) | the resource's range contains the state's |
| `tc` (candidates known past the size), `zf` (zeros from an offset) | the candidate lists they give for a byte contain the state's |

A sync shrinks the state's lists, so an old resource stays related. The `tc`/`zf` row is the delicate one.
`OsFile.synced` resets every byte's candidates, past the size included (`diskByte`: the page-cache value in
the last page, 0 beyond), and `OsMeta.synced` sets `tc := ∅` and `zf := some (pageUp size)`. Later grows
and extensions build new bytes' candidates from the resource's `m` (`ofResize`, `ofWrite`'s gap), so an old
`tc` must still predict a superset. The byte-less spec therefore returns `m' := { m with tc := ∅ }`, every
other field as in `m`, unless the proof shows that the old `tc` stays sound.

Every crash lemma says "a crash leaves one of the resource's candidates", which stays true of a superset.
Before step 3's other work, prove the `tc`/`zf` part, and check that minibolt's crash proof (P1 uses `valAt`
of the resource's candidates) and walfs's and crashlog's crash proofs survive the relaxation.

### 2.4 D22: the meta write's commit point

`Tx.writeMeta` writes the 4096-byte meta buffer at slot `txid % 2` under `metalock`; the commit point
(`Hcp`) takes the slot's bytes and gets them back "as the write left them", which v1's D22 makes all of
`metaBuf` or nothing whatever `WriteAt` returned (`os.File.WriteAt.spec`'s `off % osPageSize = 0 ∧
data.length ≤ osPageSize → j = 0 ∨ j = data.length`). After a failed commit bbolt keeps running and reads
both metas from the mapping (`db.meta()`), so a torn page-cache meta would have to fail its checksum: an
in-process P1-like premise. The new `PWriteFinish` (`GooseLang/Ext/Fs/Impl.lean:619`) lets a call that
returns an errno land any prefix (`(k = len ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0`).

**Trusted change (replaces D22 entirely), a `PWriteFinish` rule only:** whatever the errno, the landed
prefix is empty, the whole write, or ends on a 4096-byte file-page boundary.

```lean
(k = 0 ∨ k = data.length ∨ (off + k) % 4096 = 0) ∧ (e = 0 → 0 < k)
```

It holds on configuration C, which already fixes the two conditions it rests on:
- **`RLIMIT_FSIZE` unlimited.** With a limit inside a page, the count is cut there, mid-page.
- **A readable source buffer**, which live Go memory always is. An unreadable source page gives `EFAULT`
  after progress, mid-page.

Both contrasts were measured and produced mid-page counts, so both conditions are load-bearing; the rule's
docstring states them.

**Evidence** (the review's Part 2, `notes/axiom-review/bbolt-port-plan-review/{pw/,results.txt}`, on fresh C
filesystems that passed `check.sh`):
- **ENOSPC**, swept over 0–3071 free blocks, aligned and unaligned offsets, a write past EOF:
  - 18 `pwrite`s returned `ENOSPC` with nothing landed.
  - 17 returned a short count, every one ending on a page boundary of the file offset, landing exactly the
    count and nothing beyond.
  - Aligned one-page and 16-page writes landed all or nothing at every free-block count.
- **EFBIG** at `s_maxbytes` (`2^44 - 4096`, page-aligned with 4 KiB blocks): 2 short counts ending at
  `s_maxbytes`, 2 `EFBIG` with nothing landed.
- **Signals**: 155,816 `SIGUSR1` during 3 × 256 MiB writes. Always full: only fatal signals interrupt.
- **Mechanism** (v7.0 `mm/filemap.c:4296-4386`): `written` advances only by whole folios' `write_end`
  status, and a `write_begin` failure stops before any copy into its folio.
  - So a cut ends on a folio boundary, and folios are page-aligned.
  - `generic_write_check_limits` cuts at `s_maxbytes` or `RLIMIT_FSIZE`.
  - A cut inside a folio needs a short copy followed by a stop before the folio finishes: `EFAULT`, a fatal
    signal (the process dies), or a `write_begin` failure on already-reserved blocks.

"Errno lands nothing" is dropped. bbolt doesn't need it: v1's `Tx.writeMeta` proof already handles a meta
page that fully landed while `WriteAt` returned an error (`Tx__writeMeta.lean:96`,
`(j = 0 ∨ j = 4096) ∧ (err = nil → j = 4096)`). It also has kernel exceptions on extending writes
(`ext4_da_do_write_end`, `ext4_write_end` failing after committing). The weaker rule holds even on those
paths, because what lands is a whole folio.

**What follows from it:**
- **One aligned page lands all or nothing** (`k = 0` or `k = 4096`): D22, as a consequence.
- **Mid-call states are invisible in-process.** A mapped load of a byte under a change in flight is stuck,
  and bbolt's readers read the metas under `metalock`, which `writeMeta` holds.
- **Not at a crash or restart.** The rule is about a `PWriteFinish`'s result. A process killed mid-write
  (`fatal_signal_pending`, `filemap.c:4319`, after a short copy) leaves a mid-page prefix in the page
  cache. It is never returned, so it is invisible in-process, but a restarted process sees it. So the rule
  never applies to a change in flight at a crash or restart; that case keeps the general per-byte crash
  rule.

It is an Impl change (the header, `examples/osfs/semantics/data_short_io.go` citing the measurements,
`Tests.lean`), and gets a review round.

**Go's `WriteAt` over it.** Go's loop (`os/file.go:251-260`) retries a short count, and when the retry fails
it returns `(0, err)`, skipping `n += m`, after a page-cut prefix landed. Measured 19 times under ENOSPC and
twice under EFBIG. So:
- **A one-page aligned write** returns the whole page or an error, and on error the page holds all of the
  new data or none of it (`j = 0 ∨ j = 4096`, whatever `err` is).
- **A multi-page write** (data-page runs, `DB.init`'s 4 pages) can return `(0, err)` with any page-cut
  prefix landed. The `WriteAt` spec's error case keeps `j` as any page cut, not 0. The fs-bytes model
  already returns 0 on error.

Side finding: this contradicts `io.WriterAt`'s contract ("returns the number of bytes written"), a Go
standard-library defect recorded nowhere. It goes to `nonissues/` (Go code, not a precondition bbolt
violates).

### 2.5 Writes past the end of the file (`NoGrowSync`)

`Tx.write_ext` exists because under `NoGrowSync` `DB.grow` does not truncate, so dirty pages may lie past the
end and `WriteAt` extends the file with a zero gap. The new `WriteAt` spec requires `off ≤ m.size`; the
semantics allows the gap (`OsChange.ofWrite`'s `lo := min off f.size`). Options: (i) generalize the program
logic's write spec to `off > size` (the gap's bytes announced as zeros: `osBytes` of the gap created) —
proof work only; (ii) exclude `NoGrowSync` from `OptsM.ok` (an API narrowing; etcd sets it only with
`--unsafe-no-fsync`). Recommended: (i), keeping the API.

### 2.6 Chunked writes

fs-bytes's `File.WriteAt.impl` already chunks at `0x40000000`, as Go does (`TrustedCode/os.lean`, the `max`
in the `pwrite` loop), so no trusted-model merge is needed for this. Only the spec's `data.length ≤ 2^30`
premise has to be lifted, a program-logic proof over the chunk loop (lean's `Proof/os/WriteChunks.lean`
is the template). The generalization is needed: bbolt writes up to `maxAllocSize - 1` (2 GiB - 1) per
`WriteAt` (`tx.go`'s write loop).

## 3. bbolt's own specs that change

Exported (`etc/api/bbolt.txt`, `importable`; their `interface/` files are API diffs the user reviews):
`Spec.go_etcd_io.bbolt.Api` (vocabulary: `fileHolds` and its laws), `Open`; and every exported spec's
binder `∀ [HasExt osFsExt]` (§1a's rename: shape only). `DB.Close.spec` does not change: it returns
`True`, giving nothing back, and `isBolt` already hides the path (`Inv/Bolt.lean:116`, `∃ p`). Internal:
`fdatasync`, `Tx__write_ext`, `DB__grow`, `DB__init`, `Tx__writeMeta`.

**The `_kv` specs stay unchanged** (`Open_kv`, `DB__Close_kv`, …). They are over etcd backend's own axiomatic
vocabulary (`backend.fileHolds`, `dbFile`, `Proof/.../storage/backend/InvBbolt.lean:113`), with no OS
resource, and about 25 etcd server files use the path-keyed `backend.fileHolds` (snapshots, `Rename`,
`Cleanup`). Restating them would break those files for no gain. They only need §1a's section-variable
rename.

### `fileHolds` (Api.lean, sealed; `Inv/FileHolds.lean`'s `fileHoldsDef`)

Today: `fileHolds (path : GoString) (D : Data)`, with "no file" as `osMeta path 1 none`. New: the file is
named by the tree, so `fileHolds` speaks of an inode, and "no file" is a lookup the caller states:

```lean
/-- The file of inode `i` holds a database with the data `D`: no mapping, all its page-cache bytes
held, their values an image of `D` (`fileOK`, unchanged). -/
def fileHoldsDef (i : Ino) (D : Data) : IProp GF :=
  iprop(∃ (m : OsMeta) (xs : List ByteG), osMeta i (DFrac.own 1) m ∗ osBytes i 0 (DFrac.own 1) xs ∗
    ⌜m.maps = ∅ ∧ xs.length = m.size ∧ m.size < 2 ^ 62 ∧ fileOK (xs.map Prod.fst) m.size D⌝)

@[no_expose] def fileHolds (i : Ino) (D : Data) : IProp GF := fileHoldsDef i D

/-- What `Open(path)` needs of the file system: the tree, in which `path` is a file holding `D`, or
nothing (then `D = ∅` and `Open` creates it, in `path`'s directory). -/
def pathHolds (R : Roots) (V : Hist) (path : GoString) (D : Data) : IProp GF :=
  iprop((∃ i, ⌜lookupH R V path = some (.file i)⌝ ∗ fileHolds i D) ∨
        (∃ d b j, ⌜path = child d b ∧ NameOk b ∧ lookupH R V d = some (.dir j) ∧
          lookupH R V path = none ∧ D = ∅⌝))
```

`fileHolds_new` becomes `osMeta i 1 newMeta ⊢ fileHolds i ∅` (a created file: size 0, no mapping, no
bytes). `fileOK`, `fileImage`, `flFileOK` are unchanged (pure, over byte values). The `(w8 × Bool)` →
`ByteG` change is invisible outside (`xs.map Prod.fst`).

### `Open.spec`

```lean
abbrev Open.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [ThreadBoundLe GF (2 ^ 29)]
    [ReceiptBoundLe GF (2 ^ 62)] (N : Namespace) (path : GoString) (mode : w32) (opts : Loc)
    (dq : DFrac) (o : OptsM) (D : Data) (R : Roots) (V : Hist),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ ⌜↑N ## ↑osN⌝ ∗
      osTree (DFrac.own 1) R V ∗ pathHolds R V path D ∗
      optsAt opts dq o ∗ ⌜o.ok⌝ ∗ (⌜o.logger = GoInterface.nil⌝ ∨ boltLogger o.logger) }}
    (App (App (App (Val (@! go_etcd_io.bbolt.Open)) (Val #path)) (Val #mode)) (Val #opts))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err); optsAt opts dq o ∗
      (∃ V', osTree (DFrac.own 1) R V' ∗ ⌜V' = V ∨ ∃ e, V' = V.push e⌝) ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (γ : BoltName) (i : Ino),
          ⌜γ.ns = N ∧ lookupH R V' path = some (.file i)⌝ ∗ isBolt db γ ∗ boltState γ 1 D) ∨
       ⌜err ≠ GoInterface.nil⌝) }}
```

The post says where the file is (`lookupH R V' path = some (.file i)`), so a later reopen can find it.

The tree is taken whole only because creating a file needs it (`os.OpenFile.specCreate`). bbolt always
passes `O_CREATE` (`db.go:229`). The tree is returned before `Open` returns (bbolt does no metadata
operation afterwards). Today only `Results` uses `Open.spec`; etcd's backend uses `Open_kv`. A variant for
an existing file over a tree fraction is cheap (`os.OpenFile.spec` takes any `q`) — open question §6.

`OpenFile` fixes the flag to `0x42`, which is fine because `OptsM.ok` excludes `ReadOnly` and a custom
`OpenFile`, as on lean. `PageSize` must stay 4096 in `OptsM.ok` (it does, `Api.lean:43`, `:148`); otherwise a
meta page spans several OS pages and the §2.4 consequence fails.

**Restart caveat.** These are in-process specs. A restart is modelled as a machine crash (the semantics'
restart assumption: a `sync` before the program restarts), and a change in flight at a crash or restart
falls under the per-byte crash rule, not §2.4's rule. So nothing here claims anything across a restart; a
crash theorem for real bbolt would be separate work (§4, §6).

### Internal specs

- `fdatasync.spec`: `osMeta p 1 (some m)` → `osMeta i 1 m`; `osFd fd dq ⟨p, true, true⟩` → `⟨i, true,
  true⟩`; post `∃ m', osMeta i 1 m' ∗ ⌜m'.size = m.size ∧ m'.maps = m.maps⌝` (unchanged), proved over
  §2.3's byte-less sync.
- `Tx.write_ext.spec`: `K.p : GoString` → `K.i : Ino` (the writer's context names the inode),
  `osMeta K.p 1 (some om)` → `osMeta K.i 1 om`, `wrSlotsSz b K.p …` → `wrSlotsSz b K.i …`; the post's size
  facts unchanged; proved over §2.5(i).
- `DB.grow`, `DB.init`, `Tx.writeMeta`, `Tx.write`, `mmap`/`munmap`: the same renames.
  - `writeMeta`'s commit point uses §2.4's consequence (`j = 0 ∨ j = 4096` for the aligned meta page,
    whatever `err` is) in place of D22. v1's proof already has that shape (`Tx__writeMeta.lean:96`).
  - `DB.grow`'s error path must allow either size, since `Truncate`'s failure is "maybe resized"
    (`ftUndone`). `fileOK`'s `hwm·4096 ≤ size` stays true, because the file only grows.
  - `DB__grow.lean:282`'s positional `OsMeta` literal is rewritten with the new fields.
  - Data-page runs and `DB.init`'s 4 pages take `WriteAt`'s error case with any page-cut `j` (§2.4).

## 4. The invariants

bbolt's invariant (`Inv/Store.lean`'s `wdbLive`/`store`, `Inv/WSlots.lean`, `Inv/Locks.lean`) owns, over
v1: the file's whole `osMeta p 1 (some m)` (the writer's side, with `m.maps` the one mapping), the file's
bytes by 4096-byte slot (`osSlot p s bs`), the cells of the mapping (`mcells`), and `osInv`. Nothing in it
mentions crash facts (no `durable`, `dirty`, `lost`), so the new invariant is the old one with the
resources renamed:

```lean
/-- Slot `s` (bytes `[4096 s, 4096 (s+1))`) of the file `i` holds the values `bs`. -/
def osSlot (i : Ino) (s : Nat) (bs : List w8) : IProp GF :=
  iprop(∃ xs : List ByteG, osBytes i (4096 * s) (DFrac.own 1) xs ∗ ⌜xs.map Prod.fst = bs⌝)
```

and, in `wdbLive` and friends, `K.p : GoString` replaced by `K.i : Ino` (the context's file), `osMeta K.p
1 (some m)` by `osMeta K.i 1 m`. What the v1 proof used, and where it now comes from:

| used | v1 | new |
|---|---|---|
| the writer may change the file | whole `osMeta` | whole `osMeta` (also required: one change in flight per file, which the writer's ownership gives) |
| pages' contents | `osSlot` values | `osSlot` values (candidates existential, never read) |
| mapping and cells | `m.maps`, `mcells` | same fields, same cells (`Cells.lean`) |
| no file / empty file | `osMeta p 1 none` | `pathHolds`'s second case at `Open`; nothing afterwards |
| reads racing writes | `ReadAt` with a meta fraction, mapped loads | same; a mapped load of a byte under a change is stuck in both models, and bbolt's readers never load a page being written (meta under `metalock`, data pages from the freelist's free set) |

Candidates are stronger than v1's arbitrary bytes, but bbolt's in-process proof never looks at them, so
they stay existential in `osSlot` and `fileHoldsDef`. No P1. If a crash theorem for real bbolt is wanted
later, minibolt's `BootP1.lean` and crash framework (`Proof/os/CrashSt*`, `cfInv`/`csInv`) are the template,
and the invariant would carry the candidates instead of hiding them.

## 5. Order, mechanics, estimates, risks

**Order** (each step builds before the next; one `lake build` target at a time):

1. *Trusted*: §2.4's `PWriteFinish` rule (Impl, header, `data_short_io.go`, Tests) → review round.
2. *Merge `origin/lean` into `fs-bytes`* (before bbolt, since bbolt's lean files depend on lean's
   post-fork os work):
   - `GooseLang/Ext/OsFs/*`: deleted on fs-bytes, modified on lean (D22, `RLIMIT_FSIZE` text, the
     `netpollinit` note) → keep deleted; carry the text: `RLIMIT_FSIZE` is part of C, the `netpollinit`
     fatal error is covered by the restart assumption (fs-bytes' header already says so), D22 is §2.4.
   - `TrustedCode/{os,syscall}.lean`, `golang_org/x/sys/unix.lean`: both sides changed. Take fs-bytes's
     extension calls (its `WriteAt` already chunks, §2.6) and lean's initializer translation
     (`os-init-lean`), `Stderr`, `arbitraryStrings` and `fmtErrorOk` error models. Manual; then a review
     round of the merged models (they are trusted).
   - `Spec/os`, `Proof/os`, `Spec/syscall`, `Proof/syscall`, `Proof/golang_org/x/sys/unix`: fs-bytes's
     statements, plus lean's `fmtErrorOkOrNil err` / `IsPointerError` conjuncts in every post that has them
     on lean (35+ bbolt files depend on them), plus lean-only modules ported: `Getpagesize`, `Init`,
     `PkgInit`, `Models`, `ErrorOk`. Drop lean's `CrashNarrow`, `CrashWReach` (v1 crash, superseded).
   - `ManualProof/*`, `Proof/OsFsPrelude.lean` (→ an `FsPrelude`), `Proof/runtime/Init.lean`,
     `Code/*.toml`, `etc/*.py`: mechanical.
   - `examples/osfs/*` and their proofs: fs-bytes's (lean's are v1).
3. *Program logic additions*: first the `tc`/`zf` part of §2.3's superset relaxation (the step most likely
   to fail), checked against minibolt's, walfs's and crashlog's crash proofs; then the byte-less
   fsync/`File.Sync` spec, §2.5's writes past EOF, §2.6's lifted `2^30` premise, and the `WriteAt` error
   case with any page-cut `j` (§2.4).
4. *bbolt specs* (§3): `Api.lean`, `Open`, internal specs. Regenerate `interface/`
   (`etc/gen-interface.py etc/api/bbolt.txt`) for review.
5. *bbolt invariants* (§4): `Inv/{Ctx,FileHolds,Store,Locks,WSlots}`.
6. *The 363 section-variable files*: `sed -i -e 's/\[hos : HasExt osFsExt\]/[ExtSemantics fsExt] [FsSemOk]
   [hos : HasExt fsExt]/' -e 's/GooseLang\.Ext\.OsFs\./GooseLang.Ext.Fs./'` plus `open Fs` where
   `osInv`/`osN` are used; the 38 file-name files (§1a') by hand; then a build sweep.
7. *The 62 files*, in dependency order: `Inv/*` → `Mmap/*`, `DB__grow` → `Open/*`, `Open` → `DB__init`,
   `DB__loadFreelist` → `Commit/WriteDefs`, `Commit/Write*`, `Tx__write*` → `Commit/PwMeta`,
   `Tx__writeMeta`, `Commit/Tail*`, `Commit/PubOk`, `Commit/Rollback*`, `Tx__rollback_f` → `Txn/*` →
   `DB__Close` → `Link` (regenerated) → `Results`.
8. Gates: every bbolt target, `etc/tcb-report.py --check`, `etc/api-check.py`, `etc/gen-interface.py
   --check`, `notes/STATUS.md`. Also record the `io.WriterAt` side finding (§2.4) in `nonissues/`.

**Estimates** (relative; the 62 files are 20.5k lines):
- renames (steps 4–6): small per file, but a full build sweep of bbolt (1044 files) is the long pole;
  expect several sweeps.
- `Inv/Store.lean` (2.8k lines): mostly renames; its byte-splitting lemmas (`osBytes_cons'`, slot carving)
  move to `ByteG` unchanged.
- `Open` (path → tree; create branch; `fileHolds` decode): moderate, new logic for the lookup split.
- `Commit/Write*`, `Tx__write*`: moderate (new `PwOut` post in place of `pwBytes` equalities; page-cut
  error case; chunks).
- `Tx__writeMeta`: small once §2.4 is in (v1's proof already has the needed shape).
- the merge's trusted models (step 2): the riskiest non-proof step.

**Risks / unknowns**:
- §2.4's rule must survive review; it is measured on C, and the fallback (an in-process slot premise) is
  not expected to be needed.
- The superset relaxation's `tc`/`zf` part (§2.3) is the likeliest step to fail; if the old `tc` can't be
  kept, the byte-less spec returns `tc := ∅` (already planned).
- Whether bbolt ever needs `off > size` writes other than `write_ext` (grep `pwSize` users).
- lean's post-fork `TrustedCode/os.lean` (initializers, errors) interleaved with fs-bytes's extension
  calls: conflicts are certain; the merged file gets its own review.
- Build memory: bbolt's files are large; one target at a time, `etc/lean-check.py` for the edit loop.

## 6. Open questions for review

1. §3: `Open` takes the whole tree (`osTree (own 1)`) and returns it; keep that, or add an existing-file
   variant over a tree fraction (cheap; today only `Results` uses `Open.spec`)?
2. §2.5: keep (i), generalizing `WriteAt`'s spec to writes past EOF? Under the §2.4 rule the gap case
   behaves like any other (measured: an ENOSPC write past EOF lands nothing, or a page cut with the gap
   zeroed). (ii), narrowing `OptsM.ok`, is cheaper than first thought, because etcd's backend uses the
   `_kv` axioms rather than `Open.spec`.
3. Should real bbolt get a crash theorem now (minibolt's design, P1) or stay Hoare-only? This plan keeps it
   Hoare-only, as on lean.

## 7. Implementation log

**2026-11-12, fork BX (step 3 begun, branch `fs-lean`).**

Done:
- **The byte-less fsync (§2.3), program logic only.** Not the plan's field-by-field superset: a
  *cut*. `OsMeta.cut : Option Nat` (default `none`), and the byte clause of the state
  interpretation (`OsCoh.bytes`, `GooseLang/Ext/Fs/Ghost.lean`) relates a byte resource's
  candidates to the state's by `CandRel (cutOf Γm i)`: `none`, equal (every existing proof's case);
  `some c`, the same candidates stamped after `c`, and every value of the state's among the
  resource's. A byte resource also records that its page-cache value is among its candidates'
  values. `OsCoh.cut_le`: a cut is at most the last change number. `wp_osFsyncB`
  (`GooseLang/Ext/Fs/Specs.lean`): `{osMeta i 1 m} fsync {e = 0 ∗ ∃ c, osMeta i 1 (m.bsynced c) ∨
  e ≠ 0, e ≠ EINTR ∗ osMeta i 1 m}`, `OsMeta.bsynced c := {m with cut := some c, zf := some
  (pageUp m.size), tc := ∅}` (size, maps, crash bounds kept). Why a cut and not a superset: a
  sync replaces each byte's candidates by one stamped 0, which no list relation on the resource's
  candidates alone predicts after later writes; the cut keeps the later candidates equal, so every
  write/resize/finish spec stays exact after it (`CandRel.append`), and the crash lemmas use only
  values (`CandRel.mem`). Stamp-precise reasoning (minibolt's P1) still needs `cut = none`, which
  holds for every file that never had a byte-less sync. Every spec, the crash layer, `Proof/os`,
  crashlog and walfs (three results) rebuilt; no statement of theirs changed. `osMeta_eq` gained the
  `cut` hypothesis.
- **The merge review's fixes** (`notes/axiom-review/fs-lean-merge.md`, dispositions appended).
- **The mechanical step (§5.6)**: `etc/fs-port/bbolt-rename.py`, run over the 1044 files: the
  instance binders, imports, `open Fs`. What still mentions the v1 extension is doc text.
- **Statements, not yet type-checked** (bbolt does not build until the substantive files are
  ported, as before the merge): `fileHolds (i : Ino) D` and `fileHoldsDef` by inode
  (`Inv/FileHolds.lean`), no "no file" case (it is `pathHolds`'s); `pathHolds R V path D`
  (`Spec/go_etcd_io/bbolt/Api.lean`); `fileHolds_new : osMeta i 1 newMeta ⊢ fileHolds i ∅`;
  `Open.spec` over `osTree (own 1) R V ∗ pathHolds R V path D`, returning the tree (`V' = V ∨ V'
  = V.push e`) and, on success, `lookupH R V' path = some (.file i)`; `fdatasync.spec` and
  `Tx.write_ext.spec` by inode; `osSlot` by inode, over `ByteG`.

Deviation from the plan:
- **`BC` keeps the path and gains the inode** (`BC.p : GoString`, `BC.i : Ino`), not `K.p → K.i`:
  the path is also the file's name (`fileOwn f fd p`, `db.path ↦ p`), which the inode does not
  give. Every resource is keyed by `K.i`; `fileOwn` and `db.path` keep `K.p`.

Not done (in order):
1. `WriteAt` past the end of the file (§2.5) and the lifted `2 ^ 30` premise (§2.6, chunks;
   `Proof/os/WriteChunks.lean` over the new extension), with the page-cut error case (§2.4);
   lean's `fmtErrorOkOrNil` on `WriteAt`/`ReadAt`/`OpenFile`; `specRacyLt`.
2. bbolt's invariants beyond `osSlot` and `BC` (`Inv/{Store,Locks,WSlots,Bolt,Tx,Txs}` over
   `K.i`), the 38 file-name files, then the 62 substantive files; `Link`, `Results`; gates.
