# Plan: real bbolt onto the per-byte Linux file extension

**Date:** 2026-11-12. **Status:** plan, for review before any proof is written. **Scope:** the real bbolt
proof of `origin/lean` (`Proof/go_etcd_io/bbolt`, `Spec/go_etcd_io/bbolt`; 812 files), today over the v1
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
- **395 of the 451 OS-touching files are mechanical**: only the section variable `[hos : HasExt osFsExt]`
  (500 occurrences), a few `osN`/`osInv`.
- **4 files** use os specs by name only (linking, initialization, options).
- **52 files (19,008 lines)** hold or pass file resources (`osMeta`, `osBytes`, `osSlot`, `osFd`, `OsMeta`
  fields): the real work, concentrated in `Inv/Store.lean` (2,804 lines), `Open.lean`, `Open/*`, `Mmap/*`,
  `Commit/Write*`, `Tx__write*`, `Tx__writeMeta`, `DB__init`, `fdatasync`.
- **Three things are not mechanical and need a decision first** (§2.4, §6):
  1. *D22*: `Tx.writeMeta`'s commit point needs a one-page meta write to land all or nothing in-process;
     the new semantics lets a failed `pwrite` land any prefix. Proposed fix: a uniform, true-on-C rule for
     a `pwrite`'s returned count (*errno lands nothing; a short count is a page cut*), a trusted change.
  2. *File naming*: v1's `osMeta path none` ("no file here") has no counterpart; `Open` must take the
     directory tree (`osTree`) to look up or create `path`. An API change.
  3. *Durability-free syncs*: bbolt's `fdatasync` spec holds no file bytes; the new `Fdatasync` needs the
     bytes covering every not-yet-durable byte (`Covers`). Proposed fix: a byte-less `fsync` spec in the
     program logic (no trusted change).

## 1. Inventory

### (a) Mechanical: 395 files

Only `variable [hos : HasExt osFsExt]` (and `osN`, `osInv`, `osSlot` 2×) — the readers (`Read/*`), the
writer's tree code (`Write/*`, `Spill/*`, `Rebalance/*`, `Bucket__*`, `Cursor__*`, `node__*`), the
freelist, transactions (`Txn/*` but the four below), stats, `Inv/{Bolt,Ctx,State,Tx,Txs,…}` except §(c).
Edit: `[hos : HasExt osFsExt]` → `[ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]` (the section variables
of fs-bytes' clients, e.g. `Spec/github_com/.../bboltfs/testMinibolt.lean`), `open Fs`, imports
`GooseLang.Ext.OsFs.*` → `GooseLang.Ext.Fs.*`. A `sed` script (§5) does all 395; nothing to review.

### (b) os specs by name only: 4 files

`Proof/go_etcd_io/bbolt/Link.lean` (links the os/syscall/unix proofs), `internal/common/Init.lean`,
`internal/common/Verify.lean` (package initializers), `Spec/go_etcd_io/bbolt/Options.lean`. Regenerated or
mechanical once §2's specs exist (`etc/gen-link.py --bbolt`, `etc/gen-init.py`).

### (c) File resources: 52 files

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

- **(recommended) a byte-less spec in the program logic:** `wp_osFsyncAny`: `{osMeta i 1 m} fsync {osMeta i
  1 m'}`, with `m'` = `m` but the size bounds (`lo`, `hi`) and the durable range unchanged (no knowledge
  gained). It needs the state interpretation to let a byte resource's candidates be a *superset* of the
  state's (a sync shrinks the state's lists; resources keep the old ones). That is sound for every crash
  lemma (each says "a crash leaves one of the resource's candidates"), and changes no trusted file. Check
  that nothing needs candidates to be *exact* (minibolt's P1 proof uses `valAt` of the resource's candidates;
  a superset only weakens what it gets).
- carry the bytes: every caller passes the writer's `W` slots and meta slots. Possible (the writer owns
  them) but touches `Commit`, `grow`, `init`, `writeMeta` for no in-process benefit.

### 2.4 D22: the meta write's commit point

`Tx.writeMeta` writes the 4096-byte meta buffer at slot `txid % 2` under `metalock`; the commit point
(`Hcp`) takes the slot's bytes and gets them back "as the write left them", which v1's D22 makes all of
`metaBuf` or nothing whatever `WriteAt` returned (`os.File.WriteAt.spec`'s `off % osPageSize = 0 ∧
data.length ≤ osPageSize → j = 0 ∨ j = data.length`). After a failed commit bbolt keeps running and reads
both metas from the mapping (`db.meta()`), so a torn page-cache meta would have to fail its checksum: an
in-process P1-like premise. The new `PWriteFinish` (`GooseLang/Ext/Fs/Impl.lean:619`) lets a call that
returns an errno land any prefix (`(k = len ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0`).

**Proposed trusted change (uniform, replaces D22 entirely):** a `pwrite` returns either an errno having
landed nothing, or a count `k > 0` that is the whole length or ends on a 4096-byte file-page boundary:

```lean
((k = data.length ∨ (0 < k ∧ (off + k) % 4096 = 0)) ∧ e = 0) ∨ (k = 0 ∧ e ≠ 0)
```

- *Errno lands nothing* is write(2)'s ABI: "On error, -1 is returned"; a call that wrote something returns
  the count (`generic_perform_write` returns `written ? written : status`). Documented.
- *A short count is a page cut on C*: a buffered write is cut short only between folios (`ENOSPC`/`EDQUOT`
  from `write_begin` of the next folio), by `RLIMIT_FSIZE` (unlimited on C), at `s_maxbytes` (page-aligned
  with 4 KiB blocks, round 4 N2), or if faulting the source back in fails (`EFAULT`, never for live Go
  memory). A copy that stops mid-page because the source was being migrated (round 6, mechanism A) is
  retried within the call after the fault-in, so it is never *returned* (round 6's e2e tears were transient
  states reaching disk, not return values). Reasoned from v7.0 `mm/filemap.c`; to be checked by review and,
  where possible, measured (§6).
- Transient mid-call states are invisible in-process: a mapped load of a byte under a change in flight is
  stuck (the per-byte semantics), and bbolt's readers read the metas under `metalock`, which `writeMeta`
  holds.

With it, a one-page aligned write lands all or nothing (`k = 0` or `k = 4096`), which is D22 as a
consequence, and Go's `WriteAt` loop returns either the whole page or nothing, with the page cache
untouched on error. The new rule is an Impl change (header, `examples/osfs/semantics/data_short_io.go`,
`Tests.lean`), and needs a review round. Alternative without a trusted change: an in-process P1 premise on
steps (a torn page-cache meta slot never validates) — rejected: another client premise, harder to state,
and the rule above is simply true on C.

### 2.5 Writes past the end of the file (`NoGrowSync`)

`Tx.write_ext` exists because under `NoGrowSync` `DB.grow` does not truncate, so dirty pages may lie past the
end and `WriteAt` extends the file with a zero gap. The new `WriteAt` spec requires `off ≤ m.size`; the
semantics allows the gap (`OsChange.ofWrite`'s `lo := min off f.size`). Options: (i) generalize the program
logic's write spec to `off > size` (the gap's bytes announced as zeros: `osBytes` of the gap created) —
proof work only; (ii) exclude `NoGrowSync` from `OptsM.ok` (an API narrowing; etcd sets it only with
`--unsafe-no-fsync`). Recommended: (i), keeping the API.

### 2.6 Chunked writes

lean's `os.File.WriteAt` model (`TrustedCode/os.lean`, after the fork) writes in chunks of at most 1 GiB
(`poll.FD.Pwrite`'s `maxRW`), with `Proof/os/WriteChunks.lean`; fs-bytes's spec instead requires
`data.length ≤ 2^30`. bbolt writes a page run (overflow pages included) in one `WriteAt`, which can exceed
1 GiB for a large value. The merge keeps lean's chunked model (it is what Go does) and ports
`WriteChunks` onto `pwPost`/`PwOut`; the spec drops the `≤ 2^30` premise.

## 3. bbolt's own specs that change

Exported (`etc/api/bbolt.txt`, `importable`; their `interface/` files are API diffs the user reviews):
`Spec.go_etcd_io.bbolt.Api` (vocabulary: `fileHolds` and its laws), `Open`, `DB__Close`; and every
exported spec's binder `∀ [HasExt osFsExt]` (§1a's rename: shape only). Internal: `fdatasync`,
`Tx__write_ext`, `DB__grow`, `DB__init`, `Tx__writeMeta`, the `_kv` backend specs (`Open_kv`,
`DB__Close_kv`: still axioms for etcd's backend, restated the same way).

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
      ((⌜err = GoInterface.nil⌝ ∗ ∃ γ : BoltName, ⌜γ.ns = N⌝ ∗ isBolt db γ ∗ boltState γ 1 D) ∨
       ⌜err ≠ GoInterface.nil⌝) }}
```

The tree is taken whole only because creating a file needs it (`os.OpenFile.specCreate`); it is returned
before `Open` returns (bbolt does no metadata operation afterwards), so a caller (etcd's backend, at
startup) is not blocked from other tree operations while the database is open. If the caller cannot give
the whole tree, a variant for an existing file takes a fraction (`os.OpenFile.spec` accepts any `q`) — open
question §6.

### `DB.Close.spec`

Its post gives back `fileHolds`; with the inode: `… ∗ ∃ i, fileHolds i D` where `i` is the one `Open`
resolved (recorded in `isBolt`'s ghost name: add `γ.ino : Ino`, so the post is `fileHolds γ.ino D`).
`DB.Close_kv` likewise.

### Internal specs

- `fdatasync.spec`: `osMeta p 1 (some m)` → `osMeta i 1 m`; `osFd fd dq ⟨p, true, true⟩` → `⟨i, true,
  true⟩`; post `∃ m', osMeta i 1 m' ∗ ⌜m'.size = m.size ∧ m'.maps = m.maps⌝` (unchanged), proved over
  §2.3's byte-less sync.
- `Tx.write_ext.spec`: `K.p : GoString` → `K.i : Ino` (the writer's context names the inode),
  `osMeta K.p 1 (some om)` → `osMeta K.i 1 om`, `wrSlotsSz b K.p …` → `wrSlotsSz b K.i …`; the post's size
  facts unchanged; proved over §2.5(i).
- `DB.grow`, `DB.init`, `Tx.writeMeta`, `Tx.write`, `mmap`/`munmap`: the same renames; `writeMeta`'s commit
  point uses §2.4's consequence (`j = 0 ∨ j = 4096` for the aligned meta page) in place of D22.

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

1. *Trusted*: §2.4's `PWriteFinish` rule (Impl, header, example, Tests) → review round.
2. *Merge `origin/lean` into `fs-bytes`* (before bbolt, since bbolt's lean files depend on lean's
   post-fork os work):
   - `GooseLang/Ext/OsFs/*`: deleted on fs-bytes, modified on lean (D22, `RLIMIT_FSIZE` text, the
     `netpollinit` note) → keep deleted; carry the text: `RLIMIT_FSIZE` is part of C, the `netpollinit`
     fatal error is covered by the restart assumption (fs-bytes' header already says so), D22 is §2.4.
   - `TrustedCode/{os,syscall}.lean`, `golang_org/x/sys/unix.lean`: both sides changed. Take fs-bytes's
     extension calls and lean's initializer translation (`os-init-lean`), `Stderr`, `arbitraryStrings`,
     `fmtErrorOk` error models, and the chunked `WriteAt` loop. Manual; then a review round of the merged
     models (they are trusted).
   - `Spec/os`, `Proof/os`, `Spec/syscall`, `Proof/syscall`, `Proof/golang_org/x/sys/unix`: fs-bytes's
     statements, plus lean's `fmtErrorOkOrNil err` / `IsPointerError` conjuncts in every post that has them
     on lean (52 bbolt files use `fmtErrorOk`), plus lean-only modules ported: `Getpagesize`, `Init`,
     `PkgInit`, `Models`, `ErrorOk`, `WriteChunks` (onto `PwOut`). Drop lean's `CrashNarrow`,
     `CrashWReach` (v1 crash, superseded).
   - `ManualProof/*`, `Proof/OsFsPrelude.lean` (→ an `FsPrelude`), `Proof/runtime/Init.lean`,
     `Code/*.toml`, `etc/*.py`: mechanical.
   - `examples/osfs/*` and their proofs: fs-bytes's (lean's are v1).
3. *Program logic additions*: §2.3 byte-less fsync (and the superset relaxation), §2.5 writes past EOF,
   §2.6 chunked `WriteAt` spec.
4. *bbolt specs* (§3): `Api.lean`, `Open`, `DB.Close`, internal specs. Regenerate `interface/`
   (`etc/gen-interface.py etc/api/bbolt.txt`) for review.
5. *bbolt invariants* (§4): `Inv/{FileHolds,Store,Locks,WSlots}`.
6. *The 395 mechanical files*: `sed -i -e 's/\[hos : HasExt osFsExt\]/[ExtSemantics fsExt] [FsSemOk] [hos :
   HasExt fsExt]/' -e 's/GooseLang\.Ext\.OsFs\./GooseLang.Ext.Fs./'` plus `open Fs` where `osInv`/`osN` are
   used; then a build sweep.
7. *The 52 files*, in dependency order: `Inv/*` → `Mmap/*`, `DB__grow` → `Open/*`, `Open` → `DB__init`,
   `DB__loadFreelist` → `Commit/Write*`, `Tx__write*` → `Tx__writeMeta`, `Commit/Tail*`, `Commit/Rollback*`,
   `Tx__rollback_f` → `Txn/*` → `DB__Close` → `Link` (regenerated) → `Results`.
8. Gates: every bbolt target, `etc/tcb-report.py --check`, `etc/api-check.py`, `etc/gen-interface.py
   --check`, `notes/STATUS.md`.

**Estimates** (relative; the 52 files are 19k lines):
- mechanical renames (steps 4–6 for most files): small, but a full build sweep of bbolt (812 files) is the
  long pole; expect several sweeps.
- `Inv/Store.lean` (2.8k lines): mostly renames; its byte-splitting lemmas (`osBytes_cons'`, slot carving)
  move to `ByteG` unchanged.
- `Open` (path → tree; create branch; `fileHolds` decode): moderate, new logic for the lookup split.
- `Commit/Write*`, `Tx__write*`: moderate (new `PwOut` post in place of `pwBytes` equalities; chunks).
- `Tx__writeMeta`: small once §2.4 is in.
- the merge's trusted models (step 2): the riskiest non-proof step.

**Risks / unknowns**:
- §2.4's rule must survive review; if it does not, the fallback is an in-process slot premise (P2-like).
- The superset relaxation (§2.3) must not break minibolt's crash proof or crashlog/walfs (they rely on
  exact candidates only through crash lemmas that stay true for supersets — to check).
- Whether bbolt ever needs `off > size` writes other than `write_ext` (grep `pwSize` users).
- lean's post-fork `TrustedCode/os.lean` (initializers, errors, chunking) interleaved with fs-bytes's
  extension calls: conflicts are certain; the merged file gets its own review.
- Build memory: bbolt's files are large; one target at a time, `etc/lean-check.py` for the edit loop.

## 6. Open questions for review

1. §2.4: accept the uniform `PWriteFinish` rule (*errno lands nothing; a short count is a page cut*) in
   place of D22? It is true on C (ABI + reasoning from `generic_perform_write`); a measurement would count
   short returns of aligned page writes under compaction and `ENOSPC`.
2. §3: `Open` takes the whole tree (`osTree (own 1)`) and returns it; acceptable for etcd's backend, or do we
   want an existing-file variant over a tree fraction?
3. §3: record the inode in `BoltName` (`γ.ino`) so `DB.Close` returns `fileHolds γ.ino D`?
4. §2.3: byte-less fsync via a superset relaxation of byte resources (program logic only) — or thread the
   bytes through bbolt's sync callers?
5. §2.5: generalize `WriteAt`'s spec to writes past EOF (keep `NoGrowSync`) — or narrow `OptsM.ok`?
6. Should real bbolt get a crash theorem now (minibolt's design, P1) or stay Hoare-only? This plan keeps it
   Hoare-only, as on lean.
