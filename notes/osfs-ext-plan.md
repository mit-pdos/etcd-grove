# Plan: a Linux file extension (files, fsync, read-only mmap) for bbolt

**Date:** 2026-10-31. **Status:** design agreed in outline; decisions D1–D8 below take the
recommended option until the user says otherwise. **Perennial pin:** `d62b13ac1`.

The extension is this repository's (`GooseLang/Ext/OsFs/`), not Perennial's, and is named
`"os"`. This repository translates `os`, `syscall`, `io/fs` and `golang.org/x/sys/unix` itself,
for project `bboltfs` of `etc/goose.py` (lean roots `os=`, ...), instead of using Perennial's
`os`. Their `.toml`s trust exactly the calls bbolt makes, modelled in `TrustedCode/` in terms of
the extension, so the bbolt fork can call `os` directly. Lean refuses a module that imports
both this `os` and Perennial's (raft's translation still uses Perennial's), so moving every
project to `os=` is the step after.

## Environment assumptions (hypotheses of the adequacy statement)

The files the program may open are a fixed set of paths (the domain of the state's `files`).
These paths name distinct regular files on a local ext4 or xfs filesystem. No other process
touches them. The device honours cache flushes, writes each sector atomically, and has no media
errors. Opening any other path is stuck. Path
resolution is not modelled.

## State

```lean
structure File where
  cur      : List w8   -- what pread, fstat and the mappings see; size = cur.length
  durable  : List w8   -- the image known to be on disk
  dirty    : GSet Nat  -- offsets whose durable byte may differ from cur
  sizeLo sizeHi : Nat  -- smallest/largest size since the last successful sync
  lost     : Nat → Bool -- offsets whose writeback a failed sync lost (D2)
  named    : Bool      -- the directory entry is durable (false if created since boot, D4)

structure OsState where
  files    : GMap GoString (Option File)               -- allowed paths; none = absent
  fds      : GMap w64 (GoString × Bool × Bool)         -- fd ↦ (path, readable, writable)
  inflight : GMap w64 (GoString × Nat × List w8)       -- pwrites in progress (token ↦ ...)
  maps     : GMap Loc (GoString × Nat)                 -- base ↦ (path, length)
```

- A path is a file's identity: there is no rename, link or unlink. A mapping refers to the path,
  so it outlives `Close` of its fd, as on Linux.
- Fds are real fd numbers. Open picks any number not in `fds`. The kernel's choice always
  qualifies, because the model's table is a subset of the real one. Calls through a forged or
  closed fd are stuck.

## Primitives

Each returns an errno as well (0 = success). Any operation may instead fail with an arbitrary
errno and no effect (environmental failure: EIO, ENOSPC, EMFILE, EACCES). Misuse is stuck (D6):
a wrong access mode, a bad fd, or an unsupported flag.

| op | needs (else stuck) | effect |
|---|---|---|
| `Open(path, flags)` | path allowed; flags ⊆ {RDONLY, WRONLY, RDWR, CREAT, TRUNC, CLOEXEC} | absent, no CREAT: ENOENT. Absent, CREAT: create (`named := false`). TRUNC: size 0. Fresh fd. |
| `PRead(fd, off, n)` | fd readable, off ≥ 0 | `cur[off, min(off+n, size))`; a byte under an in-flight change is arbitrary, and while a change resizes the file the length is that of a size `Fstat` could see then (`ReadSees`). On failure, a prefix of that with an errno. |
| `PWriteStart(fd, off, data)` | fd writable; affected range misses the other in-flight writes | records the write, returns a token |
| `PWriteFinish(tok)` | – | writes a prefix of length k (k = len on success), marks it dirty |
| `Fstat(fd)` | – | `cur.length`, or while a change resizes the file, a size between it and the change's target (`StatSees`, D8) |
| `FtruncateStart(fd, sz)` / `FtruncateFinish(tok)` | fd writable; no other change in flight on the file | resize, zero-fill; dirty from `min(old, new)` to `max(old, new)`. Two steps, like pwrite: a pread racing a shrink can stop anywhere between the sizes on Linux. While in flight, it affects every byte from `min(size, sz)` on. |
| `Fsync(fd)` | – | success: `durable[i] := cur[i]` for dirty i outside in-flight changes (they stop being lost); size durable. Failure: those bytes become *lost* and clean (D2) |
| `Close(fd)` | fd open | removes the fd; errno arbitrary (the fd is freed either way) |
| `Mmap(fd, off, len, prot, flags)` | off = 0, prot = PROT_READ, flags ∈ {SHARED, SHARED\|POPULATE}, fd readable, len > 0, no in-flight write on the file | fresh page-aligned (4096) range of `len` cells, or an errno |
| `Munmap(base, len, cap)` | `base` a mapping, `len = cap` = its length | removes the mapping and its cells |

- **Affected range** of a write of n bytes at `off`: `[min(off, size), off+n)`. It includes the
  zero gap that an extending write creates. A truncate affects every byte from `min(size, sz)`
  on. A mapped load that could see a partial change is stuck (a hole). A racing `pread` or
  `fstat` instead returns any mix. bbolt's `WriteTo` copies pages that a concurrent writer may
  be rewriting, so its read must not be stuck.
- **Edge cases.**
  - A zero-length write changes nothing, even past EOF (Go makes no system call). A partial
    write of k bytes at `off` past EOF leaves the size at `off + k`.
  - Negative offsets are stuck in the primitives. The models return Go's error first, without a
    system call (`ReadAt`/`WriteAt`), or pass the call through to an EINVAL (`Truncate`).
  - `O_TRUNC` truncates whatever the access mode, as Linux does, and marks the file as
    `Ftruncate` does.
- **Two-step pwrite.** An atomic pwrite would be more defined than Linux, because a concurrent
  `LoadBytes 8` or `pread` can tear. With a start and a finish step, any real overlap in time
  maps to a model interleaving that is stuck.
- **One heap rule.** Every step ends with `h' := render st' (h minus the cells of st.maps)`.
  `render` sets mapping cell i to the byte `cur[i]`, or to `LitV LitPoison` (a *hole*, never a byte) when i is past EOF
  or under an in-flight change. A new cell is an ordinary byte cell (`Free`). A hole makes every
  load stuck (SIGBUS, or a race). A store to a mapped byte succeeds until the next render: on
  Linux it is fatal (see "Mappings are not read-only in the model"). No operation spells out
  its own heap update.
- **The extension never touches user buffers.** The trusted models marshal them with ordinary
  Go: `WriteAt(b, off)` passes `string(b)`, and `ReadAt` `copy`s the returned data into `b`.

## Crash

`fds`, `inflight` and `maps` are dropped (the heap is arbitrary after a crash). Each file
becomes an image, which is then both `cur` and `durable`:

- **Existence.** If `¬named`, the file may vanish (D4).
- **Size.** Any size between `min(sizeLo, in-flight targets)` and `max(sizeHi, in-flight
  targets)`.
- **Bytes.** Byte i is `durable[i]` unless i is dirty, lost, under an in-flight change, or `≥
  durable.length`. In those cases it is arbitrary (D1).
- **Afterwards.** A file the crash keeps is named, and all of it is durable.

## Trusted Go models

- `*File` mirrors Go's `File{*file}`: a cell holding a pointer to an inner cell holding
  `(fd, name)`.
  - `Close` sets the fd to -1, so copies of the struct share that state, as in Go.
  - `Fd()` is a load (a closed file gives `^uintptr(0)`).
  - `Name()` is the exact name.
- `Stat()` returns a value holding the size, and `Size()` reads it.
- `Sync` and `Fdatasync` are both `Fsync` (D3).
- Errors are `&PathError{op, name, Errno(e)}`. A short `ReadAt` returns `io.EOF`.
- Trivial ones:
  - `Flock` is the extension's `Flock`: any errno, stuck on an fd not open (D7).
  - `Madvise`, `Mlock` and `Munlock` return nil or an arbitrary Errno.
  - `SameFile` and `Getenv` are arbitrary.
  - `Getpagesize` is 4096.
  - `Exit` is `AngelicExit`.
  - `Stderr.Write` returns some `(n, err)`.

## Mappings are not read-only in the model (2026-10-31)

A store or CAS on a mapped byte succeeds in the model: mapped cells are ordinary byte cells
(`Free`), and the next extension step renders the file over them. The first design made them
read-only with a phantom reader (`Reading 1`). That relied on Perennial's failing byte CAS
(`CmpXchgBytesFailS`) refusing cells with readers, which it does not. The user did not want a
core-semantics change shaped by this extension.

Read-only-ness needs no model because violating it is fatal on Linux. A store, or any `LOCK
CMPXCHG`, on a `PROT_READ` page is a SIGSEGV, and Go's runtime makes that a fatal error
(`unexpected fault address`), not a panic. The model then only has to contain the run up to
the fault, as for out-of-memory (`AllocOOMS`):
- plain adequacy claims nothing of a run that dies;
- crash adequacy covers the restart, because a process death is a crash at that step. Unlike
  a machine crash, the kernel survives the process, so the files end up with the page cache's
  contents. Those contents are always one of the crash images the model allows.

The condition is that the fault stays fatal. `runtime/debug.SetPanicOnFault(true)` would make
it a recoverable panic, and Perennial does not model `runtime/debug`.

Holes stay. A load past EOF, or racing an in-flight change, is stuck, because a byte load needs
a byte.

## Decisions (recommended option first; taken until the user says otherwise)

- **D1:** unsynced bytes are arbitrary after a crash (vs old-or-written). Either way, bbolt's
  torn-meta argument needs a no-checksum-collision premise.
- **D2 (changed 2026-10-31):** a failed fsync marks the dirty bytes *lost*: arbitrary at a
  crash until written again and synced. Linux marks failed pages clean, so a later successful
  sync does not redo them. The first choice, a poisoned bit making the whole file arbitrary,
  made every crash property unprovable once a sync can fail: `examples/bboltfs`'s minibolt
  needed a premise "no fsync fails".
- **Fsync never fails with EINTR (2026-11-01).** `fsync(2)` on a local ext4 or xfs file does not
  return EINTR, and Go's `File.Sync` retries it. With EINTR allowed, a successful `Sync` could
  hide a failed attempt that lost the dirty bytes (D2), so no crash proof could rely on a sync.
- **D3:** `Fdatasync` = `Sync`: both flush contents and size. Linux flushes `i_size` in
  fdatasync. bbolt's `init` grows an empty file by `WriteAt`, then calls `fdatasync`.
- **D4:** a created file is not durably named until a crash survives it (no dir fsync
  primitive).
- **D5:** known gap: Go's finalizer closes an unreachable unclosed file's fd, the model never
  does, so the model cannot return that number again. Observable only by comparing stored fd
  integers.
- **D6:** misuse is stuck, not an errno.
- **D7:** `Flock` is trivial (single-process spec).
- **D8 (changed 2026-10-31):** a `Stat` or `pread` racing a change returns a nondeterministic
  answer instead of being stuck. Only mapped loads are stuck on a race.

## Tests of the trusted definitions

`GooseLang/Ext/OsFs/Tests.lean` holds lemmas about the step and crash relations:
- misuse is stuck: a closed fd, a read-only fd, a disallowed path or flag, a writable mapping,
  a partial munmap;
- mapped cells: the file's byte, a hole past EOF and under an in-flight change, and a hole is
  never a byte;
- reads and `fstat`: exact with nothing in flight, and a racing read may see any byte the
  change may write;
- crashes: after a successful sync, a crash leaves the file with exactly the contents the page
  cache had at the sync, since the sync wrote them to disk; after an unsynced
  write, it may keep the old byte or the new one; a byte lost by a failed sync stays lost
  across a later successful sync.

Writing them surfaced the invariant the program logic must carry: a clean byte's durable copy
is its page-cache copy (`crash_after_sync`'s premise). The operations maintain it, because
every change marks what it changes as dirty, but the trusted file does not state it.

## Work

1. `GooseLang/Ext/OsFs/Impl.lean`: state, `render`, step, crash.
2. The `os`/`syscall`/`unix` translation, its trusted models (`TrustedCode/...`) and `.toml`s (done, `dc1e2a2999`).
3. Test programs: `examples/bboltfs` (targets, stuck probes, unprovable probes, a minibolt).
4. `Specs.lean` (untrusted): mapped cells use the ordinary byte points-to; per-byte file ghost state
   that owns the mapped cells; the durable/dirty ghost state; `ExtCrashInterp`.
5. Adequacy with the environment assumptions as premises.
6. minibolt's proofs (`Proof/github_com/mit_pdos/etcd_grove/examples/bboltfs/`, linked by
   `etc/gen-link.py --bboltfs`), as of 2026-11-01: every function of `page.go` and `minibolt.go`
   (`Open`, `init`, `mmap`, `munmap`, `meta`, `readPageSize`, `Get`, `Snapshot`, `commit`,
   `Commit`, `Close`, `close`, `flock`, the page helpers) and the two non-crash programs,
   `testMinibolt` and `testMiniboltConcurrent` (`{{ pkgFacts ∗ envFacts ∗ osInv ∗ osMeta
   (dir ++ "/db") 1 none }} f(dir) {{ RET #true }}`), with no `sorryAx`. The representation and
   lock invariants are `DB.lean`; readers borrow mapped cells from the mapping invariant
   (`MapLoan.lean`), since a Go load is a sequence of non-atomic byte reads. Every result takes
   the hand-written `os.file`/`os.fileStat` field assumptions (`TrustedCode/os.lean`) as
   hypotheses. Not done: a closed theorem through `osFs_adequacy` (it must establish `pkgFacts`
   and `envFacts` from package initialization), and `BootMinibolt`'s crash safety
   (`BootCrashSafety` is stated, with P1 as a strengthened crash relation and the machinery in
   `CrashP1.lean`/`SemCongr.lean`; the specs are Hoare triples that keep the file's resources in
   lock resources, so no generation's proof can hand them to the crash interpretation; that
   needs logically atomic `os` specs and a crash invariant).

### Program logic, as of 2026-11-01 (branch `osfs-specs`)

Extension-level specs (`GooseLang/Ext/OsFs/Specs.lean`, `Write.lean`, `Truncate.lean`): `Close`,
`Flock`, `Fstat`, `PRead` (exact and racing), `Fsync`, `Mmap` (with the mapping's bounds),
`Munmap`, `Open` without `O_TRUNC`, `PWriteStart`/`PWriteFinish` (and the facts a retried write
needs: `pwBytes_retry`, `mcellsAny_split`/`_merge`), `FtruncateStart`/`FtruncateFinish` for a
growing truncate (`Truncate.lean`; the first step takes the client's halves of every mapped cell
past the size, up to `hi`, since a truncate in flight affects every byte from the size on; a
failed truncate that left the file unchanged gives back `ftMeta m sz`, the crash bound widened,
as a failed write gives back `pwMeta`), and the racing `PRead` over a list of held ranges
(`wp_osPRead_racy_list`). Each is named `wp_os<Op>` (`wp_osClose`, ...), clear of Perennial's
channel `wp_Close`. Not yet: a shrinking truncate, `Open` with `O_TRUNC`.

Go-level specs (`Spec/`, proved in `Proof/`): `syscall.Fdatasync`, `syscall.Flock`, `unix.Mmap`,
`unix.Munmap`, `unix.Madvise`, `os.OpenFile` (`O_RDWR|O_CREATE`), `(*os.File).Fd`, `Name`, `Stat`
with `fileStat.Size`, `Sync`, `Close`, `WriteAt` (offset ≥ 0, `0 < len(b) ≤ maxRW`; EINTR
retries), `ReadAt` (exact: inside the file, `len(b) ≤ maxRW`; and racing, `File.ReadAt.specRacy`,
which needs the read to end below `2^63`), `Truncate` (growing). An open file is `os.ownFile`
(`Proof/os/Base.lean`), field by field.

`os.file` and `os.fileStat` are trusted types, for which goose emits no field get/set facts;
`TrustedCode/os.lean` states them by hand (`file.FieldAssumptions`, `fileStat.FieldAssumptions`,
in goose's form), a trust-base item. `OpenFile` and `Stat` take them as instance hypotheses.

### Crash proofs: a premise on crashes, and what they need of specs (2026-11-01, branch `osfs-boot`)

- **A premise `Q` on crashes** (`GooseLang/Ext/OsFs/CrashP1.lean`, proved): a program is closed
  with `osFsSemWith Q` (step `OsStep`, crash `OsCrash ∧ Q`), so the end-to-end statement shows
  `Q`. The specs are proved for `osFs_semantics` and are reused as they are: the WP depends on
  the semantics only through the extensions' steps (`SemCongr.lean`, `wp_sem_congr`, generic,
  a candidate for Perennial). `osFsQ_crash_adequacy` takes each generation's proof in
  `osFs_semantics`'s terms; after a crash `crashRestQ Q` gives the files and, by
  `osCrashQ_take`, the crashed state `st` (coherent with the old ghost maps) and `Q st st'`.
  `HasExt.sem_eq` (Perennial) asks for the whole `ExtSemantics`, though only its step is used
  (`HasExt.step_iff`); weakening it to the step would make `wp_sem_congr` unnecessary.
- **minibolt's P1** (`Proof/.../bboltfs/BootP1.lean`): a valid meta slot of the crash image is
  the slot's durable bytes, or its page-cache bytes if all 64 are dirty or lost, or what a
  write in flight leaves. The "dirty or lost" condition excludes a page-cache mix left by a
  failed `pwrite` (its untouched bytes stay clean), which validates only by a collision.
  `BootCrashSafety dir` is the statement of `BootMinibolt`'s crash safety (a `def`).
- **The gap: crash-aware specs.** There is no crash WP: what the crash part of a generation's
  proof uses must be in an invariant at every step, and `osCrash_take` needs the old
  generation's `osMeta p` (some fraction) and the bytes it reads. minibolt's specs (`Open`,
  `Commit`, `Close`, `init`) and the `os` wrappers' (`File.Sync`, `WriteAt`, `Truncate`, ...)
  take the whole `OsMeta` and the bytes as Hoare triples, and `DB.lean` keeps them in lock
  resources (`rwlock` holds the whole `OsMeta`), so at a crash in the middle of a call nothing
  can be handed to `osCrash_take`. `Open`'s error case also drops the bytes. A crash proof
  needs the database file's `OsMeta` fraction and meta-page bytes in an invariant across every
  step (logically atomic specs of the `os` wrappers, the extension's operations being single
  steps), and minibolt's proofs redone over it.

### Crash-aware specs and the first end-to-end crash proof (2026-11-01, branch `osfs-crashex`)

`examples/crashlog` (project `crashlog`): a flag byte at offset 8 guarding 8 bytes of data at 0,
proved crash-safe end to end (`Proof/.../examples/crashlog/Results.lean`, `crash_safety`, no
`sorryAx`). The flag is after the data: the first write to an empty file extends it over offset 0,
and an unsynced extended byte is arbitrary after a crash (D1), so a flag at 0 could read nonzero
with no data.

- **The crash interpretation keeps the changes in flight** (`GooseLang/Ext/OsFs/CrashTok.lean`,
  `os_crash_interpT`, `osFs_crash_adequacyT`). A `pwrite` past the end (or a truncate) holds the
  file's whole `OsMeta` in `tokRes`, which `os_crash_interp` drops, so no invariant could take
  such a file at a crash. `crashRestT` keeps the old map of changes; `osCrashT_take_tok_keep`
  takes the file with the token's fragment. The `_keep` lemmas give the old resources back, so
  that the crash part closes the invariant it opened.
- **Crash-aware specs take an invariant** (`Proof/os/CrashFile.lean`, `CrashOps.lean`,
  `Spec/os/Crash.lean`): `cfInv N p γ Good` holds the file's state (`CFile`: absent, idle, or a
  `pwrite` in flight with its token), half of its resources and `CrashOk Good s` (every file a
  crash may leave of `s` is `Good`); the caller holds the other half (`cfOwn`), so it reads with
  the existing Hoare specs (`ReadAt`, `Stat` need only fractions). `OpenFile.specCrash`,
  `File.WriteAt.specCrash`, `syscall.Fdatasync.specCrash` open it around each of the extension's
  steps (atomic: `osOp_atomic`). A write's caller shows `CrashOk` of the first attempt in flight
  only; every later state, retries included, is a narrowing (`Proof/os/CrashNarrow.lean`).
  Chosen over atomic updates because the wrappers loop with two steps per attempt, and the
  states between them are the extension's, not the caller's: one predicate of crash images
  (`Good`) covers them all, and the lock-protected state of minibolt fits the same shape (the
  lock holds `cfOwn`). Not covered yet: mappings (`CfWf` asks for none), truncate, fractional
  `OsMeta` for concurrent readers.
- **Not proved:** the package initializer. `crash_safety` takes `Hinit_wp` (the package's
  `initialize'` runs from `ownGoState ∅`); `etc/gen-init.py` does not generate `wp_initialize'`
  for this repository's `os`/`syscall`/`io/fs`.

### minibolt's crash proof, round 1 (2026-11-01, branch `osfs-mbcrash`)

Done (no `sorryAx`):
- `GooseLang/Ext/OsFs/CrashQT.lean`: the crash interpretation under a premise `Q` that keeps the
  changes in flight (`crashRestQT`, `os_crash_interpQT`, `osFsQ_crash_adequacyT`), and the take
  lemmas `osCrashQT_take_runs_keep`/`osCrashQT_take_tok_keep`, which return `FileCrashedR` and the
  crash's facts `CrashSeenR` (crashed state `st`, `OsCoh` with the old maps, `OsCrash`, `Q`, the
  file in `st'`, the runs' bytes and the tokens in `Γt`).
- `Proof/os/CrashFileQ.lean`: `CrashOkQ Q p Good s` (`CrashOk` with `CrashSeenR` as a further
  hypothesis; `crashOk_Q`), `cfInvQ`, `cfInvQ_alloc`, `cfInvQ_crash_keep`.
- `Proof/.../bboltfs/CrashGood.lean`: minibolt's `Good` (`goodImg`: at most 1 GiB, and short with
  no valid meta in a slot held whole, or four pages with neither meta valid, or committed:
  `metaPagesOk`, high water mark inside, `bootOk` of the current root page), with
  `goodImg_fileOk` (`Open`'s `dbFresh`) and `goodImg_freshTx` (`BootMinibolt`'s first check).

**Finding 1: `BootCrashSafety` is false for the current `init`.** A crash during the first `init`'s
first `WriteAt` (pages 2–3 at offset 8192 of the new, empty file) may leave a file of 79 bytes,
all arbitrary (D1; P1 says nothing of a slot the image does not hold whole). The next boot finds a
short file and redoes `init`, whose first `WriteAt` zero-fills `[79, 8192)`: slot 0 is then the 63
old bytes and a zero, which validates if the 79 bytes were chosen so. Example (txid 59, root 3,
pgid 4; FNV-64a's top byte is 0, so the zero completes the checksum):
`00000000000000000000000000000000edda0ced02000000001000000000000003000000000000000000000000000000020000000000000004000000000000003b00000000000000b5c02b352ffed3`.
After the `Fdatasync`, a crash leaves that valid meta durable; the third boot's `Open` takes it
(`readPageSize` validates it), and `Get` finds page 3 (`init`'s root page, `count` 0) under txid
59: `BootMinibolt` panics. It is a checksum collision on garbage, not on a torn meta, so P1 does
not exclude it. Proposed fix (a change to `examples/bboltfs/minibolt.go`, for the user): `init`'s
first `WriteAt` writes all four pages from offset 0 with pages 0–1 zero, then `Fdatasync`, then the
metas, then `Fdatasync`. A torn first write then leaves every slot dirty, and P1 makes a valid one
the durable slot (one `goodImg` already had invalid) or zeros. (Alternative: `Truncate(0)` before
`init`, which needs a shrinking-truncate spec.) `goodImg` is written for the fixed `init`.

**Finding 2: the ghost state does not know the durable bytes, which P1 needs.** P1's first case is
"the slot is the durable one" (`f.durable`). The ghost state knows `durable[i] = cur[i]` only for a
clean byte (`OsCoh.bytes`, `CleanPhys`); once a write makes a byte dirty, nothing ties its durable
copy to anything. Commit's meta write over slot `(T+1) % 2` needs "the durable slot is meta `T-1`"
(it was clean before the write), and the fixed `init`'s writes need "the durable slots are the old
ones (invalid)" and "zeros". No `Good` avoids it: the old durable slot validates. Proposed ghost
change (untrusted, `GooseLang/Ext/OsFs/Ghost.lean`): a field `dur : List (Option w8)` of `OsMeta`,
the durable bytes known, with `MetaOk.dur : dur[i]? = some (some d) → f.durable[i]? = some d`.
Durable bytes change only at a successful sync (which takes the whole `OsMeta`) and at a crash, so
every other step keeps `dur`; `OsMeta.synced` resets it to what the sync makes durable (the given
bytes, when `m.ok`); `initMeta f` sets it to `f.cur`; `newMeta` to `[]`. `CrashSeenR` then gives the
durable slot through `OsCoh.meta_some`. It touches the `MetaOk` constructions (`Facts.lean`,
`Specs.lean`), `wp_osFsync`, and everything that builds an `OsMeta` anonymously.

`CrashOk` obligations of `BootMinibolt` (with the fixed `init`), all open; "P1+dur" marks those
needing finding 2:
1. `OpenFile` of an absent path: created, empty (`openState none`): short.
2. `init` W1 (four pages at 0, pages 0–1 zero), in flight and after, failed or retried: P1+dur
   (old slots invalid by `goodImg`, or not held whole).
3. `init` S1 (`Fdatasync`), and its failure (bytes lost: arbitrary, P1's dirty-or-lost case).
4. `init` W2 (the metas at 0): P1+dur (durable slots zero; the page cache's or the write's are
   `init`'s metas, txids 0 and 1, root 3, whose page is synced with `count` 0).
5. `init` S2.
6. Commit's `Truncate` (growth) and `Sync`: the metas and committed pages are below the old size.
7. Commit's data page `WriteAt` (page `pgid`, past every committed page) and `Fdatasync`.
8. Commit's meta `WriteAt` (slot `(T+1) % 2`) and `Fdatasync`: P1+dur (slot is meta `T-1`, durable,
   or meta `T+1`, whose root page `pgid` is synced; `curMeta` picks the right one even if the slot
   is invalid with any txid field).
9. Failure paths (a failed sync's lost bytes; a partial write's mixed slot is excluded from P1's
   page-cache case by its clean bytes).

Next round: get the user's decision on both findings; then (a) fix `init` and regenerate the
translation; (b) add `OsMeta.dur`; (c) prove the obligations above as pure lemmas over
`CrashSeenR`/P1 (`CrashOkQ (P1 p) p Good`); (d) the crash-aware specs of `Spec/os/Crash.lean` for
`cfInvQ` (generalize `CrashOps.lean` over the invariant's predicate; `crashOk_narrow` over
`CrashOkQ`, where a retry is a new token with the rest of the data), plus `Truncate` (growth),
`File.Sync` (= `Fdatasync`), and `Mmap`/`Munmap` with mappings (`CfWf` asks for none); `ReadAt`,
`Stat` and `Close` need no crash-aware spec (fractions or no file resource); (e) rework `rwR` to
hold `cfOwn` with `cfInvQ` as the invariant, and re-prove `Open`, `init`, `commit`, `Close`.

### minibolt's crash proof, round 2 (2026-11-01, branch `osfs-mbcrash`)

Done (no `sorryAx`; `DB.init.wp_proof` has only goose's usual opaque-type axioms):
- **`init` fixed** (`9a01d8a154`, the user's) and **`DB.init`'s proof redone** (`DB__init.lean`):
  `buf` from `initPages`, `first` zero with `buf`'s last two pages copied in (`wp_slice_copy`),
  `WriteAt(first, 0)`, `Fdatasync`, `WriteAt(buf[:8192], 0)`, `Fdatasync`. Same spec, except that
  the post's `OsMeta` now says the bytes are durable (`dur := durOf 0 (initFile xs)`); `Open`
  and `stored_of_init` follow. Proof note: `iframe` on the `wp_slice_copy` precondition made the
  kernel hit "deep recursion" (a `List.replicate 16384` unfolded); `isplitl`/`iexact` does not.
- **`OsMeta.dur : List (Option w8)`** (`Ghost.lean`), the durable bytes known, with
  `MetaOk.dur : m.dur[i]? = some (some d) → f.durable[i]? = some d`. Only a successful sync changes
  the durable image; **`OsMeta.synced m lo xs`** (now taking the synced bytes) sets
  `dur := if m.ok then durOf lo xs else []` (`durOf lo xs = replicate lo none ++ xs.map (some ∘ fst)`,
  `durOf_some`); every other step keeps `dur` (`osCoh_addTok`'s and `osCoh_setMaps`' hypotheses
  have `om.dur = m.dur` / `m'.dur = m.dur`). `initMeta f` knows all of the file
  (`dur := f.cur.map some`), `newMeta` nothing. `wp_osFsync`, `syscall.Fdatasync.spec`,
  `os.File.Sync.spec` post `m.synced lo xs`; minibolt's (`DB__commit`), crashlog's (`Boot`) and
  `CrashOps`/`Spec/os/Crash.lean` follow (`m.synced 0 bs`).
- **`CrashSeenR` knows the other changes in flight on the file** (`CrashQT.lean`): each is one of
  `ts` or takes a fraction of the `OsMeta` (`ti.q ≠ 1`) and none of the runs' bytes
  (`tokRes_runs_disj`: a token holds its bytes whole). `crashRestQT` gained
  `∀ t ti, Γt !! t = some ti → ti.c.path ∉ D → Γt' !! t = some ti` (tokens of files not yet taken
  are still there). Without this, a foreign write in flight would make P1's third case arbitrary.
- **`Proof/.../bboltfs/CrashOk.lean`**: the obligations reduced to pure statements on images.
  - `seen_file` (idle, runs `[(0, dq, bs)]`, `bs` whole) and `seen_writing` (the write's state):
    the crashed file `f` has `f.cur = bs.map fst`, `f.durable` agrees with `m.dur` and the clean
    bytes (outside the write's range), and the only change in flight on it is the client's write
    (idle: others write `[]`).
  - **`crashOkQ_idle`**: `CrashOkQ (P1 p) p Good (some (m, bs, none))` from
    `∀ img D, idleImg m bs img D → goodImg img`; **`crashOkQ_writing`**: the same for
    `some (m, bs, some (t, off, data))` from `writingImg m bs off data img D`. `idleImg`/`writingImg`:
    size bounds, the clean bytes, `D` (the durable image) agreeing with `m.dur` and the clean bytes,
    and each valid slot of `img` (held whole) is `D`'s, `bs`'s, or (writing) `writeBytes bs off data`'s.
  - **`crashOkQ_create`** (obligation 1) proved.

**Gap found: commit's data-page sync forgets the metas' durable bytes.** Commit syncs the data page
alone (`Fdatasync` with `(4096 * hwm, ys)`), which resets `dur` to that page; the meta write that
follows needs the durable slot `(T+1) % 2` (meta `T-1`, recorded by the previous commit's meta sync
`(0, X)`). Fix (untrusted, `Specs.lean`): a sync that also records other bytes the caller shows clean,
at any fraction: `wp_osFsync_keep ... (lo2 dq2 ys2) (hc : ∀ y ∈ ys2, y.2 = true)` posting
`dur := overlay (if m.ok then durOf lo xs else []) (durOf lo2 ys2)` (clean bytes are not dirty, so
the sync keeps their durable byte = their page-cache byte; `CleanPhys`), with `wp_osFsync` its
instance `ys2 = []`; use it only in the crash-aware Fdatasync spec. Alternative: sync's `dur` keeps
the entries of `m.dur` at bytes the caller shows clean.

Open, in order:
4. The remaining obligations, each now `∀ img D, idleImg/writingImg ... → goodImg img` (pure):
   init W1 (`writingImg m bs 0 first`, `first` = zeros then pages 2-3; the old slots invalid or not
   held whole, `goodImg` of the opened image, `m.dur` = the whole file from `initMeta`/the last
   sync); S1 (`m.synced 0 _`, failed: `{m with ok := false}`, `idleImg` ignores `ok`); W2
   (`writingImg` over the zero slots, `dur` zeros from S1); S2; commit's `Truncate` and `Sync`;
   data `WriteAt`/`Fdatasync`; meta `WriteAt`/`Fdatasync` (needs the gap's fix); failure paths
   (a failed `WriteAt` leaves `pwBytes` with `j` bytes: an idle state again).
5-7. Not started: `CrashOps`/`Spec/os/Crash.lean` over `cfInvQ` (`crashOk_narrow` for `CrashOkQ`;
   `Truncate`, `File.Sync`, `Mmap`/`Munmap` with mappings), `rwR` holding `cfOwn`, the re-proofs,
   `BootCrashSafety`.

### minibolt's crash proof, round 3 (2026-11-01, branch `osfs-mbcrash`)

Merged `origin/lean` (`21879d1e78`, clean; Perennial pin still `2130bdb99`).

Done:
- **`OsMeta.durHi`** (`Ghost.lean`, untrusted): a bound on the length of the durable image,
  `MetaOk.durLen : f.durable.length ≤ m.durHi`. Needed because P1's first case ("the slot is the
  durable one") says nothing useful when the ghost state cannot rule out a durable image that holds
  the slot: a created file (`newMeta`, `durHi = 0`, the model's `OsFile.ofDisk []`), or a short
  file a crash left (`initMeta f`, `durHi = f.cur.length`), whose durable copy of a slot it does not
  hold is shorter than 64 bytes and so never equal to a slot the image holds whole. Only a
  successful sync changes the durable image (and makes it the file's size): `OsMeta.synced` sets
  `durHi := m.size`; every other step keeps it (`osCoh_setMaps`, `osCoh_addTok` now ask
  `(m'.dur, m'.durHi) = (m.dur, m.durHi)`). `DB.init.spec`'s post gained `durHi := max m.size 16384`.
- **`wp_osFsync_keep`** (`Specs.lean`, the approved proposal): a sync also given bytes `ys2` from
  `lo2`, at any fraction, shown clean, posts `m.syncedKeep lo xs lo2 ys2` (`dur := durOverlay
  (m.synced lo xs).dur (durOf lo2 ys2)`); `wp_osFsync` is its instance `0 []`
  (`OsMeta.syncedKeep_nil`).
- **`P1s`** (`CrashOk.lean`): P1 with `data ≠ []` in its third case (`P1s_P1 : P1s → P1`).
  `crashOkQ_idle`/`_writing`/`_create` are now for `CrashOkQ (P1s p)`. Reason: with the file idle,
  `CrashSeenR` admits other changes in flight on it only if they take none of the client's bytes
  and a fraction of the `OsMeta`, i.e. an empty write (another thread could start one: nothing in
  the crash invariant's half excludes it); P1's third case then admits the page cache's slot,
  even a torn one (a failed write's mix of new bytes and clean old bytes). **Decision for the
  user:** state `BootCrashSafety` with `P1s` (one conjunct; an empty write makes no change, so the
  slot "as it would leave it" is the page cache's, which P1's second case already restricts).
- **`idleImg`** gained `D.length ≤ m.durHi` and its page-cache case now requires that no byte of
  the slot is clean in `bs` (from P1's "every byte dirty or lost"; `seen_file` returns
  `CleanPhys` of the clean bytes). `writingImg` gained `D.length ≤ m.durHi`.
- **`CrashImg.lean`** (item 4, pure): slot machinery (`metaSlot_ext`, `slot_held`,
  `fileMeta_of_slot`, `slot_zero_invalid`; `durOk m i P` for the durable copy of slot `i`,
  `durOk_of`; `cacheOk bs i P` for the page cache's, idle; `idleImg_slot`, `writingImg_slot`,
  `idleImg_clean`, `writingImg_clean`), and the image obligations:
  - `goodImg_noValid`, `goodImg_cur`, `curMeta_cases`, `curMeta_congr`, `curMeta_take`;
  - init: `initIdle` (`initIdle_good`: Open's state, W1's narrowings, S1 and its failure, with
    `cacheOk` for zeros-or-clean slots), `initW1_good` (the first write in flight), `initMid`
    (after S1: durable slots zero, page 3 clean) with `initW2_good` (the meta write in flight)
    and `initMid_idle_good` (after it, S2, failures; `cacheOk` for `init`'s metas), via
    `goodImg_init`;
  - commit: `commitClean`/`commit_clean_img` (every state before the meta write: the metas and
    the current root page are clean, so an image has them; covers Truncate/Sync/data
    WriteAt/Fdatasync, in flight or idle, and their failures, given the image's size bounds and
    that the changed range misses them), `commitMeta` with `commitMetaW_good` (meta write in
    flight) and `commitMetaIdle_good` (after it, failed, or a failed meta sync), via `commit_cur`
    and `commitMeta_good`.
- **`curInSlot`** (`CrashGood.lean`): `goodImg`'s committed case also asks that the current meta
  be in slot `txid % 2` (`curMeta mp = fileMeta mp (txid % 2)`), so that the next commit, which
  writes slot `(txid + 1) % 2`, never overwrites it. Without it a crash during the meta write
  could leave the other slot, whose meta (if valid) the proof knows nothing of. `goodImg_cur`
  takes it (`hs`); `init`'s images and both commit outcomes satisfy it (`commitMeta.sTx`,
  `nTxS : N.txid = T + 1`).

All of the above: no `sorryAx` (`#print axioms` of `wp_osFsync_keep`, `crashOkQ_idle`,
`crashOkQ_writing`, `initIdle_good`, `initW1_good`, `initW2_good`, `initMid_idle_good`,
`commit_clean_img`, `commitMetaW_good`, `commitMetaIdle_good`: `propext`, `Classical.choice`,
`Quot.sound`). `CrashImg.lean` is not imported by any root (as `CrashOk.lean`); build it by name.

Open, in order (items 5-7 not started; what round 3 learned of them):
5. **Crash-aware specs over `cfInvQ`.** Plan: generalize `cfInv` to `cfInvP N p γ (Ok : CFile →
   Prop)` (`cfInv = cfInvP (CrashOk Good)`, `cfInvQ = cfInvP (CrashOkQ Q p Good)`), and
   `CrashOps.lean`'s four ops over `Ok`, the facts they use of `CrashOk` becoming hypotheses
   (`crashOk_notOk`: the caller shows `Ok` of the failed sync's state; `crashOk_tok`). **Narrowing
   does not carry over:** `crashOk_narrow` holds for `CrashOk`, not `CrashOkQ (P1s p)`, because P1
   admits the page cache's slot of each narrowing (a partial write's mix) only by its cleanliness,
   which differs between narrowings. So `File.WriteAt.specCrash` over `Ok` should ask `Ok` of every
   state the loop passes through: each narrowing idle (`finBytes`, iterated) and with the next
   attempt in flight. The image lemmas are shaped for that: idle narrowings need `cacheOk` of the
   slot (a partially written slot keeps a clean old byte, or is the data's), writes in flight need
   only the write's and the old slot. A lemma "`cacheOk` of iterated `finBytes`" (bytes outside the
   written prefix keep their flags; written bytes are the data's, flagged not clean) is the missing
   link. `syscall.Fdatasync.specCrash` posts `m.synced 0 bs` with all of `bs`, so `dur` knows the
   whole file and `wp_osFsync_keep` is needed only if the client syncs part of it (next point).
   Also needed: a `CFile` state for a truncate in flight (commit's growth: its crash images are
   `idleImg` with `hi` widened to the target, P1's write case not applying), and mappings (`CfWf`
   asks `m.maps = ∅`; minibolt maps the file).
6. **`rwR` holding `cfOwn`** conflicts with `DB.lean`'s committed pages: `pageIs` keeps them as
   persistent `osBytes ... DFrac.discard`, while `cfOwn`/`invRes` hold all of `bs` in halves.
   Proposal: let the idle `CFile` hold runs (as `cRuns` already does) with any fractions, so
   that committed pages sit in the invariant at a discarded fraction (readers' `ReadAt` and the
   mapping take them from there); a sync then takes only the pages the writer holds whole
   (`wp_osFsync_keep` records the committed and meta bytes, shown clean). `CrashSeenR`'s runs
   already have arbitrary fractions, so `seen_file` generalizes to runs covering the file.
   The DB invariant must also carry what `commitClean`/`commitMeta` ask: `curInSlot mp`, the meta
   and current root pages clean, `4096 * curPgid mp ≤ m.lo`, and, between the data page's sync and
   the meta write, `durOk m (1 - s) (old or new)` (from `wp_osFsync_keep` over the meta pages).
   `Open` must carry `curInSlot` from `goodImg` (add it to `fileOk`/`dbFresh`).
7. `BootCrashSafety`, once 5-6 are done; stated with `P1s` if the user agrees (above).

### minibolt's crash proof, round 4 (2026-11-01, branch `osfs-mbcrash`)

`origin/lean` already merged (Perennial pin `2130bdb99`, unchanged).

Done (no `sorryAx`; `#print axioms` of everything below: `propext`, `Classical.choice`,
`Quot.sound`, plus goose's usual opaque `os.*`/`sync.*`/`syscall.*` types for the Go-level specs):
- **P1 is P1s** (the coordinator's decision, `52d050ccae`): `BootP1.lean`'s `P1` has `data ≠ []`
  in its third case, with the reason in its docstring; `P1s` and `P1s_P1` are gone, `CrashOk.lean`
  and `CrashImg.lean` use `P1`.
- **`Proof/os/CrashSt.lean`: a crash invariant generic in a predicate on states** (items 1–3's
  infrastructure). A new state type instead of `CFile` (left as is, for crashlog):
  `CSt = ⟨m, bs, fa, fb, busy⟩`, `CState = Option CSt`, `busy ∈ {idle, write t off data,
  trunc t sz}`. The invariant `csInv N p γ Ok` holds `ghostVar γ ½ s`, `invResS p s` and `⌜Ok s⌝`
  for any `Ok : CState → Prop`; the caller holds `csOwn p γ s`. Bytes are per byte (`cByte`,
  `cBytes`): **`[fa, fb)` frozen**, held by the invariant at `DFrac.discard` (minibolt's committed
  pages: `pageIs` copies come from `cs_freeze`), every other byte at a half each (invariant and
  caller), minus a write's taken bytes (its token holds them). `CSt.Wf`: `bs.length = m.size`,
  `fa ≤ fb ≤ m.size`, a write misses `[fa, fb)` (`off + n ≤ fa ∨ fb ≤ off`), a truncate grows.
  Mappings are allowed (any `m.maps`). A crash sees `sMeta`/`sRuns` (one run per byte)/`sToks`;
  `CrashOkS Q p Good s` is `CrashOkQ`'s condition on that view, and `crashOkS_idle`/
  `crashOkS_write` reduce it to `CrashOkQ` of the corresponding `CFile` (`RunsSub`: a crash's view
  does not depend on fractions), so round 3's lemmas apply. `csInv_alloc` (from `osFileStart`,
  state `csStart fo`, nothing frozen), `csInv_crash_keep` (needs `CrashOkS Q p Good s`).
- **`Proof/os/CrashStOps.lean`: the extension's steps over `csInv`**: `wp_osOpen_cs` (`csOpen`),
  `wp_osPWriteStart_cs`/`wp_osPWriteFinish_cs` (mapped cells passed through: `mcellsAny` in,
  `mcells` out), `wp_osFtruncateStart_cs`/`wp_osFtruncateFinish_cs` (grown: `csGrownOwn`, or
  `ftMeta` on failure), `wp_osFsync_cs` (state `H ++ (F ++ T)`, `F` frozen: `csSynced false` syncs
  `T` and keeps `H` (shown clean) in `dur` via `wp_osFsync_keep`; `csSynced true` syncs `H`),
  `wp_osMmap_cs`, `wp_osMunmap_cs`, and the ghost step `cs_freeze` (freeze a superset; the caller
  gets `osBytes p fa' DFrac.discard` of the frozen bytes). Each takes `Ok` of every state it may
  leave as a hypothesis.
- **`Spec/os/CrashSt.lean` + `Proof/os/CrashStSpec.lean`: the crash-aware Go-level specs**
  (item 4): `os.OpenFile.specCrashS`, `os.File.WriteAt.specCrashS` (obligation: `Ok` of every
  `WReach` state, idle and with the next attempt in flight; post `WReach m bs off data m' bs'`;
  `WReach.narrow`), `os.File.Truncate.specCrashS` (growth; `Ok` of each `TReach` state, idle and
  truncating), `os.File.Sync.specCrashS`, `syscall.Fdatasync.specCrashS`,
  `golang_org.x.sys.unix.Mmap.specCrashS`/`Munmap.specCrashS`; all proved
  (`*.wp_proof_crashS`). Item 2 is covered by the frozen bytes: committed pages sit in the
  invariant discarded, a sync covers the bytes the writer holds whole (`csSynced`).
- **minibolt's obligations on the new states** (`CrashOk.lean`, `CrashImg.lean`):
  `crashOkS_trunc` (a growing truncate in flight: `idleImg (ftMeta m sz)`; P1's third case cannot
  apply), and `initIdle_okS`, `initW1_okS`, `initMid_okS`, `initW2_okS`, `commitClean_okS`,
  `commitClean_write_okS`, `commitClean_trunc_okS`, `commitMetaW_okS`, `commitMetaIdle_okS`: round
  3's image lemmas as `CrashOkS (P1 p) p Good (some s)`.

**New gap (blocks item 1's last lemma and every failure path after a partial write): the ghost
state forgets which bytes a failed write left untouched.** A clean byte cannot be in flight
(`OsCoh.bytes`: `x.2 = true → CleanPhys f i ∧ ¬ InflightAt st p i`), so `PWriteStart` takes the
range's bytes with their flags dropped (`TokInfo.saved` keeps only values) and `PWriteFinish`
returns `pwBytes`, **all flagged dirty**, including the bytes past the `k` written. Physically
those bytes are untouched (`pwFile` marks only `[min off len, off + k)` dirty) and stay clean, so
P1's page-cache case (every byte of the slot dirty or lost) excludes a torn slot; the ghost state
cannot show it, and `cacheOk` of a torn slot (`k` inside a slot: new bytes, then old ones, none
clean in the ghost) is not provable. Round 3's "bytes outside the written prefix keep their
flags" holds only outside the write's range. Affected: `cacheOk` for every idle `WReach` state
of a write whose range covers a slot: `init`'s W1/W2 and commit's meta write, i.e. their failure
paths (`initIdle_okS`'s `cache`, `initMid_okS`'s and `commitMetaIdle_okS`'s `hc`).
- Proposed fix (untrusted ghost, `GooseLang/Ext/OsFs/{Ghost,Facts,Write}.lean`; a decision for
  the user, like `OsMeta.dur`): `TokInfo` keeps the taken bytes' clean flags (`cl : List Bool`),
  with a coherence clause `cl[j] = true → f.dirty i = false ∧ f.lost i = false ∧ i < f.sizeLo ∧
  f.durable[i]? = f.cur[i]?` (`CleanPhys` without `¬ InflightAt`), kept by every step (no sync
  while a token holds the bytes, other writes touch other bytes); `pwBytes` keeps those flags for
  the bytes past the written prefix. Then "a partially written slot keeps a clean old byte, or is
  all the new data" holds for `WReach` states (given the old slot clean), and `cacheOk` follows.
  Cost: every `TokInfo` construction (`⟨c, q, saved, om⟩`), `wp_osPWriteStart`/`Finish`, the
  truncate token, `Facts.lean`'s preservation lemmas.
- Partial alternative without the ghost change: `init`'s two writes have concrete data. W1 writes
  zeros over the slots: a torn slot is the old one (if `k` stops before it) or starts with a zero
  byte, whose magic (`0xED0CDAED`, no zero byte) fails: provable now, by induction on `WReach`.
  W2's torn slots are `initMeta i`'s prefix then zeros, 2 × 64 concrete cases: `decide +kernel`
  checks one in well under a second with a concrete `GooseExts` (`osFsExts`), but `Meta` is
  parameterized by `[GooseExts]` (free variable: `decide` refuses, `rfl` fails), so the proof needs
  `metaValid (decode L : Meta) ↔` an instance-free check on the tuple `Meta.byteEncoding` is
  `ofEquiv` of (likely `Iff.rfl`). Commit's meta write has no such way out (the new meta is not
  concrete): it needs the ghost fix.

Open, in order:
5. **The DB rework** (not started; the plan):
   - `isDB` gains `csInv dbCrashN p γc (CrashOkS (P1 p) p Good)`; `rwR`'s `writerFile` holds
     `csOwn p γc (some ⟨m, bs, 8192, 4096 * hwm, .idle⟩)` in place of `osMeta 1`, `osBytes ½ mxc`
     and `osBytes 1 tail` (`thrBytes` of that state is `osBytes 0 ½ mxc ∗ osBytes (4096 hwm) ½
     tail`, `idle_thrBytes`); `metaR` loses its `osBytes ½ mxc` (the invariant holds that half
     now; the meta `WriteAt` gets the other half from it). Committed pages: `pageIs` from
     `cs_freeze` after the meta sync (`fb` becomes `4096 * (hwm + 1)`). `rwR` also needs what
     `commitClean` asks (clean metas and root page, `curInSlot`, `4096 * curPgid ≤ m.lo`,
     `m.hi ≤ 2^30`), most of it already in `writerFile`/`metaR`.
   - `curInSlot` into `fileOk`/`dbFresh` (from `goodImg`, `goodImg_fileOk`).
   - Re-prove as crash-aware variants, each step's `Ok` from the `*_okS` lemmas: `init` first
     (self-contained: `DB.init.spec` holds the file whole; a `DB.init.specCrash` over `csOwn` with
     `fa = fb = 0` needs only the W1/W2 torn-slot lemmas above), then `Open` (OpenFile, Stat,
     readPageSize with the caller's halves, init, mmap via `Mmap.specCrashS`), `commit`
     (Truncate/Sync/data WriteAt/Fdatasync/meta WriteAt/Fdatasync/freeze), `Close`
     (`Munmap.specCrashS`). Keep the existing non-crash specs (`Link.lean`) as they are; the crash
     variants are new files; `Snapshot`/`Get` unchanged if `pageIs` stays.
6. `BootMinibolt`'s per-generation proof and `BootCrashSafety` (`osFsQ_crash_adequacyT` with
   `P1`, `csInv_alloc`, `csInv_crash_keep`; `crashlog/Results.lean`'s shape with `Hinit_wp`).

### minibolt's crash proof, round 5 (2026-11-01, branch `osfs-mbcrash`)

Merged `origin/lean` (`b4274660d4`, the `etc/proof_roots.py` fix; Perennial pin still `2130bdb99`).

Done (no `sorryAx`; `#print axioms` of `wp_osPWriteFinish`, `WReach.torn`, `cacheOk_wreach`,
`initIdle_wreach`, `initMid_wreach`, `initW1_obl`, `initW2_obl`, `initSync_ok`, `commitMetaW_okS`:
`propext`, `Classical.choice`, `Quot.sound`). Rebuilt: all of `GooseLang/Ext/OsFs`, `Proof/os`,
`Spec/os`, crashlog's `Results`, every `bboltfs` module.
- **Round 4's gap 1 fixed (the approved ghost change, untrusted)**: `TokInfo.cl : List Bool`, the
  taken bytes' clean flags (`osCoh_addTok` records `xs.map Prod.snd`; truncate tokens `[]`), and
  `OsCoh.tok_clean`: `ti.cl[j]? = some true → j < affHi - affLo ∧ CleanPhys f (affLo + j)`, kept by
  `osCoh_addTok`, `pwFinish_coh` (other tokens' clean bytes are outside the finished write, by
  `infl_disj`), `ftFinish_coh`, `osCoh_setFile_sameCur` (`hkeep`), `osCoh_create`; `osCoh_setMaps`
  and the fd steps pass it through. `pwBytes` now flags a byte past `off + k` with its flag in `xs`
  (`decide (off + k ≤ i) && xs[j].2`); `pwFinish_coh`/`wp_osPWriteFinish` prove those bytes clean
  and not in flight. `cToks`/`CSt.toks` carry `cl`. Nothing downstream depended on the old `false`.
- **`Proof/os/CrashWReach.lean`** (new, generic): `finBytes_mid`, `WReach.prefix` (a retried write
  has written a prefix `K` of its data; the size is `pwSize m.size off K`; every other byte of the
  range is untouched, flag included), `WReach.torn` (a part `[a, a + w)` of the range held by the
  reached state: untouched, or first byte the data's and either an old byte left, inside the old
  file, or all data).
- **`writingImg`'s page-cache case now requires no clean byte in the slot** (as `idleImg`'s):
  `seen_writing` returns `bs[j].2 = true → ¬dirty ∧ ¬lost` for all `j`, the write's range from
  `tok_clean`. So `writingImg_slot`, `initW1_good`/`initW2_good`/`commitMetaW_good` and their
  `_okS` take `cacheOk` (no longer "the page cache's slot is invalid / P"), which is what a torn slot
  with a clean old byte satisfies. This replaces round 4's "partial alternative" (no decode of a
  zero-prefixed magic is needed).
- **`CrashImg.lean`**: `cacheOk_wreach` (the blocked lemma: from a state whose slot bytes are all
  clean, every reached state has `cacheOk` if the all-data slot satisfies `P`), `slot_data_write`,
  `wreach_dur`, `durOk_congr`, `initIdle_wreach` (the helper `initIdle_good` needed: W1's reached
  states are `initIdle`, given the slots clean in Open's bytes), `initMid_wreach`, `initMid_synced`,
  `initIdle_notOk`/`initMid_notOk`, and, ready to feed `WriteAt.specCrashS`/`Fdatasync.specCrashS`:
  **`initW1_obl`**, **`initW2_obl`** (`∀ m' bs', WReach … → Ok idle ∧ ∀ t, Ok write`, any `fa fb`),
  **`initSync_ok`** (`Ok (some (csSynced false m [] [] bs 0 0))`, i.e. `H = F = []`, `T` the file).

Not started: the separation-logic re-proofs (item 5's resource rework and `DB.init.specCrash` on),
item 6.

Open, in order:
5a. **`DB.init.specCrash`** (new Spec + Proof files, keep `DB.init.spec`). Proposed statement:
   `DB.init.spec`'s, with `csInv N p γ (CrashOkS (P1 p) p Good)` and `↑osN ⊆ ⊤ \ ↑N`, and
   `csOwn p γ (some ⟨m, xs, 0, 0, .idle⟩)` in place of `osMeta 1 m ∗ osBytes 0 1 xs`; extra
   premises `initIdle m xs` (Open: no valid slot in the durable copy or page cache, `m.hi ≤ 2^30`)
   and the slots clean in `xs` (`∀ i < 2, ∀ k < 64, ∀ x, xs[4096 i + 16 + k]? = some x → x.2`; at
   boot every byte is clean). Post: success `csOwn p γ (some ⟨m2, initFile xs, 0, 0, .idle⟩)` with
   `m2` as now (`dur := durOf 0 (initFile xs)`), failure `∃ s', csOwn p γ (some s')`. Proof: copy
   `DB__init.lean`'s; `wp_WriteAt` → `os.File.WriteAt.specCrashS` (obligation `initW1_obl`, then
   `initW2_obl` with `D = I.take 8192`, `hDs` from `initBytes_meta0/1` + `fileMeta_take`), whose post
   gives `WReach` (use `WReach.narrow`/`finBytes_data` for the bytes, in place of `pwBytes_full`);
   `wp_Fdatasync` → `syscall.Fdatasync.specCrashS` with `H = F = []`, `hd = false` (success:
   `initSync_ok`; failure: `initIdle_okS ∘ initIdle_notOk` / `initMid_okS ∘ initMid_notOk` of the
   write's last reached state). After S1 the slots are zero and clean (`syncedBytes`), as
   `initW2_obl` needs. `csSynced false … = ⟨m.syncedKeep 0 T 0 [], syncedBytes m T⟩`;
   `syncedKeep 0 T 0 [] = synced 0 T` (see `initSync_ok` for the proof without `[GooseSemantics]`).
5b. The rest of item 5 as in round 4's handoff: `isDB` gains `csInv`, `rwR`/`metaR` rework,
   `cs_freeze` after each commit, `curInSlot` into `fileOk`/`dbFresh`; crash-aware `Open`, `commit`
   (its meta write: `commitMetaW_okS`/`commitMetaIdle_okS` with `cacheOk_wreach`, the old slot
   `1 - s` clean: both meta slots stay clean between commits, as every meta write is followed by a
   sync and no other write touches the metas; carry that in `rwR`), `Close`.
6. `BootMinibolt`'s per-generation proof and `BootCrashSafety` (unchanged plan).

### minibolt's crash proof, round 6 (2026-11-01, branch `osfs-mbcrash`)

`origin/lean` not merged this round (Perennial pin still `2130bdb99`).

Done (no `sorryAx`; `#print axioms DB.init.wp_proof_crash`: `propext`, `Classical.choice`,
`Quot.sound`, plus goose's usual opaque `os.*` types):
- **5a. `DB.init.specCrash`** (`Spec/.../bboltfs/DB__initCrash.lean`, proof
  `DB.init.wp_proof_crash` in `Proof/.../bboltfs/DB__initCrash.lean`; `DB.init.spec` kept).
  Pre: `csInv N p γ (CrashOkS (P1 p) p Good)`, `↑osN ⊆ ⊤ \ ↑N`, `csOwn p γ (some ⟨m, xs, 0, 0,
  .idle⟩)`, `m.ok`, `m.maps = ∅`, `m.size ≤ 2^30`, `initIdle m xs`, `slotsClean xs` (new def).
  Post: success `csOwn p γ (some ⟨initDoneMeta m xs, initFile xs, 0, 0, .idle⟩)` (`initDoneMeta`:
  `DB.init.spec`'s `OsMeta`, as a def: `⟨{ m with … }, …⟩` does not parse inside `⟨…⟩`), failure
  `∃ sz s', filesz ↦ sz ∗ csOwn p γ (some s')`. Takes `os.File.WriteAt.specCrashS`,
  `syscall.Fdatasync.specCrashS`, `initPages.spec`, `os.File.Fd.spec`. Helpers there:
  `narrow_full0` (a successful write at 0: size `max`, bytes data ++ old suffix), `synced_eq`,
  `csSynced_nil`, `initBytes_page3`.
- `CrashImg.lean`: `initW2_reach` (W2's reached states: `initMid` and `cacheOk`; used for the
  failed-sync obligation), `initW2_obl` now uses it. **`CrashImg`'s structure `commitMeta` is
  renamed `commitMetaSt`**: it clashed with `Writer.lean`'s `commitMeta` (any file importing both
  failed).
- **5b started: `Proof/.../bboltfs/DBCrash.lean`** (the DB's resources over the crash invariant;
  see its header): `dbCrashN`, `dbOk p := CrashOkS (P1 p) p Good`, `writerFileC γc … mp fl hwm st
  m bs` (`csOwn p γc (some ⟨m, bs, 8192, 4096 * hwm, .idle⟩)` in place of `osMeta 1`, the meta
  half and the tail; while not failed: `(bs.map fst).take 8192 = mp`, **`commitClean m bs`** (so
  both meta slots and the root page clean, `curInSlot`, `bootOk`, `4096 * curPgid ≤ m.lo` hold
  between commits), and `writerFile`'s other facts), `metaRC` (`metaR` without `mx`/`mxc`/the meta
  bytes; `cls` is `∃ c, ghostVar γ.cls ½ c`), `rwRC` (`rwR` with `writerFileC`), `isDBC γ γc db`
  (`isDB` with `rwRC`/`metaRC`, `csInv dbCrashN p γc (dbOk p)`, and `∀ t vo, γ.vp t vo → bootOk t
  vo`: `Good` needs `bootOk` of every committed root page, so commit's new `commitClean.boot` comes
  from `γ.vp`). Lemmas: `commitClean_meta` (ignores maps/ok), **`writer_okS`** (the `Mmap`/`Munmap`
  obligations: any mappings, from `commitClean`), **`init_commitClean`** (`commitClean
  (initDoneMeta m xs) (initFile xs)`: after `init`, a commit may start). `mapR`, `mapInv`,
  `pageIs`, `writerCells`, `writerExtra` are reused unchanged.

Findings for the rest of 5b:
- `os.File.ReadAt.specRacy` (Snapshot) needs only `osBytes`, no `osMeta`: Snapshot/Get need no
  file change, only re-proofs against `isDBC`/`metaRC` (their proofs destructure `metaR`; `metaRC`
  differs only by the missing meta bytes and `mx = mp`).
- `readPageSize` needs no crash variant: `csOwn_idle` splits an idle `csOwn` into `osMeta ½` and
  `thrBytes`, and `idle_thrBytes` (with `fa = fb = 0` at Open: `H = []`) gives `osBytes 0 ½ bs`;
  call `DB.readPageSize.spec` with `dqm = dqb = ½` and fold back. Same for `File.Stat`.
- `Mmap`/`Munmap` change only the mappings: `golang_org.x.sys.unix.Mmap.specCrashS`/`Munmap.specCrashS`
  with `writer_okS`. `CrashOkS` does depend on the maps syntactically (`CrashSeenR` fixes `Γm`), so
  the obligation needs `commitClean` (i.e. `fl = false`, which `DB.mmap.spec` already assumes).

Open, in order:
5b. (a) **`DB.mmap.specCrash`** (new files; `DB.munmap.specCrash` is done: `DB__munmapCrash.lean`
   in Spec and Proof, `DB.munmap.wp_proof_crash`, no `sorryAx`, with `mappingResC`/`unmappedResC`:
   `csOwn p γc (some ⟨m, bs, fa, fb, .idle⟩)` plus `⌜bs.length = m.size ∧ commitClean m bs⌝` in
   place of `osMeta 1 m`, and `dbCrashN_disj : ↑osN ⊆ ⊤ \ ↑dbCrashN`): a copy of `DB__mmap.lean`
   with `writerFileC`, `DB.munmap.specCrash` and `Mmap.specCrashS` with `writer_okS`. `mmap_prep`/`mmap_unmapped`
   (`DB__mmap.lean`) have `osMeta` in their statements: crash copies needed.
   (b) **`Open.specCrash`**: pre `csInv dbCrashN p γc (dbOk p) ∗ csOwn p γc s` with `s = none` or an
   idle state all clean whose bytes are a `goodImg` (`csStart (some f)` with `Good (some f)`, as
   `csInv_alloc`/`csInv_crash_keep` give), and `∀ t vo, vp t vo → bootOk t vo`; post `isDBC γ γc
   db …` (as `Open.spec`'s) or failure `∃ s', csOwn p γc s'`. Steps: `os.OpenFile.specCrashS`
   (`Ok (csOpen s)`: `csOpen none` is the empty file, `initIdle_okS`; an existing file is `s`),
   flock, `Stat`/`readPageSize` via `csOwn_idle` (above), `DB.init.specCrash` on a short or
   uninitialized file (`initIdle` from `goodImg`'s first two cases with every byte clean and
   `m.dur` the whole file, as `initMeta f` sets it; `slotsClean` from all clean), then
   `init_commitClean`; for a committed file `commitClean` from `goodImg`'s third case (needs
   `curInSlot` in `fileOk`/`dbFresh`, or take `goodImg` directly in the crash spec); then
   `cs_freeze` from `(0, 0)` to `(8192, 4096 * hwm)` (hsub vacuous), whose discarded bytes give
   every `pageIs p r B` for `2 ≤ r < hwm` (split with `bytesG_append`, all clean), and
   `DB.mmap.specCrash`.
   (c) **`DB.commit.specCrash`** (copy of `DB__commit.lean`, 1139 lines; `writerSt`/`writerStF`
   need crash copies over `writerFileC`): Truncate (`commitClean_trunc_okS` in flight,
   `commitClean_okS` idle, both from `commitClean_meta` for `ftMeta`/`grown`), data `WriteAt` at
   page `hwm` (`commitClean_write_okS`; misses the metas and root page: `hwm > curRoot`), Fdatasync
   with `H = metas`, `F` = frozen, `T` = tail, `hd = false` (`csSynced false` keeps the clean
   metas in `dur`: gives `commitMetaSt.dur` for slot `1 - s` with `durOk_of`), meta `WriteAt` at
   `4096 * (1 - s)` (`commitMetaW_okS`/`commitMetaIdle_okS`, `cacheOk_wreach` from the slot clean
   by `commitClean.metas`), Fdatasync, then `cs_freeze` to `(8192, 4096 * (hwm + 1))` for the new
   page's `pageIs`, and the new `commitClean` (`boot` from `isDBC`'s `vpBoot` and `dbTx`).
   (d) **`Close`** over `rwRC`/`metaRC` (Munmap crash, file close); its post hands back `csOwn`.
   (e) `Get`/`Snapshot` re-proved against `isDBC` (mechanical).
6. `BootMinibolt`'s per-generation proof and `BootCrashSafety` (unchanged plan; at boot every byte
   is clean, `csStart`, which gives `slotsClean` and `Open.specCrash`'s premise).

### minibolt's crash proof, round 7 (2026-11-01, branch `osfs-mbcrash`; in progress)

`origin/lean` not merged (Perennial pin still `2130bdb99`).

Done (no `sorryAx`; axioms `propext`, `Classical.choice`, `Quot.sound` plus goose's opaque types):
- **`DB.mmap.specCrash`** (`DB__mmapCrash.lean`, Spec and Proof; `DB.mmap.wp_proof_crash`):
  `DB.mmap.spec` with `writerFileC γc … st m bs` in place of `writerFile`, plus `csInv`; post
  `writerFileC … st' m' bs` (same bytes) with `m'.size/ok/hi/lo` unchanged. Helpers:
  `writer_thrBytes` (the writer's halves of its idle state: `bs.take 8192` at 0 and the tail),
  `unmapRestC`, `mmap_prepC`, `mmap_unmappedC` (the state after munmap is `{ m with maps := M }`,
  `M = ∅` on success). The new mapping's cells agree with the meta pages through `csOwn_idle` +
  `writer_thrBytes` (osMeta ½, osBytes ½), folded back after.
- **`Open.specCrash`** (`OpenCrash.lean`, Spec and Proof; `Open.wp_proof_crash`). Statement: for
  `fo : Option OsFile` with `Good fo`, `freshTx ((startImg fo).map (·, true)) = (t, vo, n)`,
  `vp t vo`, `∀ t vo, vp t vo → bootOk t vo`; pre `pkgFacts ∗ osInv ∗ csInv dbCrashN path γc (dbOk
  path) ∗ csOwn path γc (csStart fo)`; post as `Open.spec`'s with `isDBC γ γc db`, or failure
  `∃ s', csOwn path γc s'`. Pure lemmas there: `startMeta`, `csOpen_csStart`, `openStart`,
  `noValid`/`committedImg`/`goodImg_cases`, `start_initIdle`, `start_commitClean`, `start_okS`,
  `freshTx_noValid/committed`, `openReady` (the file after the init step: `commitClean`, all
  clean, `lo = size`, txid/value/hwm), `ready_init`, `ready_committed`, `noValid_of_rps`,
  `committed_of_rps`, `noValid_of_short`; ghost: `csOwn_idle00`, `ready_pages` (the frozen bytes
  as `pageIs`), `open_ghostC` (`open_ghost` with `metaRC`). `Open.wp_proof_crash` needs
  `set_option maxRecDepth 20000` (kernel deep recursion otherwise; cause not investigated).
- **`writerFileC` change**: it now also carries `∀ M, dbOk p (some ⟨{ m with maps := M }, bs, 8192,
  4096 * hwm, .idle⟩)` (unconditionally, third conjunct), and `mappingResC` carries the same for
  its state in place of `bs.length = m.size ∧ commitClean m bs`: a failed handle (no
  `commitClean`) can still unmap (`Munmap.specCrashS`'s obligation) in `Close`.
- **`DB.commit.specCrash`** statement (`Spec/.../DB__commitCrash.lean`: `writerStC`/`writerStFC`,
  `metaRC`, `rwRC`, extra premise `bootOk (t + 1) (some v)`); its proof is being done separately
  (see the section's end for status).
- **`DB.Commit.specCrash`** (`DB__CommitCrash.lean`, over `isDBC`; `bootOk` from `isDBC`'s
  `vpBoot`), proved from `DB.commit.specCrash`: `rwRC_of_writerStC`, `fail_handleC`.
- **`DB.close.specCrash`** (`DB__closeCrash.lean`, `mappingResC`/`unmappedResC`) and
  **`DB.Close.specCrash`** (`DB__CloseCrash.lean`, over `isDBC`; post `∃ p, db.path ↦□ p ∗ ∃ s,
  csOwn p γc s`: the closed state's contents are not kept, a boot does not reopen in the same
  generation), proved; `unmappedC_own`.
- **`DB.Get.specCrash`**, **`DB.Snapshot.specCrash`** (`DB__GetCrash.lean`, `DB__SnapshotCrash.lean`,
  over `isDBC`), proved by the mechanical copy (`metaRC` for `metaR`); `dbReaderC_borrow`.
- **`DB.commit.specCrash` proved** (`Proof/.../DB__commitCrash.lean`, `DB.commit.wp_proof_crash`,
  no `sorryAx`; file-level `set_option maxRecDepth 20000`, `maxHeartbeats 1000000` on the main
  theorem). Deviations from the plan: the meta page's Fdatasync uses `hd = true` (the meta bytes are
  dirty after the write, so `hd = false`'s premise fails; its success state gives the new
  `commitClean`); `cs_freeze` to `4096 * (hwm + 1)` happens after the meta sync. Its helpers
  (all in that file): `commitClean_of_prefix`, `treach_commitClean`, `trunc_obl`,
  `synced_commitClean`, `dataW_obl/after`, `dataS_facts`, `commitMetaSt_of/_wreach/_meta`,
  `metaW_obl/after`, `metaSynced_commitClean`, `metaS_facts`, `csOwn_split3`, `commitErrC*`,
  `meta_failC`, `dataErrC`, `dataErrTC`, `frozen_page`, `rwRC_of`, list/sync lemmas
  (`syncedKeep_dur`, `csSynced_false_eq/_true_eq`, ...). Notes: `omega` unfolds `curPgid` in a
  hypothesis `curPgid mp = hwm` and blows up (hide it: `HideEq`); give `(m := …)` to
  `writer_okS`/`commitClean_meta` (unification loops on `{ m with maps := M }`); use
  `rw [csSynced_false_eq]`, not `dsimp only [csSynced]`.
- **Item 6.** `wp_BootMinibolt` (`BootMinibolt.lean`): one generation of `BootMinibolt(dir)`, no
  panic, over `Open/Get/Commit/Close.specCrash` with `vp := bootOk`, under an extra premise
  `bootPremises fo` (`1 ≤ t`, `t + 1 < 2^64`, `(n + 2) * 4096 ≤ 2^30` for `freshTx`'s `t, n`).
  `bootCrashSafety` (`Results.lean`): `BootCrashSafety dir` from `osFsQ_crash_adequacyT`,
  `csInv_alloc` (`start_dbOk`), `csInv_crash_keep`, every spec linked to its proof, under the
  hypotheses `Hinit_wp` (the package initializer, ending in `pkgFacts`), `Hprem : ∀ fo, Good fo →
  bootPremises fo` (**false**, below), `Hlive` (fewer than `2^30` live threads in executions of
  `≥ 2^30 - 2` steps: `Open.specCrash` needs `ThreadBoundLe GF (2^30)`), and the `os.file`/
  `os.fileStat` field facts. `BootP1.lean`: the stray `[GoSemanticsFunctions]` binder of
  `BootCrashSafety` was removed (it made `package_sem : Assumptions` resolve against it rather
  than `go.Semantics`'s, so the statement was unprovable).
- `#print axioms bootCrashSafety`, `DB.commit.wp_proof_crash`, `Open.wp_proof_crash`,
  `DB.Snapshot.wp_proof_crash`, ...: `propext`, `Classical.choice`, `Quot.sound` and goose's type
  declarations; no `sorryAx`.

**Gaps (decisions for the user), in order:**
1. **A reachable panic in `BootMinibolt`** (`bootPremises.1` false): `init` writes both metas in
   one `WriteAt(buf[:2*pageSize], 0)`; a crash tearing it can leave slot 0 (txid 0) whole and
   valid and slot 1 zero, which `goodImg` accepts (committed, `bootOk 0 none`, `curInSlot`).
   That boot passes its check, commits txid 1 with value 1; the next boot reads txid 1 with a
   value and panics ("init's root page holds a value"). Fixes: (a) `init` writes and syncs slot 1
   (txid 1) before slot 0 (or writes only slot 1; slot 0 stays zero), so txid 0 is never current;
   then strengthen `goodImg`'s committed case to `1 ≤ txid`; (b) change the check in
   `BootMinibolt` (accept txid 1 holding 1) and widen `bootOk`. Either changes Go code (regoose).
2. `(n + 2) * 4096 ≤ 2^30`: `metaPagesOk` gives only `(n + 1) * 4096 ≤ 2^30`. A full file makes the
   Go `Commit` return an error (its `mmap` of `(n+2)` pages fails? check), but
   `DB.Commit.spec(Crash)` requires the bound. Fix: drop the premise and allow the error result
   (spec change in `DB__Commit.lean`/`DB__commit.lean` and their crash copies).
3. `t + 1 < 2^64`: `goodImg` does not relate txid and pgid. Fix: add `txid < pgid` to `goodImg`'s
   committed case (kept by `init`: 1 < 4, and each commit adds one to both), carried in
   `commitClean`.
4. `Hlive`: prove the boot program forks no thread, or add `n + 2 ≤ 2^30` to `BootCrashSafety`.
5. `Hinit_wp`: the package initializer (as crashlog's).

Next: decide gap 1, then fix 1–3 (`goodImg`, `commitClean`, the obligations, `Open.specCrash`'s
`freshTx` facts), which discharges `Hprem`; then 4.

### minibolt's crash proof, round 8 (2026-11-01, branch `osfs-mbcrash`)

`origin/lean` not merged (Perennial pin still `2130bdb99`).

Done (no `sorryAx`; `#print axioms bootCrashSafety`: `propext`, `Classical.choice`, `Quot.sound`
and goose's opaque declarations, `.underlying`/`.zero_val`/`.init`, as in round 7):
- **`DB.init`'s two proofs** for the Go fix of `154786d32a` (meta 1 at 4096, synced, then meta 0
  at 0, synced). `DB__init.lean`: the buffer's first 8192 bytes split with `ownSlice_split` at
  4096; the file split in three around page 1. `DB__initCrash.lean`: `narrow_mid` (a write inside
  the file read back), `map_clean_getElem`; both theorems need `set_option maxRecDepth 20000`.
- **`goodImg`'s committed case has `txOk`** (`CrashGood.lean`: `1 ≤ txid ∧ txid < curPgid`);
  `goodImg_freshTx_tx` gives `1 ≤ t < n ∧ (n + 1) * 4096 ≤ 2 ^ 30` for `freshTx`.
  `goodImg_cur` takes `1 ≤ X.txid` and `X.txid < X.pgid`.
- **`init`'s states in two phases** (`CrashImg.lean`): `initMid ph` (`ph = false`: meta 1 being
  written at `4096 * initSlot false`, slot 0 clean and zero; `true`: meta 0 at 0, slot 1 clean
  and `init`'s meta 1: `initOrd`), `goodImg_init` with `h01` (slot 0 valid only with slot 1:
  `curMeta_init1`, the current meta is meta 1, txid 1). `initW_good/okS/reach/obl`, `initWData`
  (the data's slot is `initBytes`'s), `initW_done` (after a meta write: slots, page 3, and
  `initOrd true` for the next sync), `initMid_synced`/`initSync_ok` take `ph` and `initOrd ph` of
  the clean bytes.
- **`commitClean.tx : txOk`** (last field), **`commitMetaSt.tx`** (after `metaS`) and
  **`commitMetaSt.nTxPg`** (after `nRootPg`); `init_commitClean`, `start_commitClean`
  (`committedImg` has `txOk`), `commitClean_of_prefix`, `commitMetaSt_of`,
  `metaSynced_commitClean` (new premise `txOk mp'`), `metaS_facts` (new premise
  `mv.txid < hwm`, from `hcc4.tx`).
- **`bootPremises`** is now only `(n + 2) * 4096 ≤ 2 ^ 30`; `wp_BootMinibolt` gets `1 ≤ t` and
  `t + 1 < 2 ^ 64` from `goodImg_freshTx_tx`.
- **`BootCrashSafety` takes `n + 2 ≤ 2 ^ 30`** (`BootP1.lean`), `Hlive` dropped:
  `bootCrashSafety` uses `RealCrashThreadsBelow.of_single` (`T = n + 2`). Why not a proof that the
  boot program forks no thread: `RealCrashThreadsBelow` is a property of every reachable
  configuration of the real semantics (no `Fork` redex through every function `FuncResolve`/
  `MethodResolve` reach, every closure in the heap, every external step's result); there is no
  proof device for it, and the adequacy theorem does not derive the thread bound from the proof's
  thread tokens (that would be a new Perennial adequacy theorem). `Open` needs `ThreadBoundLe GF
  (2 ^ 30)` for `mmaplock`'s reader pool.

**Left (decision 2, blocked on the Go code):** `Hprem : ∀ fo, Good fo → bootPremises fo`, i.e.
`(n + 2) * 4096 ≤ 2 ^ 30`, is false for long runs. `Good` gives `(n + 1) * 4096 ≤ 2 ^ 30`; at that
bound `commit` computes `minsz = (n + 2) * 4096 > 2 ^ 30`, `mmap(minsz)` maps `mmapSize(minsz) =
2 ^ 31` (no cap in `mmapSize`), and `db.grow` truncates the file to `2 ^ 31`; the model's `Mmap`
(any `len > 0`) and `ftruncate` succeed, as Linux does. The new meta has `(pgid + 1) * 4096 >
2 ^ 30` and the file exceeds 1 GiB: not `goodImg` (`img.length ≤ 2 ^ 30`, `metaPagesOk`). Dropping
the premise from `DB.Commit.spec`/`DB.commit.spec` therefore needs a check in Go, e.g. in
`commit`, `if minsz > maxMapSize { return errFull }` (1 GiB), before `mmap`; then the specs can
allow that error result and `bootPremises` goes. Nothing else is assumed besides `Hinit_wp` and
the `os.file`/`os.fileStat` field instances.

### minibolt's crash proof, round 9 (2026-11-01, branch `osfs-mbcrash`)

`origin/lean` not merged: its Perennial pin moved (`c4a24e323`), so the branch stays on
`2130bdb99` until someone merges it with the pin bump.

Done (no `sorryAx`; `#print axioms bootCrashSafety`: `propext`, `Classical.choice`, `Quot.sound`
and goose's opaque declarations, as in rounds 7-8): **`Hprem` is gone**, on the Go fix of
`63528e82b9` (`commit` returns `errMapTooLarge` when `minsz = (pgid + 1) * 4096 > maxMapSize`,
1 GiB, before remapping).
- **`pkgFacts`** ends with `∃ e3, globalAddr errMapTooLarge ↦□ e3 ∗ ⌜e3 ≠ nil⌝`
  (`pkgFacts_errMapTooLarge`); `Get`/`Snapshot`'s `icases` of it take one more `-`.
- **`DB.commit.spec`/`specCrash`** drop `(curPgid mp + 2) * 4096 ≤ 2 ^ 30`; the proofs take
  `(hwm + 1) * 4096 ≤ 2 ^ 30` from `metaPagesOk` (no overflow in `minsz`) and split on the check
  (`by_cases Hb`): past it, `errMapTooLarge` with the state unchanged, not failed
  (`commitErr_of`, `commitErrC_mk`); below it, the old proof with `Hb`. Clear `Hb1` in that branch:
  with both `Hb1` and `Hb` in context, later `omega`s hit `maxRecDepth`.
- **`DB.Commit.spec`/`specCrash`** drop `(n + 2) * 4096 ≤ 2 ^ 30`; the result is unchanged
  (`Commit` fails the handle on any error from `commit`, so the error branch already covered it).
- **`bootPremises` removed**; `wp_BootMinibolt` needs only `Good` (`1 ≤ t`, `t + 1 < 2 ^ 64` from
  `goodImg_freshTx_tx`). Its error branch after `Commit` (close, return) needed no change.
- `testMinibolt`, `testMiniboltConcurrent`: one premise fewer to `wp_Commit`. `Link.lean`
  regenerated (unchanged).

`bootCrashSafety`'s remaining hypotheses: `Hinit_wp` (package initialization, ending in
`pkgFacts`), the `os.file`/`os.fileStat` field instances, and, in `BootCrashSafety` itself, the step
bound `n + 2 ≤ 2 ^ 30` and P1 (the strengthened crash relation).

Left: the step bound (a thread-count proof device or an adequacy theorem deriving the bound from
thread tokens, see round 8), and `Hinit_wp` (needs `wp_initialize'` for `os`, `syscall` and their
imports).
