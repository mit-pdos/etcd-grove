# Plan: a Linux file extension (files, fsync, read-only mmap) for bbolt

**Date:** 2026-10-31. **Status:** design agreed in outline; decisions D1–D8 below take the
recommended option until the user says otherwise. **Perennial pin:** `d62b13ac1`.

The extension is this repository's (`GooseLang/Ext/OsFs/`), not Perennial's. Perennial
translates the standard library and owns its trust lists (`os.toml` translates nothing and
trusts nothing), so the extension's Go side is a thin wrapper package whose API mirrors exactly
the `os`/`syscall`/`golang.org/x/sys/unix` calls bbolt makes. That package's functions are
`trusted` here (as `examples/durable`'s are for `durableExt`), and the bbolt fork calls the
wrapper instead of `os`. Where the wrapper lives is open (W below).

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
| `PRead(fd, off, n)` | fd readable, off ≥ 0 | `cur[off, min(off+n, size))`; a byte under an in-flight change is arbitrary, and while a change resizes the file the length is anything ≤ n (`ReadSees`). On failure, a prefix of that with an errno. |
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
  `render` sets mapping cell i to the byte `cur[i]`, or to `#()` (a *hole*) when i is past EOF
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

## Trusted Go models (the wrapper's functions)

- `*File` mirrors Go's `File{*file}`: a cell holding a pointer to an inner cell holding
  `(fd, name)`.
  - `Close` sets the fd to -1, so copies of the struct share that state, as in Go.
  - `Fd()` is a load (a closed file gives `^uintptr(0)`).
  - `Name()` is the exact name.
- `Stat()` returns a value holding the size, and `Size()` reads it.
- `Sync` and `Fdatasync` are both `Fsync` (D3).
- Errors are `&PathError{op, name, Errno(e)}`. A short `ReadAt` returns `io.EOF`.
- Trivial ones:
  - `Flock` returns nil or an arbitrary Errno; it is stuck on a fd not open (D7).
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
- crash adequacy covers the restart, because a process death is a crash at that step, and the
  files keep the page cache, which the crash image allows.

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
- **W (open):** where the wrapper package lives.

## Work

1. `GooseLang/Ext/OsFs/Impl.lean`: state, `render`, step, crash.
2. The wrapper package, its trusted models (`TrustedCode/...`), its `.toml`; constants.
3. Test programs: `examples/bboltfs` (targets, stuck probes, unprovable probes, a minibolt).
4. `Specs.lean` (untrusted): mapped cells use the ordinary byte points-to; per-byte file ghost state
   that owns the mapped cells; the durable/dirty ghost state; `ExtCrashInterp`.
5. Adequacy with the environment assumptions as premises.
