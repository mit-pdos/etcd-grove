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
touches them. The device honours cache flushes. Opening any other path is stuck. Path
resolution is not modelled.

## State

```lean
structure File where
  cur      : List w8   -- what pread, fstat and the mappings see; size = cur.length
  durable  : List w8   -- the image known to be on disk
  dirty    : GSet Nat  -- offsets whose durable byte may differ from cur
  sizeLo sizeHi : Nat  -- smallest/largest size since the last successful sync
  poisoned : Bool      -- a sync failed since boot (D2)
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
| `PRead(fd, off, n)` | fd readable; `[off, off+n)` misses every in-flight write's affected range | `cur[off, min(off+n, size))`, or a prefix of it with an errno |
| `PWriteStart(fd, off, data)` | fd writable; affected range misses the other in-flight writes | records the write, returns a token |
| `PWriteFinish(tok)` | – | writes a prefix of length k (k = len on success), marks it dirty |
| `Fstat(fd)` | no in-flight change resizes the file (D8) | `cur.length` |
| `FtruncateStart(fd, sz)` / `FtruncateFinish(tok)` | fd writable; no other change in flight on the file | resize, zero-fill; dirty from `min(old, new)` to `max(old, new)`. Two steps, like pwrite: a pread racing a shrink can stop anywhere between the sizes on Linux. While in flight, it affects every byte from `min(size, sz)` on, and `Fstat` is stuck. |
| `Fsync(fd)` | – | success: `durable[i] := cur[i]` for dirty i outside in-flight writes; size durable. Failure: `poisoned := true` |
| `Close(fd)` | fd open | removes the fd; errno arbitrary (the fd is freed either way) |
| `Mmap(fd, off, len, prot, flags)` | off = 0, prot = PROT_READ, flags ∈ {SHARED, SHARED\|POPULATE}, fd readable, len > 0, no in-flight write on the file | fresh page-aligned (4096) range of `len` cells, or an errno |
| `Munmap(base, len, cap)` | `base` a mapping, `len = cap` = its length | removes the mapping and its cells |

- **Affected range** of a write of n bytes at `off`: `[min(off, size), off+n)`. It includes the
  zero gap that an extending write creates. Any read, load or stat that could see a partial
  write is stuck. That is the only race rule.
- **Two-step pwrite.** An atomic pwrite would be more defined than Linux, because a concurrent
  `LoadBytes 8` or `pread` can tear. With a start and a finish step, any real overlap in time
  maps to a model interleaving that is stuck.
- **One heap rule.** Every step ends with `h' := render st' (h minus the cells of st.maps)`.
  `render` sets mapping cell i to `(Reading 1, LitByte cur[i])`, or to `(Reading 1, #())` (a
  *hole*) when i is past EOF or in an in-flight write's affected range. The phantom reader makes
  every store stuck. A hole makes every load stuck (SIGBUS, or a race). No operation spells out
  its own heap update.
- **The extension never touches user buffers.** The trusted models marshal them with ordinary
  Go: `WriteAt(b, off)` passes `string(b)`, and `ReadAt` `copy`s the returned data into `b`.

## Crash

`fds`, `inflight` and `maps` are dropped (the heap is arbitrary after a crash). Each file
becomes an image, which is then both `cur` and `durable`:

- **Existence.** If `¬named`, the file may vanish (D4).
- **Size.** Any size in `[sizeLo, max(sizeHi, in-flight ends)]`, or any size if `poisoned`.
- **Bytes.** Byte i is `durable[i]` unless i is dirty, in an in-flight write, `≥
  durable.length`, or the file is poisoned. In those cases it is arbitrary (D1).

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

## Perennial prerequisite

`CmpXchgBytesFailS` accepts cells with readers (`BytesAt … true`). On a `PROT_READ` page, x86
`LOCK CMPXCHG` faults even when the compare fails, so the model is more defined than Go there.
It should require `BytesAt … false`. Only the phantom reader gives byte cells readers, so
nothing else should change. This goes through Perennial's `/fix-semantics` with the user's
sign-off; until then, avoid CAS on mapped memory (a probe records it). Recorded in
`notes/perennial-changes.md`.

## Decisions (recommended option first; taken until the user says otherwise)

- **D1:** unsynced bytes are arbitrary after a crash (vs old-or-written). Either way, bbolt's
  torn-meta argument needs a no-checksum-collision premise.
- **D2:** a failed fsync poisons the file (vs a precise lost-pages set). The lost pages are not
  rewritten by a later successful fsync, so "the next successful sync makes everything durable"
  would be unsound.
- **D3:** `Fdatasync` = `Sync`: both flush contents and size. Linux flushes `i_size` in
  fdatasync. bbolt's `init` grows an empty file by `WriteAt`, then calls `fdatasync`.
- **D4:** a created file is not durably named until a crash survives it (no dir fsync
  primitive).
- **D5:** known gap: Go's finalizer closes an unreachable unclosed file's fd, the model never
  does, so the model cannot return that number again. Observable only by comparing stored fd
  integers.
- **D6:** misuse is stuck, not an errno.
- **D7:** `Flock` is trivial (single-process spec).
- **D8:** `Stat` racing an extending write is stuck. This matters for bbolt only with
  `NoGrowSync`.
- **W (open):** where the wrapper package lives.

## Work

0. The Perennial prerequisite above.
1. `GooseLang/Ext/OsFs/Impl.lean`: state, `render`, step, crash.
2. The wrapper package, its trusted models (`TrustedCode/...`), its `.toml`; constants.
3. Test programs: `examples/bboltfs` (targets, stuck probes, unprovable probes, a minibolt).
4. `Specs.lean` (untrusted): a points-to for phantom-reader cells; per-byte file ghost state
   that owns the mapped cells; the durable/dirty ghost state; `ExtCrashInterp`.
5. Adequacy with the environment assumptions as premises.
