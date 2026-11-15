# Review, round 7: the byte-level crash rule (branch `fs-bytes`)

**Date:** 2026-11-11. **Reviewed:** branch `fs-bytes` at `12e1519ace` ("the crash rule byte by
byte"), phase 1 (trusted semantics only; the program logic and clients do not build on it). In
scope: `GooseLang/Ext/Fs/{Impl,Premises,FilteredSem,SemOk,Tests}.lean` (changed), with
`Tree`/`Paths`/`Lookup` and `TrustedCode/{os,syscall}.lean`, `TrustedCode/golang_org/x/sys/unix.lean`
read for how they call the changed steps (unchanged since round 6); `examples/osfs/semantics/*.go`;
the motivation in `fs-v2-r6/e2e/README.md`, `notes/fs-semantics-v2.md` ("Byte-level crash
candidates"), `notes/decisions.md` (newest entry).

**Method.** The `axiom` skill's, for a trusted semantics: every rule that changes `cache`, `cand`,
`size`, `sizeLo`/`sizeHi` checked against every interleaving the step relation allows (which
changes are stuck while another is in flight), and against ext4 v7.0 as rounds 4-6 read it. No
kernel experiment was needed: no finding depends on a kernel behaviour not already measured in
rounds 4-6 (the one kernel fact used, that ext4's buffered `pwrite` and `open(O_TRUNC)`'s truncate
both take `i_rwsem` and so serialize, is from `ext4_buffered_write_iter` and `do_truncate`).
`lake build GooseLang.Ext.Fs.Tests` passes (two `if_pos` deprecation warnings). The concrete model
computations below are checked in `fs-v2-r7/otrunc_race.lean` (`lake env lean
notes/axiom-review/fs-v2-r7/otrunc_race.lean`, no output = checked).

## Verdict

**No outcome of Linux on C found that the crash rule excludes.** The page cache is always among
the candidates (`CacheCand`) in every reachable state, so a crash after full writeback can keep
it; the author's open question (the zero gap computed at the START size) is unreachable: while a
write with a gap is in flight nothing can move the size up (every growing change is stuck), and
the only thing that moves it down, `O_TRUNC`, announces zeros over the whole old size. But the
invariant holds only by that argument across four rules, not by construction, and `Tests.lean`
checks it only for the steps that cannot break it. The client premise `SectorWhole` is stronger
than its docstring says: `valAt · m` is "the page cache right after change m" only when the
changes on a sector are sequential and land whole; with an `O_TRUNC` racing a write (F1) or two
disjoint writes in flight on one sector (F5) it excludes a state the page cache really had,
written back whole. Neither case is reachable from etcd's WAL. The simplest uniform fix is one stuck
rule (`O_TRUNC` stuck while a change is in flight, as `ftruncate` already is) plus storing each
change's announced range and values in the change, so that a finish copies announced values and
`CacheCand` holds by construction.

| # | severity | finding | where |
|---|---|---|---|
| F1 | too-strong assumption (`SectorWhole`; unreachable for the WAL) | `open(O_TRUNC)` is not stuck while a write is in flight on the file (`OpenEffect` has no `BusyAt` guard, unlike `FtruncateStart`/`FallocStart`); it takes a later stamp than the write, which lands after it, so `valAt` (last stamp wins) disagrees with the page cache (last landing wins): `SectorWhole` excludes the fully-written-back state | `Impl.lean:496-498`, `Premises.lean:43-46` |
| F2 | simplification (soundness by construction) | `CacheCand` holds in every reachable state only by a cross-rule argument (Affects uses the current size; growth stuck by PWriteStart's disjointness and BusyAt; `O_TRUNC` announces `[0,size)`); `landWrite` recomputes values from the finish-time size instead of using what was announced | `Impl.lean:286-308, 338-341, 604-617`; `Tests.lean:367-394` |
| F3 | simplification | `Affects` of a resize is `[min size sz, ∞)`, its announce `[min size sz, max size sz)`; an empty `pwrite` past EOF announces and "affects" `[size, off)` though it changes nothing (`written`'s and `landWrite`'s special cases) | `Impl.lean:291-292, 341, 273-277, 302-304` |
| F4 | doc-only | "a size it had since its last successful sync" (header, `CrashFile`): the rule is any size in `[sizeLo, sizeHi]` (needed: ext4's `i_disksize` stops at extent ends the program never set, as `data_sizes_since_sync.go` says) | `Impl.lean:83, 819-820` |
| F5 | too-strong assumption (`SectorWhole`; known in part) and doc | `valAt · m` is the page cache after change m only for sequential, whole changes: a short write (acknowledged in `fs-semantics-v2.md`, "Open") and two disjoint writes in flight on one sector landing out of start order (not acknowledged) give real page-cache states no stamp gives | `Impl.lean:153-155`, `Premises.lean:33-37` |
| F6 | (no finding) failed `fsync` | no state change is sound under "no failed writeback", and the assumption is stated in the header, at the `Fsync` step and in `env_no_failed_writeback.go`/`data_failed_fsync.go` | `Impl.lean:40-43, 637-646` |
| F7 | (no finding) sizes against bytes | every byte always has a candidate; truncate-down then crash, ftruncate racing a write, `fallocate` failing part way, sync during a resize: each crash size and byte combination checked is a superset of ext4's | `Impl.lean:819-827, 310-318` |
| F8 | doc-only | stale or mismatched text: header "durable zeros at a successful sync" (not for busy bytes); `data_mixed_writeback.go` (doc says 1 and 2, code 1, 2, 3); `data_inflight_changes.go` (its `Mmap` races the write and is stuck; "old or new" where `ReadSees` gives any byte); `data_durable_zeros.go` ("the page or zeros": any byte-wise mix is allowed); `SemOk.lean:5` names `NoTear.lean`; `os.lean:300` "all of the data with errno 0" (a short write with errno 0 is allowed) | listed in F8 |

## F1: `O_TRUNC` racing a write, and `valAt`

**Rules.** `OpenEffect` (`Impl.lean:496-498`) truncates an existing file with
`st.stampFile i (fun n => (f.announceResize 0 n).truncate 0)`, with no condition on the changes in
flight. `PWriteStart` checks only against other in-flight changes; `FtruncateStart` and
`FallocStart` require `¬ BusyAt`. So this interleaving is a run of the model:

1. file `[1, 1]`, synced (`ofBytes`);
2. `PWriteStart` of `[2]` at 0, stamp 1 (byte 0's candidates `[(1,0), (2,1)]`);
3. `Open(O_TRUNC)` from another thread, stamp 2 (bytes 0, 1 get `(0,2)`; size 0);
4. `PWriteFinish`, 1 byte: size 1, cache `(2, 0)`.

Linux has the same outcome: ext4's buffered write and the truncate both hold `i_rwsem`, so this is
"truncate, then write", the file `[2]`. A crash after writeback keeps `(2, 0)` (byte 1 is in the
size's page). **Crash rule: fine** (`2` is byte 0's stamp-1 candidate, `0` byte 1's stamp-2 one).
**`SectorWhole`: excludes it**: byte 0's `valAt` is 1, 2, 0 at stamps 0, 1, ≥2, byte 1's 1, 1, 0;
`(2, 0)` is none (`otrunc_race.lean`, first part). The premise's docstring promises "the one
right after some change m"; the state right after the write is exactly this one.

**Reach.** None of the clients opens with `O_TRUNC` while writing the same file (round 6, D2), and
the WAL never does; so no WAL theorem is affected. But the premise as defined is false of a run
its docstring says it allows.

**Fix (simplest, uniform).** Make `O_TRUNC` on an existing file require `¬ BusyAt st i` (stuck
otherwise), as `FtruncateStart` does: `O_TRUNC` is a truncate. Linux serializes the two, so a
proved program loses no behaviour it relies on, and with it the size of a file is constant while a
write with a gap or any resize is in flight (F2), so stamp order and landing order agree on every
byte except across disjoint concurrent writes (F5).

## F2: `CacheCand` holds, but only by an argument across rules

**Claim checked (question 2).** In every reachable state, for every file, every byte's page-cache
value is among its candidates and `sizeLo ≤ size ≤ sizeHi`. The steps that change `cache` or
`cand`:

| step | `cand` | `cache` | why `CacheCand` survives |
|---|---|---|---|
| boot, crash (`ofDisk`) | `[(diskByte img sz b, 0)]` | `diskByte img sz` | equal |
| `PWriteStart`, `FtruncateStart`, `FallocStart` (`announce`) | appended | unchanged | append |
| `PWriteFinish` (`landWrite`) | unchanged | `[min off size_f, off+k)` recomputed with the finish-time size `size_f` | needs: data bytes announced (yes); gap bytes `[size_f, off)` have a `0` candidate (below) |
| `FtruncateFinish`, `FallocFinish` incl. partial (`truncate`) | unchanged | `[min size_f sz, max size_f sz)` := 0 | needs a `0` candidate there (below) |
| `O_TRUNC` | `[0, size)` gets `(0, n)` | `[0, size)` := 0 | same step |
| `Fsync` success (`synced`) | non-busy: `[(diskByte cache size b, 0)]` | non-busy: same value | equal; busy kept |
| `Fsync` failure, `Mmap`, `Munmap`, reads | unchanged | unchanged | |

The finish's obligations hold because, for an in-flight change `c`, the finish-time range is
contained in the start-time announced range or in a later `O_TRUNC`'s `[0, size)`:
- the size can rise during `c`'s flight only through a change whose `Affects` contains the current
  size. If `c` is a write with a gap (`off > size`) or any resize, its own `Affects` contains the
  current size too, so a second write is stuck (`PWriteStart`'s disjointness) and a resize is stuck
  (`¬ BusyAt`); a resize in flight admits only writes below `min size sz`, which do not grow the
  file. A write without a gap has `lo = off` whatever the size does;
- the size can fall only through `O_TRUNC` (a shrinking resize admits no gap write), which
  announces zeros over the old `[0, size)`, covering `[size_f, size_s)`.
And the bytes a finish may change are always inside `InflightAt` at any sync before it (`Affects`
uses the current size, which only falls, so the range only widens), so a sync never collapses a
byte a later finish changes. So question 1's case (a concurrent change that extends the file
before a gap write finishes) is **unreachable**: every such change is stuck.

**The weakness.** This is four rules cooperating (`Affects`' current size, `PWriteStart`'s
disjointness, `BusyAt` on resizes, `O_TRUNC`'s announce), and `landWrite` does not use what was
announced: it recomputes from the finish-time state and relies on the argument to land on an
announced value. `Tests.lean` proves `CacheCand` kept by `ofDisk`, `announce` and `synced` only,
the three steps that cannot break it, and its header presents that as the check.

**Fix (by construction).** Record the announcement in the change: `OsChange` keeps the announced
range `[lo, hi)` and values `v` (for a write, `written` at the start; for a resize, zeros). Then
`Affects c b := inRange c.lo c.hi b` (no size), and a finish sets `cache b := c.v b` on the landed
part (`[lo, off + k)` for a write, `[lo, hi)` or the partial `[size, sz')` for a resize), the size
as now. Every cache write is an announced value whose candidate is kept by every sync while `c` is
in flight, so `CacheCand` is one line per step. With F1's stuck rule the result equals today's on
every run (the bytes in `[size_f, lo)` are already zero after a shrink), and `written`'s `d = []`
and `landWrite`'s `k = 0` cases go. If the stored form is not wanted, at least add
`theorem cacheCand_step` (every `IsFsStep` keeps the invariant above) to `Tests.lean`.

## F3: `Affects` and the announce disagree

A resize's `Affects` is `[min size sz, ∞)` while it announces `[min size sz, max size sz)`.
The extra bytes only make a sync leave pages past `max` uncollapsed (a harmless over-
approximation) and make writes above `max` stuck during a resize. An empty `pwrite` past EOF
(`data = []`, `off > size`) announces zeros on `[size, off)` and its `Affects` is that range,
though it changes nothing (the trusted `WriteAt` never issues one: it returns before the call when
`len = 0`). With F2's stored range these become the same definition; otherwise define a resize's
`Affects` as its announced range, and an empty write's range as empty.

## F4: crash sizes, in the text

The header (line 83) and `CrashFile`'s docstring (819-820) say "a size it had since its last
successful sync". The definition is any `sz` with `sizeLo ≤ sz ≤ sizeHi` (or towards an in-flight
target), and must be: ext4's delalloc writeback raises `i_disksize` to the end of each mapped
extent, sizes `i_size` never had (`data_sizes_since_sync.go` says so, and gives 250 as an
example). Say "any size between the smallest and largest it had since its last successful sync".

## F5: what `valAt · m` is (question 5)

`valAt l m` is the candidate of largest stamp `≤ m`. It equals the page cache right after change
`m` when every change on the bytes in question started after the previous one finished and landed
all it announced. Otherwise:
- **short landing** (a write landing `k < len` with errno 0, F6 of `fs-v2.md`; mechanism A's
  in-syscall window): the page cache's prefix-new, rest-old state is no stamp's. Acknowledged
  (`fs-semantics-v2.md`, "Open"): for `SectorWhole` it is the intended exclusion (a torn sector);
  the premise's docstring should say so ("a change's prefix" is in it, but "the one right after
  some change m" reads as if the prefix state were one);
- **interleaved changes on different bytes of one sector**: `W1` at byte 0 (stamp 1) and `W2` at
  byte 1 (stamp 2) both in flight, `W2` lands first: the cache `(old, W2)` is no stamp's (`(1,1)`,
  `(2,1)`, `(2,3)` at stamps 0-2; `otrunc_race.lean`, second part). `SectorWhole` excludes a
  sector the page cache really held, with no tear. Not acknowledged. Unreachable for the WAL (one
  appender under its mutex); bbolt's P1 is stated the same way and should be checked for it when
  bbolt is ported (minibolt is one writer);
- **`O_TRUNC` racing**: F1.
- **after a sync with a change in flight**: busy bytes keep their stamp history, the others
  collapse to stamp 0; `valAt` then combines a busy byte's pre-sync value with a non-busy byte's
  post-sync one, a state that may not have existed. This only adds states, so it weakens the
  premise (fine).

`SectorWhole` is satisfiable (`sectorWhole_durable`; it needs `h0`, every byte having a stamp-0
candidate, which holds since every list starts with one and `synced` keeps one). Compared with
the WAL's actual assumption (`isTornEntry`: a torn tail leaves whole zero sectors), it is
"each sector is one state in program order", which for a single sequential appender over
preallocated zeros gives exactly that and no more. **Fix:** the docstrings of `valAt` and
`SectorWhole` state the condition ("for changes on the sector that do not overlap in time; a short
landing's intermediate state is excluded on purpose"); F1's stuck rule removes the third case.
Making `valAt` follow landing order instead would need a second stamp at the finish; not worth it
while no client races writes.

## F6: failed fsync (question 3)

Under "no failed writeback" (header 40-43: no device I/O error, no failed delayed allocation), a
failed `fsync` lost nothing: whatever it wrote is a candidate anyway, whatever it left dirty is
still in the cache, and the next successful `fsync` writes it (Linux marks pages clean only on a
failed writeback, which the assumption excludes). So "no change" is sound and is the weakest
choice (no size made durable, no candidates collapsed). The assumption is stated where a reader
looks: the header, the `Fsync` step's comment, `env_no_failed_writeback.go` and
`data_failed_fsync.go`. Not an issue but worth a line: on C under the environment's assumptions
no failure of a file `fsync` is known to remain; the branch is kept as extra behaviour, which is
fine.

The atomic `Fsync` step against concurrent writes (mechanism B): a write whose syscall starts after
`fsync` entered can have its `PWriteStart` placed after the `Fsync` step (collapse, then announce:
the mix is allowed); one that started before is in flight at the step (its bytes kept). A write
that finished before `fsync` entered was written back and waited for. No interleaving found that
needs a candidate the model drops.

## F7: sizes against bytes (question 4)

- Every byte always has at least one candidate (lists only grow, or become one element).
- Truncate down, not synced, crash: any size in `[new, old]`; bytes of the old range old or 0;
  pages past the crash size zeros. ext4 frees the blocks with the size (orphan list completes it
  at recovery), so a page past the recovered size has no block: zeros. Superset.
- Truncate down, synced, grow, crash (`crash.sh shrink-grow`): stamp-0 candidates are 0 past the
  synced size's page, so zeros. Matches.
- Stale bytes past EOF in the size's page from boot, then an extension, then a crash: the stale
  byte is a stamp-0 candidate and may come back; real (the page cache zeroes them when read in,
  the disk block keeps them until the page is written). Allowed.
- `ftruncate` racing a write: a write is allowed only below `min size sz`; the crash size ranges
  towards the target; bytes above have their candidates. Superset.
- `fallocate` failing part way: any size in `[size, sz]`, zeros announced over `[size, sz)`.
- Sync while a resize or extending write is in flight: `sizeLo = sizeHi = size`, and the crash's
  in-flight disjunct reaches the target; the busy bytes keep their candidates. Superset.

## F8: text that does not match

- Header, "Durable zeros": "at every point where a file's size is durable (a successful sync, ...),
  the bytes of each page wholly past that size are zeros": not the bytes under a change in flight
  at the sync (`synced` keeps them).
- `data_mixed_writeback.go`: "Allowed: ... any byte-wise mix of 1 and 2 / Excluded: a byte that is
  neither 1 nor 2", while the function writes 1, 2, 3 and says "any byte-wise mix of 1, 2 and 3".
- `data_inflight_changes.go`: the `Mmap` is before `<-done`, so it may race the write, and `Mmap`
  is stuck while any change is in flight (`¬ BusyAt`, `Impl.lean:659`); the comment says only the
  load is. And "sees, per byte range, old or new data" / "any mix of the change's prefixes": the
  model (`ReadSees`) gives an in-flight byte any value.
- `data_durable_zeros.go`: "Excluded: size 4096 holding anything else than the page or zeros":
  any byte-wise mix of MAGIC's page and zeros is allowed; say "a byte that is neither".
- `valAt`'s docstring (`Impl.lean:153-154`): F5's condition.
- `SemOk.lean:5`: "e.g. `NoTear.lean`" (deleted); now `Premises.lean`'s `SectorWhole`.
- `TrustedCode/os.lean:300`: "`PWriteFinish` writes all of the data with errno 0, or a prefix with a
  nonzero errno": it also writes a non-empty prefix with errno 0 (a short write), which the loop
  handles; the sentence after says so. Older than this commit.
- `Tests.lean` header: "`CacheCand`, which `ofDisk`, `announce` and `synced` keep": the steps that
  could break it are not covered (F2).

## Not done

No kernel experiment (none needed: no new kernel claim). The program logic and the clients do not
build on this commit and were not reviewed. `Tree`/`Paths`/`Lookup` and the metadata rules are
unchanged since round 6 and were not re-attacked.

## Dispositions (2026-11-11, fork S2)

- **F1: fixed**, more broadly. Every change's first step, `open(O_TRUNC)` included (`OpenEffect`),
  is stuck while a change is in flight on the file: at most one change per file (`BusyAt`). This
  was chosen over an `O_TRUNC`-only rule, per the user's guidance (stuck restrictions instead of
  modelling interleavings). Every client changes each file from one thread.
- **F2: fixed by construction.** `OsChange` stores its announcement (`lo`, `hi`, `val`, `target`;
  `OsChange.ofWrite`, `OsChange.ofResize`), and `OsFile.announce c n` announces exactly it.
  - Each finish lands a prefix `[c.lo, e)` of the announced values with `OsFile.land c e sz`:
    - a write: `e = off + k`, or `c.lo` if nothing landed; `sz = max size e`;
    - a resize: `e = c.hi`, `sz = c.target`;
    - a failed `fallocate`: any `e` in `[c.lo, c.hi]`, `sz = e`.
  - `InflightAt` is the announced range.
  - `Tests.lean` proves the invariant `CacheOk` (page cache among candidates; size in range;
    announced values of every change in flight are candidates of its file; a write's `hi` is the
    end of its data; inodes below `nextIno`) at the start (`cacheOk_init`), after every step
    (`cacheOk_step`, all 27 cases of `IsFsStep`) and after a crash (`cacheOk_crash`).
- **F3: fixed.** A resize's range is its announced `[min, max)`; `Affects` is gone. An empty
  `pwrite` is stuck (Go's `WriteAt`/`Write` never issue one), so `written` lost its `d = []` case.
- **F4: fixed.** The header and `CrashFile` say "a size between the smallest and the largest it had
  since its last successful sync (ext4's delayed allocation ...), or towards the target of the
  change in flight".
- **F5: documented.** Out-of-order finishes are now impossible (one change per file).
  `valAt`'s and `SectorWhole`'s docstrings say `valAt · m` is the page cache after change `m` when
  every change landed whole, and that a short landing's state is excluded on purpose.
  Not adopted: a second stamp at each finish (announcing the landed state). It would make
  `SectorWhole` hold for short landings, but it would also make a short-landed, torn meta slot
  "one state" for bbolt's P1, so P1 would no longer exclude it. That weakens P1 where it matters,
  and no client needs the extra case.
- **F6, F7:** no change needed.
- **F8: fixed.**
  - The header's durable-zeros sentence now exempts bytes under the change in flight at a sync.
  - `data_mixed_writeback.go` now says 1, 2 and 3.
  - `data_inflight_changes.go` is rewritten: one change per file; any value seen by a racing read;
    the `Mmap` moved before the write.
  - `data_durable_zeros.go` now allows any byte-wise mix, excluding only a byte that is neither.
  - `SemOk.lean` now points to `Premises.lean`.
  - `TrustedCode/os.lean` now mentions the short write with errno 0.
  - The `Tests.lean` header now describes `CacheOk`.
  - Stale Lean names are fixed in the other examples.
