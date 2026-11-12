# Review, round 6: the trusted base of branch `fs-v2` on configuration C

**Date:** 2026-11-10. **Reviewed:** branch `fs-v2` at `cea8cc1430` (round 5's fixes `19a6667efc`
and dispositions), on configuration C (`fs-config/README.md`; every experiment below made its
filesystem with `fs-config/mkfs-mount.sh` and passed `fs-config/check.sh`; crash images recovered
with `c_recover`). In scope, as rounds 4-5: the top-level statements (`bboltfs/Results.lean`'s
`bootCrashSafety` over `BootNoTear.lean`, `crashlog/Results.lean`,
`walfs/{Results,SegLogResults,DirSwapResults}.lean`) and their Go programs; the semantics
`GooseLang/Ext/Fs/{Impl,Tree,Paths,Lookup,FilteredSem,AdequacyS,NoTear}.lean`; the models
`TrustedCode/{os,syscall}.lean`, `TrustedCode/golang_org/x/sys/unix.lean`; `etc/goose.py`'s
project `walfs`. Changed since round 5: `NoTear.lean`'s justification (a program assumption,
buffer address ≡ file offset mod 4096, and a machine assumption, no migration of a source page
mid-copy), `Follows` reduced to the start-order rule, `DirSync` = `commitAll`.

**Method.** The `axiom` skill's, for a trusted semantics. Kernel claims read in the v7.0 sources
round 4 fetched (`.lake/review-r4/k`); Go claims in go1.27.3's sources
(`~/go/pkg/mod/golang.org/toolchain@v0.0.1-go1.27.3.linux-amd64`) and its compiler's output. Scripts
in `fs-v2-r6/` beside this report. No Lean counterexample was built: the findings are about premises
of the theorem (they narrow what it covers), not runs that a theorem's conclusion excludes.

## Verdict

**No run on C found whose outcome a top-level theorem's conclusion excludes; but NoTear's
program assumption is false of minibolt, so `bootCrashSafety`'s premise is false of minibolt's
real runs on C, and the machine assumption is not something Linux provides.** minibolt's write
buffers are not the heap objects round 5's argument is about: go1.27.3's escape analysis puts every
one of them on the goroutine stack, where they sit at `addr % 4096 = 0xd10` (commit) and `0xda8`
(init) in a plain `main` (A1, measured with `strace`). With that buffer offset, a pwrite on C under
compaction commits a prefix ending 952 bytes into the file page (14 in 30 s, A1); every such commit
violates `NoTearCrash` if a crash or a process kill finds it, and the window is not only
microseconds (`balance_dirty_pages` can sleep inside it, and a fatal signal there ends the write at
that cut: A2). minibolt itself survives these cuts for another reason (its checksum, round 1's P1),
which the theorem no longer states. The machine assumption (ii) was not seen to fail (0 mid-page cuts in 7.1·10⁸ aligned source
pages under forced compaction), but no kernel code excludes it, and the docstring's account of the
window it guards is wrong (A2). The rest
held: the start-order journal rule and `commitAll` under every write reordering a flush-honouring
device allows (C1, 13 scenarios, 867 images); readdir racing inserts and htree conversion (D1);
`O_TRUNC` races (D2, reasoned).

| # | severity | finding | evidence |
|---|---|---|---|
| A1 | too-strong assumption (premise of `bootCrashSafety` false of minibolt's runs) | NoTear's program assumption "minibolt's buffers are size-class aligned" is false: all five write buffers are stack-allocated (`does not escape`), at `0xd10`/`0xda8` mod 4096; under compaction such a write commits a mid-page prefix (cut at 752/952 bytes) | **tested on C** (`addr/`, `tear/`), compiler output |
| A2 | too-strong assumption (machine assumption ii: honestly labelled, frequency evidence only) and doc (`NoTear.lean`, `notear.go`) | (ii) not excluded by Linux, not observed in 7.1·10⁸ aligned pages; the torn window includes `balance_dirty_pages_ratelimited` (may sleep under dirty throttling, while writeback runs) and a fatal-signal check, so a SIGKILL there ends the write at a mid-page cut: "a fatal signal is checked between folios, never inside one" is false; the not-uptodate path also commits a mid-page prefix (retry with `bytes = copied`) | kernel source (`mm/filemap.c:4313-4381`, `fs/ext4/inode.c:3292`); **tested on C** (`tear/`, aligned: 0 mid-page cuts) |
| S1 | simplification (the proposed fix) | drop NoTear from `bootCrashSafety` and restore round 1's P1 (a torn meta slot does not validate), which minibolt's FNV checksum gives whatever the cut; or, keeping NoTear, make minibolt's buffers escape (heap, size-class aligned) and keep (ii) as an assumption | reasoned; Go source |
| C1 | (no finding) journal order and `commitAll` under device reordering | round 5's 13 scenarios replayed with every write since the last flush kept or dropped at random (8 subsets per crash point): 0 violations in 867 images; no C behaviour outside the start-order rule found, and the rule's extra freedom only concerns overlapping calls, which no client makes | **tested on C** (`reorder/`), kernel source |
| D1 | (no finding) readdir racing inserts | getdents64 through 512/2048-byte buffers while 200-5000 names are created (linear-to-htree conversion, leaf splits): no name returned twice, none missed (12 runs) | **tested on C** (`readdir/`) |
| D2 | (no finding) `O_TRUNC` racing reads and maps | reasoned from `ext4_setattr` and `filemap_read`: a racing read returns a prefix of the old bytes or nothing, a racing mapped load is stuck in the model when after the step; no client opens with `O_TRUNC` | kernel source |
| D3 | doc-only | `NoTear.lean`/`BootNoTear.lean`/`notear.go`: "size classes 44 and 59", "the 4096-byte second half of one" (it is the second page, `buf[pageSize:2*pageSize]`, and the first, `buf[:pageSize]`); "a fatal signal … never inside one"; `bboltfs/README.md` still states P1 as "the premise of the crash property", and "a killed process loses nothing" (A2: a SIGKILL can leave a torn page in the cache) | read |

## Findings

### A1 (too-strong assumption): minibolt's pwrite buffers are on the stack, not 4096-aligned

**The claim.** `NoTear.lean` (the docstring's "Program assumption"), `BootNoTear.lean`'s header
and `examples/osfs/semantics/notear.go`: "minibolt meets it: it writes only `make([]byte, n)`
buffers of 4096 or 16384 bytes (and the 4096-byte second half of a 16384-byte one) at offsets that
are page multiples, and go1.27.3 places the objects of those size classes at multiples of 4096 and
8192 (`internal/runtime/gc/sizeclasses.go`, classes 44 and 59)". Round 5's disposition rests
`bootCrashSafety`'s premise (`fsExtsSemanticsWithS NoTearStep NoTearCrash`) on it.

**What go1.27.3 does.** The size classes are as stated (`sizeclasses.go:50,65`: 4096 and 16384,
"min align" 4096 and 8192), but no minibolt buffer is a heap object. The compiler's escape analysis
(`go build -gcflags=-m ./osfs/bboltfs/`, go1.27.3):

```
osfs/bboltfs/minibolt.go:108:13: make([]byte, 4096) does not escape     (readPageSize: a read)
osfs/bboltfs/minibolt.go:123:13: make([]byte, 16384) does not escape    (init: buf)
osfs/bboltfs/minibolt.go:128:15: make([]byte, 16384) does not escape    (init: first)
osfs/bboltfs/minibolt.go:348:13: make([]byte, 4096) does not escape     (commit: the data page)
osfs/bboltfs/minibolt.go:361:14: make([]byte, 4096) does not escape     (commit: the meta page)
```

A non-escaping `make` of constant size up to `ir.MaxImplicitStackVarSize = 64 KiB`
(`cmd/compile/internal/ir/cfg.go:19`) lives in its function's stack frame, at whatever offset the
frame layout gives it (8- or 16-byte aligned). `os.File.WriteAt` → `poll.FD.Pwrite` →
`syscall.Pwrite` does not leak its slice. Goroutine stacks start on 8 KiB runtime pages and a frame's
offset from the stack top is fixed per call path, so each write site has a fixed `addr % 4096`.
Measured (`addr/addr.sh`: `BootMinibolt` called from a plain `main`, 200 boots under `strace -e
raw=pwrite64`, on a C filesystem):

```
pwrite64 len  4096  off%4096 0  addr%4096 0xd10  x399   (commit's data and meta pages)
pwrite64 len  4096  off%4096 0  addr%4096 0xda8  x2     (init's meta 1, buf[4096:8192], and meta 0, buf[:4096])
pwrite64 len 16384  off%4096 0  addr%4096 0xda8  x1     (init's first)
```

(From the package's test binary, `TestMain` → `BootMinibolt`, the same sites gave `0xc48` and
`0xce0`.) So the program assumption is false of minibolt: each write's source crosses a page
boundary 752 bytes in (`4096 - 0xd10`), and init's at 600, 4696, 8792, 12888.

**What C then does.** Round 5's A1 measured that program-written, misaligned source memory is
absent now and then under compaction, and the copy commits the prefix up to the source boundary.
Here with minibolt's own offset (`tear/run.sh /tmp/r6t 3144 4096 30`: `0xc48`, the test binary's
commit offset; a 64 MiB cached file; a loop writing `/proc/sys/vm/compact_memory`):

```
skew 3144, wsize 4096: 3322880 writes (addr % 4096 = 0xc48)
@calls: 3322963   @midpage: 14   @short[0]: 5   @short[952]: 14
```

14 writes in 30 s committed a 952-byte prefix of a page (a cut inside sector 1) before the rest.
Compaction runs on C without the loop (kcompactd, `vm.compaction_proactiveness = 20`, direct
compaction for any high-order allocation on the machine); the loop makes it frequent. Each such
commit is a state `NoTearCrash` excludes: the folio is unlocked and dirty with bytes
`[0, 952)` new and `[952, 4096)` old, writeback or another process's `sync` can write it (round 4,
N1), and a crash (or a kill, A2) before minibolt's `fdatasync` finishes leaves it on disk.

**Consequence.** `bootCrashSafety` is not refuted: its premise is a hypothesis on the executions,
and its conclusion holds of the runs satisfying it. But the claim made for it ("minibolt's real
runs on C satisfy the no-tear premises", `BootNoTear.lean`) is false: a run of minibolt in which
compaction hits a write's source and a crash follows within the window is a real run on C the
theorem says nothing about. minibolt itself survives these runs: its meta (bytes 16-80 of the page)
and its data page's header and value (bytes 0-24) are in sector 0, which a source-boundary cut at
752 or 952 leaves whole; but a mid-copy cut (A2) can fall inside sector 0, and then only the FNV
checksum protects the boot (P1).

### A2 (too-strong assumption, doc): the machine assumption, and how long the torn window lasts

**The claim.** `NoTear.lean`: "Machine assumption: no source page is unmapped while the copy is
inside it … Linux does not exclude it; on C it was not seen in 3·10⁶ aligned writes under forced
compaction. Assumed." And: "A fatal signal is checked between folios, never inside one: it cuts a
write at a page boundary."

**The kernel (v7.0, `mm/filemap.c:4306-4381`).** The copy is `copy_folio_from_iter_atomic` with
page faults disabled. Compaction migrates an anonymous page by replacing its PTE with a migration
entry and flushing the TLB (an IPI, taken while the copy runs with interrupts on); the next load
from that page in the copy faults, the fault is not handled (faults disabled), and the copy
returns short at that byte, which can be anywhere in the page. Nothing pins the source page against
migration (no `get_user_pages`). So (ii) is not a property of Linux; it can only be a frequency
claim. Then:

- *uptodate folio* (an overwrite of a cached page): `ext4_da_write_end` keeps the short count
  (`fs/ext4/inode.c:3292` zeroes it only for a folio not uptodate) and commits the prefix;
- *not-uptodate folio* (e.g. minibolt's new data page past the old cached size): `write_end`
  returns 0, and since `copied > 0` the loop retries with `bytes = copied` (`filemap.c:4363-4365`):
  `write_begin` on the shorter range reads or zeroes the block, the copy of the present prefix
  succeeds, and the prefix is committed. Round 4 and 5 described only the first case; both commit a
  mid-page prefix.

After the commit the folio is unlocked and the loop goes back to its top (`:4314-4322`) before
copying the rest: `balance_dirty_pages_ratelimited` (which sleeps, killably, when the machine's
dirty memory is over its threshold, exactly while the flusher is writing dirty pages back), then
`fatal_signal_pending` → `-EINTR`, `break`, and the call returns the bytes written so far, ending
mid-page. So the torn state lasts not only the microseconds of a migration: under dirty throttling
it lasts the throttle's sleep with writeback active, and a SIGKILL there (the OOM killer, a
supervisor's stop timeout) ends the write at the cut, leaving the torn page in the cache for the
restart (which the environment's "restart after `sync`" makes durable). The docstring's "a fatal
signal is checked between folios, never inside one" is false after a short copy.

**Measured (aligned buffers, the case (ii) covers).** `tear/run.sh`, buffer address ≡ file
offset (mod 4096), pool of 256 MiB written by the program, a 64 MiB cached file, compaction loop:

| run | writes | source pages copied | short copies (cut in file page) | mid-page |
|---|---|---|---|---|
| `0 65536 1200` (64 KiB writes, 20 min) | 4.04·10⁷ | 6.46·10⁸ | `[0]` ×3 | 0 |
| `0 4096 600` (one-page writes, 10 min) | 6.64·10⁷ | 6.64·10⁷ | none | 0 |
| (for scale) `3144 4096 30`, minibolt's offset, 30 s | 3.3·10⁶ | 3.3·10⁶ | `[0]` ×5, `[952]` ×14 | 14 |

So no mid-copy cut in 7.1·10⁸ aligned source pages (round 5: 3·10⁶). A migration that lands
inside the ~100 ns copy of a page is far rarer than one that is under way when the copy reaches the
page (the rate the last row shows), as expected, but not excluded by any code path. The assumption
is stated honestly ("Linux does not exclude it … Assumed"); its evidence is now 0 in 7·10⁸. It
remains an assumption whose only support is a frequency, which is the reason S1 prefers a route
without it.

**Fix.** S1.

### S1 (simplification, the proposed fix): drop NoTear; minibolt's checksum is enough

NoTear now needs two assumptions beyond C, one false of minibolt (A1) and one Linux does not
provide (A2), to rule out a state that minibolt's design already tolerates: a meta slot whose
sector is torn fails `Validate` (magic, version, FNV-64a of the first 56 bytes) unless the mixture
collides, and then `Open` uses the other slot, which is durable (`Commit` writes slot `txid % 2`
after the previous commit's `fdatasync`). That is round 1's P1, still the premise
`examples/osfs/bboltfs/README.md` states. Options, in order of preference:

1. **P1 instead of NoTear.** `bootCrashSafety` over the plain semantics (`fsExtsSemantics`), with
   P1 as the hypothesis on the crash images of a meta slot (as `old/osfs-v1/.../BootP1.lean` had).
   P1 is a property of the program's checksum, independent of the kernel, the Go compiler and the
   machine; the semantics then needs no filter (`FilteredSem`, `NoTear`, `AdequacyS` leave the
   trust base for this theorem). The cost is re-proving the crash part of minibolt's proof over
   `CrashFile`'s arbitrary in-flight prefix (the v1 proof did it over the v1 model).
2. **Keep NoTear, fix the program assumption.** Make minibolt's write buffers heap objects of the
   page-multiple size classes (e.g. keep them in `DB`, as bbolt does with `db.pagePool` and
   `tx.pages`, so they escape), and check it (a `go build -gcflags=-m` test, or a runtime
   `uintptr(unsafe.Pointer(&buf[0])) % 4096 == 0` check that panics). (ii) stays an assumption, to be
   stated as what it is: a frequency claim ("not observed in N writes"), since Linux does not
   exclude it.
3. **A weaker NoTear** cannot be stated without addresses: the source-boundary cut depends on the
   stack layout, and the mid-copy cut falls anywhere, so neither a page cut nor a sector cut is
   true of every run.

### C1 (measured, no finding): the start-order rule and `commitAll` under device reordering

**The rules.** `Tree.lean:107` (`Follows log x y := y < x ∧ ∃ ex, log[x]? = some ex ∧ y < ex.start`),
`Impl.lean:502` (`commitAll`: every logged entry committed), `:707` (`DirSync`).

**Reasoned.** (1) Does C keep a call `x` without a call `y` that took effect before `x` began? `y`'s
handle joined a transaction `Ty` before `y` became visible (ext4 creates its handle before
`d_instantiate_new`; `d_move` is after the rename's handle stops), `x`'s handle starts after `x`
began, so in a transaction no earlier than `Ty`; jbd2 replays whole transactions in order. No. (2)
Does `commitAll` commit something a successful directory `fsync` might not? `ext4_sync_file` on a
directory is `ext4_force_commit` (`fs/ext4/fsync.c:120-121`), which commits the running transaction
(or waits for the committing one) and waits for it; every call that took effect before that point
has its handle in that transaction or an earlier one. A call taking effect while the fsync waits
may join the next transaction; the model's `DirSync` step can be placed at the point the
transaction is locked, before that call's step, since `DirSync` changes nothing else a thread can
observe. Sound. (3) What the rule permits that C forbids: two overlapping calls kept in either
combination (C serializes same-directory calls by `i_rwsem`, and an `x` whose handle is in `T1` can
be kept without a `y` that took effect first but whose handle opened after `T1` closed is also
possible on C). The clients' metadata calls are on one thread (`Sequential`, `Crash.lean`'s
`follows_seq`), so the kept set is a prefix by the rule itself; no proof leans on another route.

**Measured.** Round 5 replayed `dm-log-writes` logs in completion order only (its "Limits"). A
device that honours flushes may persist any subset of the writes completed since the last
`PREFLUSH` (a FUA write once complete). `reorder/reorder.py` replays round 5's logs with that
freedom: at each crash point (before every flush/FUA entry, and at the end) every write before the
last `PREFLUSH`, every FUA write, and a random subset of the rest (8 subsets per point and the empty
one), recovered by a kernel mount and checked with round 5's checkers:

| scenario | crash points | images | violations |
|---|---|---|---|
| `segdir`, `dirswap`, `crashlog`, `replace`, `overlap`, `xrename` (meta) | 27, 27, 24, 19, 31, 31 | 75, 75, 69, 53, 95, 95 | 0 |
| `trunc-race`, `shrink`, `falloc0`, `keep-past`, `gap`, `seglog`, `grow-sync` (data) | 20, 19, 19, 23, 19, 24, 26 | 55, 53, 52, 64, 46, 71, 64 | 0 |

Device reordering between flushes is inside C's device clause ("honours cache flushes": nothing
more is promised between them), and the model holds under it.

### D1 (measured, no finding): readdir racing inserts

`DirReadNext` excludes a name returned twice that no call touched (`Impl.lean`, "not returned since
it was last touched"). The risk on ext4 is a directory converted from linear to htree
(`make_indexed_dir`) or a leaf split while a read is positioned in it. `readdir/readdir.sh`: a
directory of N names (`orig%05d`), read with `getdents64` through a 512- or 2048-byte buffer; after
the first batch, M names created; the read continued to the end. N = 100, 150, 200, 240 (M = 200:
the directory goes from one linear block to an htree, `lsattr` flag `I`), N = 1000, 5000 (M = N:
splits): every run returned each original name exactly once (0 duplicates, 0 missing). The only
client that reads a directory (walfs's `readNames`) does not change it meanwhile.

### D2 (reasoned, no finding): `O_TRUNC` racing reads and mappings

`OpenEffect` truncates in the open's one step, without `FtruncateStart`'s `¬ BusyAt`. On C,
`do_truncate` holds `i_rwsem`, so it serializes with a buffered write (whose two model steps can
be placed on either side). `ext4_setattr` sets `i_size` to 0 and removes the folios under
`invalidate_lock`; a racing `filemap_read` either copies folios it had already referenced (old
bytes, a prefix if it re-reads `i_size` between batches) or sees size 0: within `PRead`'s "a prefix of
what `ReadSees` allows". A mapped load after the truncate is `SIGBUS` on Linux and stuck in the
model; one before it reads the old byte in both. No client opens with `O_TRUNC`.

### D3 (doc-only)

- `NoTear.lean` ("Program assumption", "Machine assumption", the fatal-signal bullet),
  `BootNoTear.lean`'s header, `semantics/notear.go`: per A1/A2; also "the 4096-byte second half of
  a 16384-byte one" is `buf[pageSize:2*pageSize]` (the second page) and `buf[:pageSize]` (the first),
  both at offset 0 of their file page.
- `examples/osfs/bboltfs/README.md:38` still calls P1 "the premise of the crash property"; the
  theorem's premise is NoTear (or P1 again, after S1). Its "a killed process loses nothing, because
  the page cache survives" is false after A2's SIGKILL in a torn window (the cache keeps a torn
  page).

## Attacks that failed

- Journal order, `commitAll`, durable zeros under device reordering: C1.
- Readdir under concurrent inserts: D1.
- `NoTearStep`'s returned count: a successful `pwrite` on C returns the whole length after a short
  copy (the loop faults the source in and finishes); a short return needs an error after something
  was written, which on C is only the fatal signal of A2 (the process then never sees the count),
  `ENOSPC`/`EDQUOT` from a later folio's `write_begin` (a page boundary), or `EFAULT` (no Go buffer).
  So the step premise holds of every return a Go program sees; only the crash premise fails (A1/A2).
- Escape changes under the trusted models: Goose's `make` is a heap allocation of the model, whose
  addresses are not the machine's (round 5's disposition); the theorem cannot see A1, which is why
  it has to be an assumption about the compiled program.
- The test-binary vs. `main` difference: both misaligned (A1); every call path checked gives a
  nonzero offset, and a fixed offset of 0 would be a coincidence of frame layout.

## Not tried

- A Lean counterexample (none is due: the findings are false premises, not false conclusions).
- A crash that catches A1's torn page on disk (the measurement is of the page cache; that writeback
  and a crash can take it there is round 4's N1).
- Mid-copy migration with other triggers than `compact_memory` (CMA allocations, memory hotplug).

## Summary

| # | severity | what | evidence | fix |
|---|---|---|---|---|
| A1 | too-strong assumption | minibolt's buffers are stack-allocated, `addr % 4096` = `0xd10`/`0xda8`: the program assumption is false, and under compaction its writes commit a mid-page prefix (14 in 30 s at its offset) | tested on C; compiler output | S1 |
| A2 | too-strong assumption, doc | (ii) not provided by Linux, not observed (0 in 7.1·10⁸ aligned pages); the torn window includes dirty throttling and a fatal-signal exit; the not-uptodate path tears too | kernel source; tested on C | S1; reword |
| S1 | simplification | drop NoTear and use P1 (minibolt's checksum), or make the buffers heap-aligned and keep (ii) as a frequency claim | reasoned | — |
| C1 | none | start-order rule and `commitAll` hold under device reordering: 867 images, 0 violations | tested on C | — |
| D1 | none | readdir racing inserts/htree conversion: 0 duplicates in 12 runs | tested on C | — |
| D2 | none | `O_TRUNC` races covered | kernel source | — |
| D3 | doc-only | NoTear docs; README's P1 and "a killed process loses nothing" | read | reword |

## Scripts (`notes/axiom-review/fs-v2-r6/`)

Each makes its filesystem with `fs-config/mkfs-mount.sh` and refuses to run unless `check.sh`
passes; `sudo` where they touch devices.

- `addr/{main.go,go.mod,addr.sh}` (A1): `addr.sh /tmp/r6addr 200`.
- `tear/{main.go,tear.bt,run.sh}` (A1, A2): `run.sh WORKDIR SKEW WSIZE SECONDS`, with a compaction
  loop (`COMPACT=0` to omit). Runs: `run.sh /tmp/r6t 3144 4096 30`; `run.sh /tmp/r6a 0 65536 1200`;
  `run.sh /tmp/r6a 0 4096 600`.
- `reorder/{reorder.py,reorder.sh}` (C1): `reorder.sh meta|data WORKDIR SCENARIO 8`, which runs
  round 5's `meta.sh`/`data.sh` and then replays the same log with reordering.
- `readdir/{readdir.c,readdir.sh}` (D1): `readdir.sh /tmp/r6rd`.
