# Final review: the Linux file extension and the osfs examples (branch `fs-bytes`)

**Date:** 2026-11-11. **Reviewed:** branch `fs-bytes` at `83391b1ac7`.

- **The trusted semantics:** `GooseLang/Ext/Fs/{Impl,Tree,Paths,Lookup,Premises,FilteredSem,SemOk,AdequacyS,Tests}.lean`,
  `TrustedCode/{os,syscall}.lean`, `TrustedCode/golang_org/x/sys/unix.lean`. Round 8's fixes were
  re-checked; nothing was re-reviewed from scratch.
- **The example theorems and the definitions their statements use:**
  - `bboltfs/{Results,BootP1}.lean`
  - `crashlog/Results.lean`
  - `walfs/{Results,SegLogResults,DirSwapResults}.lean`
  - the Hoare specs `testMinibolt` and `testMiniboltConcurrent`
  - the Go programs `examples/osfs/{crashlog,walfs,bboltfs}/*.go`
- **The docs:** the Impl header, `notes/fs-semantics-v2.md`'s newest section, `notes/STATUS.md`
  "Known limitations", and `examples/osfs/semantics/`.

**Method.** The `axiom` skill, applied to a trusted semantics, with three checks:
- **Statements:** each statement compared with its version on `origin/lean`.
- **Lean, kernel-checked:** `lake env lean` on scratch files in `fs-final/`, against the built
  modules. They are untrusted checks and add nothing to the trust base.
- **P1 against real runs:** a Go enumeration (`fs-final/p1mix/`) of every meta-slot mix minibolt's
  runs can produce.

There was no new Linux experiment. No finding depends on a kernel behaviour that rounds 4-8 did
not measure on C.

## Verdict

**I found no unsoundness.** The things that need a fix are clarity and stale text. With those
fixes, the branch is ready for the user's review as the final artifact.

- **Round 8's fixes hold.** The trusted files are unchanged since the commit that fixed them
  (`05dc2a3fef`), except `AdequacyS.lean`, which is untrusted.
  - **R1-R3:** `Seek`, `Write` and `Read` each start with the closed-file panic. `Seek` returns
    `EINVAL` past `seekMax`. An empty `Write` is a "not modelled" panic.
  - **F4:** an `O_TRUNC` `Open` of a busy file is stuck in the step.
  - **F5:** `Mmap` no longer has the busy guard.
  - **F8:** `Stamp0` is in `CacheCand`, and `sectorWhole_reachable` is proved.
- **P1 holds in every real crash of `BootMinibolt` on C.** This is a fact, not only a
  low-probability assumption:
  - P1 holds trivially for every file the program does not change (`p1_untouched`, proved).
  - For `dir/db`, no byte-wise mix of the slot states minibolt can leave validates, except those
    states themselves. This was enumerated exhaustively for every txid up to the 1 GiB bound
    (P2 below).
- **P1 never makes the crash part vacuous.** From every reachable state, whenever the semantics
  has a crash, it has one that satisfies P1 (`p1_crash_exists`, proved).
- **The start hypotheses are satisfiable.** An empty root `/r` gives `FsInit`, `/r` is a root and
  `/r/db` names nothing (`fsInit0`, `db_none`, proved).
- **The statement changes since `origin/lean` are all fine.**
- **`SectorWhole` is used by no example.**
- **The axioms.** Every example theorem prints Lean's three plus Goose's names-only declarations.
  There is no `sorryAx` and no other axiom.

| # | severity | finding | where |
|---|---|---|---|
| P1a | (no finding) | P1 is stated for every file. It can never fail for a file the program does not change, whatever its bytes: every byte has one candidate, so every crash image is `valAt · 0`. Proved | `fs-final/P1Sat.lean`, `p1_untouched` |
| P1b | (no finding) | P1 is satisfiable at every crash of a reachable state. Keep the crash's tree and give every named file its last-sync state (`valAt · 0`, size `sizeLo`): that is a `MachineCrash`, and it satisfies P1 with `n = 0`. Proved | `fs-final/P1Sat.lean`, `p1_crash_exists` |
| P2 | doc / strengthening | P1 holds of real runs for a stronger reason than BootP1 and STATUS give. They give "a collision by accident". In fact, for minibolt's slot states no mix validates. 262144 pairs and 2.2 M mixes were enumerated, with 0 found. Neither the argument nor P1a, P1b is in the repository | `BootP1.lean:15-21`; `notes/STATUS.md:17-21` |
| D1 | doc (stale) | `examples/osfs/bboltfs/README.md` describes the first extension: `GooseLang/Ext/OsFs/...`, an older P1, "bytes lost by a failed sync", "allowed paths". `page.go`'s package doc says "the model's set of allowed paths is fixed" | `README.md:4,10,21,38-42`; `page.go:5-8` |
| D2 | doc (stale) | The walfs results' docstrings say "a crash keeps a prefix of the logged operations", "or all of them when only the process restarts", "`osTreeCrash_take`: the same after a restart", and "`DataGood` (…, clean)". The crash keeps a `Follows`-closed set, restarts are machine crashes, and `DataGood` has no "clean" condition | `walfs/Results.lean:4,11,15,330-336`; `SegLogResults.lean:11-12`; `DirSwapResults.lean:4-5,211-212` |
| D3 | doc (clarity) | The newest section of `fs-semantics-v2.md` names `OsFile.announceWrite/announceResize`, which round 7 removed. The sections after it ("Decisions" V4/V6, "The state", "The steps", "Crash") describe superseded models (sectors and dirty bits, a crash keeping `metaLog.take n`, a staged process restart) with no superseded mark: a reader meets three contradictory models | `notes/fs-semantics-v2.md:18, 80-215` |
| D4 | doc (stale) | Go and Lean comments name files and models that are gone: `GooseLang/Ext/OsFs` (`segdir.go:6`, `crashlog.go:2`); "the unsynced bytes of an extended file are arbitrary, D1" (`crashlog.go:8-12`; now zeros or the bytes written); "durable in order … N1" (`dirswap.go:16-19`); `OsFs/Names.lean` (`Paths.lean:4`, a trusted file's docstring) | as listed |
| D5 | doc (clarity) | The one client premise a theorem rests on, P1, is not in the semantics' own index. The Impl header's "Client premises" and `semantics/doc.go` list only `SectorWhole`. `AdequacyS.lean:3` puts `fsSemWithS` in `FilteredSem.lean` (it is in `Premises.lean`) | `Impl.lean:107-111`; `doc.go:55-57`; `AdequacyS.lean:3` |
| D6 | doc (minor) | walfs's "What is assumed" lists `Hinit_wp` and the `os.file` field facts. The statements also take `[os.Assumptions]`, and seglog takes `[golang_org.x.sys.unix.Assumptions]`. These are Goose's generated package facts, of the same kind as `package_sem`, but unnamed in the text | `walfs/Results.lean:19-21`, `SegLogResults.lean:15-16` |
| N1 | (observation) | Nothing in the repository proves that a `MachineCrash` exists from every reachable state (the tree part). Only the per-file part is proved (`crash_current`, `sectorWhole_reachable`). `p1_crash_exists` is relative to some crash. This is not a soundness question: fewer crashes only narrow what the theorems cover | `Tests.lean:23-27` |

## P1 (question 3)

The premise is `P1 st st'` (`BootP1.lean:52-57`). For every inode `i` with `f` in `st` and `f'` in
`st'`, and every slot `j < 2` whose page holds a byte of `f'`: if the slot read through the page
cache validates, then some `n` has each slot byte equal to `valAt (f.cand ·) n`.
`MachineCrash` keeps inode numbers (`Impl.lean:845-852`: `f'` is a `CrashFile` of the same
inode's `f`), so `f` is the right pre-crash file.

### Stated for every file: can it fail for another file?

No.
- A file the program has not changed since the last boot or sync has exactly one candidate per
  byte, `[(v, 0)]` (`ofDisk`, `synced`).
- So every crash image of it is `valAt · 0` at every byte, and P1's conclusion holds with `n = 0`
  whether or not its slot validates. That covers, for example, another bbolt database elsewhere in
  the roots' trees.
- Proved: `p1_untouched`.
- `BootMinibolt` opens only `dir/db` (`minibolt.go:411-441`, `Open`). After a crash every file is
  `ofDisk` again.
- So P1 restricts only `dir/db`. Stating it for every file loses nothing, and the doc's reason ("a
  checksum collision, holding of any") can be replaced by this exact one.

### True of real runs on C

For `dir/db`, the values a slot byte can take between two successful syncs come from at most two
slot states. Reading `minibolt.go`:

| who writes the slot | the two states |
|---|---|
| a new file, or `init`'s first `WriteAt` | zeros |
| `init`, slot `j` | zeros and `meta(j)` |
| commit `t`, slot `t % 2` | `meta(t-2)` and `meta(t)`, where `meta(t)` has root `t+2`, pgid `t+3`, freelist 2, pageSize 4096, flags 0 |

Why there are only two states:
- An `fdatasync` follows every slot write before the next one.
- A failed sync makes `init` return or marks the handle failed, and the boot program then only
  closes.
- `meta(t)` is a function of `t`: a retried commit `t`, after a crash that kept `meta(t-1)` as the
  current meta, writes the same `meta(t)`.
- A slot left torn by an earlier crash is itself a mix of the same two states. A mix of it with
  the next write is again a mix of the pair. It cannot rebuild `meta(t-2)`, because that would
  need the torn slot to equal `meta(t-2)`, which validates.

`fs-final/p1mix/main.go` enumerates, for every pair up to txid `2^18` (1 GiB / 4 KiB):
1. every mix of the first 56 bytes;
2. their FNV-64a;
3. whether a mix of the two checksum fields can equal it.

```
$ go run main.go            # go1.27.3, 1 s
pairs 262144 (txid < 262144), max differing bytes in [0,56) between commit metas 7,
first-56 mixes enumerated 2155072, validating endpoints found 524286,
validating mixes other than the endpoints: 0
```

524286 is every endpoint but the two all-zero ones, which do not validate, so the method finds what
it should. Every validating crash image of a slot is therefore one of the two states:
- the newer is `valAt · n` at the write's stamp, and the write announced all 4096 bytes of the page;
- the older is `valAt · 0`, the stamp-0 value.

A short write retried by Go's `WriteAt` loop splits the page between two stamps. `valAt` at the
later stamp still gives the whole new state.

So P1 removes no crash that Linux on C can produce in a `BootMinibolt` run, given the semantics'
device assumption: a byte is old or new, never garbage.

### Satisfiable from every reachable state, and not vacuous

`p1_crash_exists` (`fs-final/P1Sat.lean`, kernel-checked; axioms `propext, Classical.choice,
Quot.sound`):

```lean
theorem p1_crash_exists [GooseExts] {st st' : OsState} (hok : CacheOk st)
    (hc : MachineCrash st st') : ∃ st'', OsCrash st st'' ∧ P1 st st''
```

- **The witness:** `st'`'s tree, with every named file `ofDisk (valAt (f.cand ·) 0) f.sizeLo`.
- **Why it is a crash:** it is a `CrashFile` by `sectorWhole_durable`, using `Stamp0`, which
  `CacheOk` carries.
- **Why `CacheOk` is enough:** it holds at boot and after every step and crash (`Tests.lean`).

So P1 never removes all the crashes from a state, and the crash half of `bootCrashSafety` is not
vacuous.

Does the crash that keeps the file as it is (`crash_current`) satisfy P1?
- It does when every change landed whole: the page cache is then `valAt · stamp_max`.
- After a short landing, the page cache is a mix. For minibolt's states it does not validate (the
  enumeration), so P1 holds then too.
- In general, P1 excludes that state only if it validates.

### Compared with `origin/lean`

On `origin/lean`, P1 was:
- stated per path (`dir/db`);
- three disjuncts: durable; the page cache if every slot byte is dirty or lost; the result of the
  write in flight;
- restricted to slots wholly inside the image (`4096 i + 80 ≤ len`).

The new P1 accepts any one-stamp state, a weaker filter, so the theorem covers more crashes. Its
antecedent covers any slot whose page holds a byte (`4096 j < size`), which is broader. It is
still true of real runs by the argument above. `RawOk` needs it, for a crash that grows a short
file over a slot. The change is fine.

## `SectorWhole`

- **Unused:** no file under `Proof/` mentions it. Only `Impl.lean`, `Premises.lean` and
  `Tests.lean` do (and `fs-v2-r7/otrunc_race.lean`).
- **Satisfiable** in every reachable state: `sectorWhole_reachable` per file. `durCrash` above
  also satisfies it with `m = 0`, for the whole state.
- **False of C in general**, as the known limitation says.

## The hypotheses (question 4)

- **`FsInit` and the roots premise** (`fs-final/InitSat.lean`, kernel-checked). Take the state
  with root `/r` of inode 1, tree `{1 ↦ ∅}`, no file and `nextIno = 2`.
  - `fsInit0`: it satisfies `FsInit`.
  - `/r` is a root.
  - `db_none`: `lookup "/r/db" = none`.
  - Hence `BootCrashSafety`'s premises hold. crashlog's `Hnd`/`Hlog` hold trivially (nothing at
    `log`), and so do walfs's `Hnd`/`Hseg`, and dirswap's `SafeT j none` (`safeT_none`: no `wal`).
  - Each theorem requires `dir` itself to be a root (`RootForm`: an absolute canonical path). On
    `origin/lean`, `dir/db` was the allowed path. This matches the clients' use.
- **`Hinit_wp`** (all five theorems) is the package initializer's triple: postcondition `True`, or
  `pkgFacts` for bboltfs.
  - `Code/os.toml` translates no `os` variable, and its initializer only initializes `io`,
    `io/fs`, `syscall` and `errors`, so it is plausibly provable. It is unproved, as on `lean`.
  - bboltfs states it under `P1Ctx` (over the semantics with P1). The initializer makes no file
    call, so this is the same claim.
  - **Unchanged** from `lean`.
- **The field instances** (`os.file.FieldAssumptions`, `os.fileStat.FieldAssumptions`) are the
  struct-field steps Goose generates, written by hand for the trusted layouts. They are satisfiable
  as the generated ones are. **Unchanged.**
- **`Good`, `DataGood`, `SafeT`** are each satisfied by "absent" (`Good none = True`,
  `DataGood none`, `SafeT j none` with no `wal`). With the file present they say what the docs say:
  - crashlog `Good`: a nonzero flag means the data, and size `< 2^62`;
  - walfs `DataGood`: 8 bytes of data at 0;
  - bboltfs `Good`: `goodImg`, `RawOk`, on disk. It is not in the top statement: `Hnone` makes the
    first boot absent.
- **The thread bounds:**
  - bboltfs: `RealCrashThreadsBelow (2^30)`, as on `lean`;
  - the others: discharged by `RealCrashThreadsBelow.of_single`.

## The statements against `origin/lean` (question 2)

- **crashlog `crash_safety`:**
  - The path-keyed `files !! (dir/log) = some fo ∧ Good fo` became: `dir` a root, `dir/log` not a
    directory, and `Good` of the file it names, if any.
  - It is now over the unrestricted semantics (`fs_crash_adequacy`, no premise), where it was over
    the old `osFs_crash_adequacyT`.
  - The conclusion is the same three conjuncts.
  - Fine: a more general start state (any tree), and no crash filter.
- **bboltfs `bootCrashSafety` / `BootCrashSafety`:**
  - The semantics went from `osFsExtsSemanticsWith (P1 (dir/db))` to
    `fsExtsSemanticsWithS AnyStep P1`.
  - `AnyStep` is `True`, so the steps are exactly `FsStep`: `fsSemWithS`'s step is
    `FsStep ∧ True`, and `anyStep_keeps` holds.
  - The start: `dir` a root, `lookup (dir/db) = none`.
  - The conclusion is unchanged.
  - P1 as above. Fine.
- **walfs** (segdir, seglog, dirswap): new on this branch, with no `lean` counterpart. Each has
  the shape and hypotheses of crashlog's, over the unrestricted semantics.
- **`testMinibolt.spec`, `testMiniboltConcurrent.spec`:**
  - The precondition `osMeta (dir/db) 1 none` became the whole tree
    `osTree (DFrac.own 1) R V`, with `RootsOk R`, `dir` a directory and `dir/db` absent in `V`.
  - The postcondition `RET #true` is unchanged.
  - They are over any semantics with `FsSemOk`, which `fs_semantics` and `fsSemWithS` satisfy.
  - Fine. The caller must hand over the whole tree, which is natural for a program whose only
    thread owns the directory. Linked in `bboltfs/Link.lean` (`wp_testMinibolt`).
- **The axioms** (`fs-final/Axioms.lean`):
  - bootCrashSafety, walfs `crash_safety`, `seglog_crash_safety`, `dirswap_crash_safety`: 1130
    each; crashlog `crash_safety`: 390.
  - All of them are `propext`, `Classical.choice`, `Quot.sound` and Goose's names-only
    declarations: untranslated types with their `underlying`/`zero_val`, and untranslated
    variables' `.init`, of `os`, `syscall`, `x/sys/unix`, `sync`, `io/fs`.
  - No `sorryAx`.

## The docs (question 5)

The Impl header, round 8's fixed texts (`File.Sync`, `data_short_io.go`,
`data_inflight_changes.go`), the Premises docstrings and `STATUS.md`'s known limitations agree
with the definitions. The model reads as uniform:
- one crash rule, every byte any candidate;
- one sync rule;
- one stuck restriction, at most one change per file;
- the assumptions listed in one place with an example each.

The places that do not match are D1-D6:
- **The old models.** The most visible is D3: a reader of the design note meets the sector model
  and the prefix crash before the current rule. D1 and D2 likewise describe models the branch has
  removed: the bboltfs README, and the walfs result texts.
- **P1 is not where a reader looks for premises** (D5).

## Fixes proposed (not applied)

1. **P2.** Move `p1_untouched` and `p1_crash_exists` (`fs-final/P1Sat.lean`) next to `P1` in
   `BootP1.lean`, or into `Tests.lean` beside `sectorWhole_reachable`. Replace "Why it is a fair
   premise" with the exact argument: unchanged files satisfy it trivially; minibolt's slot holds
   at most two states between syncs; no mix of them validates, by enumeration (keep the script
   under `examples/osfs/bboltfs/` or the notes). Say the same in STATUS's known limitation.
2. **D1.** Rewrite README.md's P1 paragraph and paths, and page.go's "allowed paths" sentence.
3. **D2.** In the walfs docstrings, replace "prefix … or all of them when only the process
   restarts" with "a set of the logged operations closed under the journal's order (`Follows`);
   a restart is a machine crash", and drop "clean".
4. **D3.** Fix the newest section's names. Mark "The state", "The steps", "Crash" and V4/V6 as
   superseded, or move them to a history note.
5. **D4, D5, D6.** Update the stale paths, crashlog.go's layout reason and `Paths.lean:4`. Add P1
   to the Impl header's "Client premises" and to `semantics/doc.go` (a `premise_meta_slot.go`).
   Fix `AdequacyS.lean:3`. Name `os.Assumptions`/`unix.Assumptions` in walfs's "What is assumed".

## Files

- `notes/axiom-review/fs-final/P1Sat.lean`: `p1_untouched`, `durCrash_machine`,
  `durCrash_P1`, `p1_crash_exists`.
- `notes/axiom-review/fs-final/InitSat.lean`: `fsInit0`, `root0`, `db_none`.
- `notes/axiom-review/fs-final/Axioms.lean`: `#print axioms` of the five theorems.
- `notes/axiom-review/fs-final/p1mix/main.go`: the enumeration (`go run main.go [maxTxid]`).

Run the Lean files with `lake env lean <file>`, after `lake build` of `BootP1`, `Tests` and the
`Results` modules. They were up to date at `83391b1ac7`.

## Dispositions (2026-11-12, fork D1)

- **P1a/P1b/P2.** `p1_untouched` and `p1_crash_exists` moved into the build:
  `Proof/github_com/mit_pdos/etcd_grove/examples/osfs/bboltfs/P1Sat.lean` (imported by `Results.lean`,
  `#print axioms` of both there); `fsInit0`, `root0` and `db_none` into
  `GooseLang/Ext/Fs/TestsInit.lean`. `BootP1.lean`'s "fair premise" paragraph and STATUS's P1 entry now
  give the exact argument (the two-state pairs per slot between syncs, the enumeration in
  `fs-final/p1mix/`). A Go example for P1 (`examples/osfs/semantics/premise_p1.go`), indexed in
  `doc.go`, as CLAUDE.md asks of a trace-level assumption.
- **D1.** `examples/osfs/bboltfs/README.md` (the extension's files, the crash relation, P1) and
  `page.go`'s package doc (roots in place of allowed paths) rewritten.
- **D2, D6.** The walfs results' docstrings: a crash keeps a set closed under the journal order;
  restarts are machine crashes under the "Restarts" assumption; `DataGood` has no "clean"; "What is
  assumed" names `[os.Assumptions]` (and seglog's `[golang_org.x.sys.unix.Assumptions]`).
- **D3.** `notes/fs-semantics-v2.md`: a reading guide (the current model is its first section and the
  Impl header); the newest section's names fixed (`OsFile.announce`/`land`, `OsChange.ofWrite`/
  `ofResize`); V4, V6, sector atomicity and no mixed writeback marked superseded in place; "The
  state", "The steps", "Crash", "After the soundness audit", "The program logic" and "Phases" moved
  to `notes/fs-semantics-v2-history.md`.
- **D4.** `segdir.go`, `crashlog.go` (the flag's reason, now with candidates), `dirswap.go` (the
  journal order and `commitAll`) and `Paths.lean`'s docstring fixed; the walfs translation
  regenerated (only `go:` line markers changed; crashlog's and bboltfs's are unchanged, their package
  docs are not copied).
- **D5.** The Impl header's "Client premises" and `semantics/doc.go` list P1 next to `SectorWhole`;
  `AdequacyS.lean` points to `Premises.lean`.
- **N1.** Open: a whole-state crash from every reachable state needs two invariants `CacheOk` does not
  carry (every committed entry inside the log; every file the tree names present). Recorded in
  `notes/STATUS.md`; it narrows what the theorems cover, not their soundness.
