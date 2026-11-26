# T1 (bbolt crash premise): honest alternatives to (A‴) that do not rely on gc alignment

**Date:** 2026-11-26. **Revision:** `origin/etcd-safe-crash-r6/2026-11-26` (`8cdf5ff75f`). bbolt fork pin
`2f6fcfff`. **Method:** the `axiom` skill (`.claude/skills/axiom/`). Simulation: three Go test files (go1.27.3,
not in the repository, all PASS; output quoted below). The option (C★) is reviewed in detail in
[cstar-independent](cstar-independent.md).

## Verdicts

| Option | Verdict | Relies on gc? |
|---|---|---|
| (2) BoltCrashWhole scoped to files named `db`, no fork change | **SOUND WITH FIXES, but only with gc alignment** (the same reliance as (A‴), on bbolt's buffer only) | **Yes.** Without alignment it excludes real images by a byte coincidence, not an FNV collision. Some are harmful; see (b). |
| (C) as written: Open rewrites an invalid slot with a valid meta, then syncs | **UNSOUND** as a way to remove the gc reliance | It does not help: the repair write tears over the residue in the same way. |
| (C0) Open zeroes an invalid slot, then syncs | **SOUND WITH FIXES** for single-cut tears; **UNSOUND** for composite tears (zeros can complete a dead checksum, 1/256 per byte) | No, but it has a residual gap |
| **(C★) Open "poisons" an invalid slot (bitwise complement of the checksum its fields need), then syncs, plus the `db` scope of (2)** | **SOUND WITH FIXES**: exact for the repair write; every other case only up to an FNV-64a coincidence among bbolt-written bytes | **No.** It also does not rely on the tear shape (any per-byte mix of the two candidates) or on sector atomicity |
| Sector-sized meta write; stronger or txid-keyed checksum; meta buffer from an anonymous `mmap` | **INFEASIBLE** as routes: either the reliance stays, or the on-disk format changes, or new trusted semantics is needed | n/a |
| Modelling buffer alignment in GooseLang/Go | **INFEASIBLE / not spec-conformant**: the spec gives `[]byte` alignment 1; assuming 4096 is gc | n/a |
| (4) Leave T1 open | Honest, but the crash theorem is not closed | n/a |

**Ranking:**
1. (C★) + `db` scope.
2. (2) alone, as an interim with the gc reliance documented. This is narrower than (A‴): no WAL and no write-shape conditions.
3. (A‴).
4. (4).

(C) and (C0) are rejected.

## (a) Can the crash relation name the db file? Yes, at the cost of W1

- **Paths and entries.** `MachineCrash` exposes:
  - the roots (`st.fs.roots`, path and inode);
  - the pre-crash tree (`OsState.tree`);
  - the **crashed durable tree** `st'.fs.treeDur` with `Tree.entry` (`GooseLang/Ext/Fs/Impl.lean:1319`, `GooseLang/Ext/Fs/Tree.lean`).

  W1 already scopes itself this way: the `.wal` entries of every directory of `st'.fs.treeDur` (`Proof/go_etcd_io/etcd/server/v3/storage/wal/W1.lean:303`). The db form is the same: `DbNamed st' i := ∃ j, st'.fs.treeDur.entry j "db" = some (.file i)` and `BoltCrashDb st st' := BoltCrashWhole (DbNamed st') st st'`. A full-path form (root `memberDataDir n` / `member` / `snap` / `db`, by `walk`) is also expressible, but it is not needed. The reason: a file nobody wrote since its last sync has one stamp-0 candidate per byte, so the premise is trivially true of it. Only files that are written are constrained.
- **Use the crashed tree, not the pre-crash one.** Consider the snapshot install's rename of `.snap.db` onto `db` while the old backend still commits ([c-i1-nopath](c-i1-nopath.md)). Whichever inode the crashed tree names `db` is the one bbolt reopens, and the one `dbCrash` needs. The pre-crash tree names the new inode even when the crash drops the rename.
- **Inode reuse.** Inode reuse does not arise. Model inodes are never reused: `takeIno` only increments, `MachineCrash` keeps `nextIno`, and `FsInit` puts every inode below it. Candidates belong to the inode, so a rename moves nothing.
- **What writes a `db`-named inode in etcd's runs.** Only bbolt's syncing writes (`dbOpts`):
  - The data directory is an empty root at start (`etcdWalAreasInit`, `Proof/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/WalAreasInit.lean:36`), so there is no crafted initial db.
  - The `.snap.db` file is synced before it is renamed.
  - Defrag's `NoSync` temporary db is synced before its rename onto `db`: the etcd fork's `finishDefrag` calls `tmpdb.Sync()`, then `Close`, then `os.Rename`, then a syncing `bolt.Open`. That closes the earlier open item on `NoSync` defrag for the scoped forms.
  - Client bytes never reach a slot.
  - The WAL drops out of scope, and with it the WAL-payload attack on the any-inode form of the premise (a client-chosen WAL payload torn by mechanism A).
- **Wiring cost.** `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/crash/MemberCrash.lean` already has the name fact at the `dbCrash` call: `hdb : V'.now.entry J "db" = some (.file i0)`, from `memberDbNamed`/`BackendImage`. `dbCrash`'s `hQ` and `hN` would be restated as "`Q` gives `BoltCrashDb`" and "the crashed tree names `i0` as `db`". `dbCrash` is a trusted axiom, so that needs sign-off. The axiom asks less of `Q`, so it becomes stronger, and its eventual proof discharges the naming.

## (b) Is (2) sound without gc alignment? No: a byte coincidence, not a collision

The following facts of bbolt's crash-mode meta writes hold:
- in crash mode, a meta write is one `writeAt` of exactly page j (`tx.go:601–625`);
- the write is the file's first change since its last sync;
- `init` writes its metas over synced zeros (`db.go init`).

Under Go-spec-only alignment, `make([]byte, 4096)` may straddle a memory page. So mechanism A can cut the write at any byte, as the e2e run measured (`notes/axiom-review/fs-v2-r6/e2e/README.md`): a new prefix, the rest old.

**Single crash, old slot a valid meta V.** The image is `N[0..c) ++ V[c..64)`.
- For c ≤ 56 it validates only if `FNV-state(N[0..c)) = FNV-state(V[0..c))` with `N[0..c) ≠ V[0..c)`. Each FNV-1a step is a bijection of the state, so the shared suffix cannot cancel a difference. That is a genuine prefix collision.
- One differing byte never collides.
- From bbolt's fixed 16-byte header, the 3 low bytes of a pgid are injective (`TestInjectiveLow3`, exhaustive over 2^24).
- For c > 56 it validates only if it equals N.
- Init metas over zeros: no cut validates (`TestInitMetaOverZeros`, exact).

So for one crash, (2) is "true up to an FNV-64a collision". That is the docstring's claim.

**Double crash, the case the docstring misses.** bbolt does not repair a torn slot, so the torn invalid residue R becomes the slot's stamp-0 content after the crash (`ofDisk`).
- Crash 1 tears A (txid t+1) over B (t−1) at cut c1. That gives `R = A[0..c1) ++ B[c1..)`, which is invalid.
- Generation 2 reopens at t and commits N (txid t+1 again) into the same slot.
- Crash 2 tears N over R at c2 ≤ c1. The image is `N[0..c2) ++ A[c2..c1) ++ B[c1..)`. It **equals B byte for byte** whenever N and A agree with B on `[16..c1)`. For c1 = 17 that is just "N's root pgid has B's low byte", which happens 1 time in 256.
- This needs no collision: B carries its own checksum. B is no candidate of the slot (stamp 0 is R, stamp n is N), so **BoltCrashWhole excludes a real image.**
- Simulation (`TestPrefixTearsNoMixedValidates`): 52,000,000 single-cut images over realistic histories with residue kept. 14 rebuild an older meta of the slot, and 0 validate any other way.
- This rebuild is **harmless for bbolt.** B's txid t−1 is below the other slot's t, so Open ignores it. That is why no false etcd triple follows, but the premise is false of the image.

**The harmful version (the revival of a dead commit) under a composite tear.** Single-cut tears cannot produce it: in `TestRevivalPerByteVsPrefix` the per-byte model revives 717 of 200,000 times and the prefix model 0 times. But consider a short copy at k (mechanism A) after which writeback DMA starts on the now-dirty folio. C has `stable_writes = 0`, so `folio_wait_stable` does not wait, and the retried copy races the DMA and can overtake it at x. That yields `new[0..k) ++ old[k..x) ++ new[x..)`.
- With k ≤ 16 and x inside the checksum, the image is "dead fields plus new checksum bytes".
- If crash 1 tore only the checksum, the image validates as the dead t+1 with probability 1/256. Open picks it over pages generation 2 reused.
- `TestTargetedComposite` (70,478 residues, every composite shape):

  | Policy | Real images BoltCrashWhole excludes | Harmful revivals |
  |---|---|---|
  | none | 141 | 136 |
  | (C) copy | 120 | 119 |
  | (C0) zero | 4 | 4 |
  | **(C★) poison** | **0** | **0** |

- **Caveat:** the composite shape follows from kernel mechanics (`generic_perform_write` commits a short copy on an uptodate folio, then retries), but it has not been measured. The single-cut residue rebuild above does not depend on it.

**Also unmeasured here (later measured as a stall of the copy under page migration: [cstar-independent](cstar-independent.md) (e)), and it bears on (A‴) too.** A page-aligned source does not strictly exclude mechanism A. A migration that unmaps the source page *during* the copy (TLB-shootdown IPI, `rep movsb` resumes, then faults) gives a short copy at an arbitrary byte. the e2e run's 7 tears were all at source page boundaries, the large window. The mid-page window is tiny but not zero. So "a bbolt meta page does not tear on C" (`CrashPremise.lean` header) is an argument from the measured shape, not a guarantee. (C★) does not need it.

**(2)'s exact trust:**
- Today: (A‴) is scoped to every inode, with conditions; true of etcd only under gc alignment of both bbolt's and the WAL `PageWriter`'s buffers.
- With (2): scoped to `db`-named files, no shape conditions; true of etcd's runs only under gc alignment of bbolt's `make([]byte, 4096)`. With unaligned buffers, residue rebuilds and (if composite tears are real) revivals are excluded. A known limitation (`notes/STATUS.md`). It is false for a program over `etcdFsSem` that writes a file named `db` with chosen slot bytes or from a skewed buffer. Fixes:
  - restate `dbCrash`'s `hQ`/`hN` (sign-off);
  - prove `etcdCQ_exists` (the fix named in [cstar-independent](cstar-independent.md): `W1Sat`'s hypothesis does not hold of `durCrash` for files shrunk since their sync);
  - correct the docstring. "Up to an FNV-64a collision" is wrong without gc: the failure is a byte coincidence.

## (c) Routes that remove the gc reliance

### (C) as written: Open rewrites an invalid slot with a valid meta, then syncs
- **Today:** the residue survives a reopen.
- **With (C):** the residue survives until the repair write, and **that write tears over it.** A repair meta M sharing B's prefix rebuilds B (single cut). With composite tears, the dead fields plus M's checksum bytes revive t+1 at 1/256 (119 harmful in the table).
- **Verdict: UNSOUND** as a gc-removal; it adds nothing over (2).
- Upstreamable as a robustness fix, but it does not fix this.

### (C0) Open zeroes an invalid slot, then syncs
- **What changes:** single-cut tears over residue never validate, because bbolt's magic bytes `ED DA 0C ED` are all nonzero. Commits then always write over a whole valid meta or zeros.
- **The gap:** with composite tears, zeros complete a dead checksum whose missing bytes are 0 (4 harmful in the table).
- **Verdict: SOUND WITH FIXES** only under a single-cut premise, which is itself unmeasured as a guarantee. Not recommended.

### (C★) Open poisons an invalid slot, then syncs, with the `db` scope of (2). Recommended.

**Fork change in outline.** In `Open`, writable and `!NoSync`, at the point where 2f6fcff's early `fdatasync` runs (after `init`/`getPageSize`, before `mmapUnlocked`):
1. For j in {0, 1}: `ReadAt` page j, as `getPageSizeFromFirstMeta` already does.
2. If `Meta.Validate()` fails, set its checksum to `^m.Sum64()`: the bitwise complement of the FNV-64a its own 56 field bytes need.
3. `writeAt` the page back.
4. Then call `fdatasync` once.

About 25 lines of ordinary Go, using only bbolt's existing `pageInBuffer`/`Meta` accessors and no new unsafe. Add a robustness test with an injected torn meta, in the style of the 004c930 test.

**Why it is exact for the repair.** R and the poisoned page W have identical bytes 0..55. Every checksum byte of W differs from the byte those fields need, and R itself is invalid. So **no per-byte mix of R and W validates.** This holds for any shape, with no probability involved.

After the sync, every later meta write lands over one of:
- a whole valid bbolt meta, written and synced;
- `init`'s zeros;
- a poisoned page.

**The premise's argument then needs:** one change since the sync (bbolt's discipline), with the two candidates interleaved in any way. It needs no alignment, no single cut, no sector atomicity and no gc. A validating image that is not one of the two candidates by value then needs an FNV-64a coincidence among bbolt-written bytes. Over a poisoned page, a dead-fields image needs N's whole 64-bit checksum to equal FNV(R's fields). Simulated: 0 excluded and 0 harmful in both the single-cut and the composite runs.

**Semantics premise:**
- Today: `etcdCQ := W1`, with `dbCrash`'s `hQ` asking BoltCrashWhole for any inode (not given).
- With (C★): `etcdCQ := W1 ∧ BoltCrashDb`, the statement unchanged and the scope being the files the crashed durable tree names `db`.

**Exact trust:**
- **Probabilistic, already in the docstring:** "a mix of two bbolt-written slot contents validates only by an FNV-64a coincidence". There are at most 2^d mixes for d differing bytes, so under the per-byte model about 2^(d−64) per torn write. Client influence is only through pgids, and steering bbolt's allocator to a precomputed colliding pair is not excluded by any argument here, only impractical.
- **Environment, already stated:** C, no failed writeback, restarts after `sync`.
- **What holds for etcd's runs:** `UnsafeNoFsync = false` (`dbOpts`), empty data directories at start, defrag's pre-rename sync.
- **Known limitation:** false for a program that writes a `db`-named file with chosen bytes, or one that starts on a crafted db.

**Excluded real images:** none for etcd's runs beyond the stated FNV coincidence. For crafted files it is false, but those are outside `etcd_safe` by `etcdWalAreasInit`.

**Cost:**
- fork change, test, Goose retranslation;
- update `Open`'s in-process proof for the extra read/validate/write/sync, letting the abstraction of the file change an invalid slot's bytes;
- the crash proof's slot invariant: stamp-0 slot content is a valid meta, zeros or poisoned;
- restate `dbCrash` (sign-off);
- `etcdCQ_exists` and docstrings.

Estimate 3–5 days plus a fresh review. It rides with the other `Open` fork changes (P13, P13b, meta-tails (iii)).

**Upstreamable:** plausibly, as defence in depth against torn meta writes ("a torn meta can never validate later"). Upstream bbolt lacks the fork's `needsInit` and early sync, so it would go with them. The motivation (no tears under gc, except mid-copy migration) is thin, and upstream may decline it.

### Other fork changes
- **A sector-sized (512- or 80-byte) meta write.** The source can still straddle a page boundary, because Go code cannot control alignment without addresses. The reliance stays.
- **A stronger or txid-keyed checksum.** The checksum already covers the txid (bytes 48..55). Another hash changes the on-disk format, so it is not upstreamable, and it is still probabilistic.
- **A meta buffer from an anonymous `mmap` (page-aligned by the kernel's contract, no unsafe).** It needs new trusted semantics: writable anonymous mappings, which the model treats as stuck today, and `pwrite` recording that its source is aligned. Mid-copy migration still cuts. Unlikely upstream (portability).

### Modelling alignment in GooseLang
- Spec-conformant only as "an arbitrary address". That gives the proof nothing for bbolt's buffer, since every address is possible.
- Assuming 4096-alignment is gc.
- It would need addresses in GooseLang's abstract `Loc` and in the file extension's write steps.
- **INFEASIBLE.**

## (d) (4) Leaving T1 open

`etcd_safe` stays `etcd_safe_of_boot` from the named hypothesis `EtcdBootC`. Its member crash law takes `hA1` ("the run's crash relation gives BoltCrashWhole at the db inode"), and `etcdCQ = W1` does not give it, so `EtcdBootC` cannot be discharged. The closed crash theorem is then not proved. What is missing is the claim that, after any power loss, each member's bbolt file holds the data of its last or previous commit (C-I1's `dbCrash` conclusion). Everything a restarted member derives from its backend rests on that claim: the consistent index, applied state and membership that it recovers and replays the WAL from. Raft safety across member crashes is therefore proved only for runs in which bbolt's meta slots never come back as a validating mix that is no single write's. The no-crash theorem `etcd_safe_nocrash` is unaffected.

## Attacks and checks tried

| # | Check | Result |
|---|---|---|
| 1 | Can `etcdCQ` name `db`? | Yes: entries of `st'.fs.treeDur`, as W1 names `.wal`. No inode reuse. `MemberCrash` already has the `db` entry fact. |
| 2 | Defrag's `NoSync` db under the `db` scope | Synced before the rename (etcd fork `finishDefrag`). No residue. |
| 3 | Crafted initial db | Defeats every scoped form when tears happen (crafted slot bytes predict N). Excluded in `etcd_safe` by `etcdWalAreasInit` (empty data directory). |
| 4 | Init metas over zeros, every cut | No mixed image validates (exact). |
| 5 | Single crash, prefix tear over a valid meta | Validates mixed only by an FNV prefix collision. Single-byte differences and 3-byte pgid differences are injective. |
| 6 | Double crash, prefix tears, residue kept (2) | **The older meta B is rebuilt by a byte coincidence** (14 in 52M). BoltCrashWhole excludes it. Harmless to bbolt. |
| 7 | Revival of a dead commit, per-byte vs prefix | Per-byte 717/200,000 (about 1/256); prefix 0. |
| 8 | Revival under a composite tear (short copy, then DMA racing the retry) | Harmful revivals: none 136, (C) 119, (C0) 4, (C★) 0. The shape is from kernel mechanics, not measured. |
| 9 | Mid-page short copy on an aligned source (migration during the copy) | Possible from kernel mechanics, not measured. It weakens "a bbolt meta page does not tear" under gc too. |

**Worth measuring:**
- a dm-log-writes run with `STABLE=0` that forces a short copy (a skewed source) on a single meta-sized write while writeback runs, looking for `new|old|new` slot images;
- a forced-migration run on a page-aligned source.
