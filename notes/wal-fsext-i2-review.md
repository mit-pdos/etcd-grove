# Review of the I2 design (concurrent metadata calls, blind dfds, region ownership over `fsExt`)

**Reviewed:** `/home/ubuntu/.claude-E/jobs/af0ee947/tmp/i2-design.md`, which is identical to the
committed `notes/wal-fsext-i2-design.md` (58639fff75). **Checked against:** worktree `wal-fsext`,
`HEAD` = `a7ca666d88`. `HEAD` moved during the review: it now includes I1 (7855c288ec, 497080aa57),
and some of the design's line references and its §2.1 note on `γcom` are stale because of that
(finding m1). Semantics read: `GooseLang/Ext/Fs/{Impl,Tree,Paths}.lean`. Logic read: `Ghost`,
`TreeGhost`, `TreeSpecs`, `TreeSpecsMeta`, `CrashFiles`, `Crash`, `CrashTok`, `TreeCommit`,
`TreeCrashCommit`, `LinuxFs/Proof/os/CrashFile.lean`, `LinuxFs/TrustedCode/os.lean`. Go read:
`wal.go` (Create, renameWAL, cleanupWAL, cut, Close), `file_pipeline.go`, `fileutil/purge.go`, and
Go 1.27's `os/removeall_at.go`.

Nothing was built and no `.lean` file was checked: everything below comes from reading the code.

## Verdict: READY WITH CHANGES

I found no soundness counterexample. I tried each scenario the brief lists (below), and each is
either excluded by the claims and `osCallPerm`, or allowed by the semantics and correctly described
by the specs. `closed_cut`, the theorem everything rests on, also holds up under a paper argument
(§S4). The changes needed are about provability and fitness:

- the `os`-level shared specs must have a shape a crash invariant can use;
- the server's purge cannot be verified without the lock model (I5), and the design says otherwise;
- a few specs are missing the resource their proof needs to tell which mode the state is in;
- the design must be updated for I1, which has landed.

## Soundness: the scenarios tried

**S1. Concurrent calls in different regions.** Every step is one atomic `IsFsStep` case.

- Each step resolves its path when it runs (`OsState.lookup`, Impl.lean:454; `Open` :601-621;
  `Rename` :768-778).
- A spine (`osPathS`) holds fractions of the claim on each component. Changing one of those names
  needs the whole claim, so while the step is in flight nobody can change the path's resolution.
- Every entry a step logs writes only its footprint (`MetaOp.apply`, Tree.lean:76-84). `mkdir`'s
  extra write `<[j' := ∅]>` is to a fresh inode. So other claims' `cur` stays the same.
- Directory reads: `note` (Impl.lean:480-487) clears bits only for `touched` names, and `touched` is
  contained in the footprint. So `PhOkS` survives every operation that does not touch `N`.
- No interleaving I tried gave a claim holder a stale `cur`.

**S2. Rename and rmdir across regions.**

- A rename from `(jA,a)` to `(jB,x)` needs both whole claims, so one region must hand its claim to
  the other.
- An rmdir of `J` needs `osNames J (.except []) 1`. `NamesCoh` makes the claims under `J` a
  partition of its names, so this excludes every other holder, including a reader's fraction.
- A directory rename needs the whole claim on `(j,bs)`. That excludes every spine through it.
- The textual `¬ IsUnder s t` (Impl.lean:574) follows: a target spine through `(j,bs)` would need a
  fraction on top of the whole claim, which is invalid.
- Claims on the moved directory's own names are keyed by inode, so they stay correct.

**S3. The per-name premise `h.next ≤ s`.**

- *It is sufficient for `PerSlotSeq`.* `h.ents` lists every entry meeting `(j,N)`, so the new
  entry's previous overlapping entries all lie below `h.next ≤ s`. `Follows` holds as soon as
  `y < x.start` (Tree.lean:109-111).
- *The footprints are the right ones:*
  - `mkdir`'s `(J,*)` keeps a kept operation inside `J` from outliving a dropped `mkdir`;
  - `rmdir`'s `(J,*)` makes a kept `rmdir` find `J` empty;
  - rename-over-directory's `(J_old,*)` does the same for the replaced directory;
  - a moved directory's names need no footprint, because inodes key them.
- *A client can check it:* `osNames_next` gives `osLogLb h.next`, and `CallBeginS` gives `n ≤ s`.
  The `os` models call `CallBegin` right before the step (os.lean:563-576, :601-615), with the claim
  held whole across the gap, so no client ever states the premise itself.
- I re-checked the necessity counterexample of §4.3 against `MachineCrash` (Impl.lean:873-885). The
  kept `{x}` leaves `f` in an unreachable `J`, which violates `TreeWf` clause 2 (Tree.lean:142).

**S4. `closed_cut`, and the crash claim "R-closed plus the commit bound".**

My paper argument for it goes as follows.

1. `DirRenameExcl` holds: a directory rename steps with no other call in flight (Impl.lean:771),
   which is enforced by `osCallPerm 1` against `callResS`. So every later entry `z` has `x < z.start`.
2. Every kept entry therefore forces every earlier directory rename to be kept. The kept directory
   renames are exactly those below `max K`.
3. Mkdirs and rmdirs only add or remove leaves. A dropped `mkdir` takes with it every operation
   inside its directory (footprint `(J,*)`). A dropped `rmdir` leaves `J` under a live parent: a
   kept `rmdir` of the parent would overlap the dropped one on `(p,b)` and force it.
4. So the replayed directory structure is acyclic. Each node sits at the end of a per-slot kept
   prefix, so it is named once. Every named file is in `files`, which only grows until a crash.

Claim A (projection), Claim B (no hidden chains, using `start ≤ index`) and Claim D (`committed` is a
prefix: Impl.lean:504-506, reset at :875) all check out. `RegionCrashed`'s closure clause
`y < (ent cl x).start` is `Follows` restricted to `idx cl`. Claim C (tightness) checks out as well,
but soundness does not depend on it.

**S5. DirSync from a shared fd.** `DirSync` (Impl.lean:727-730) commits `y < metaLog.length` from
any directory fd, removed ones included. So `osLogLb n` implies the entries below `n` are committed
on `e = 0`. This is sound. The spec as written cannot be proved, though (M3).

**S6. The switch at `CallBegin`.** `osTree 1 R V` excludes every legacy call and directory fd:
`callRes` and `rdRes` hold `γd` fractions (Ghost.lean:889-903), and with them `TreeCoh.fds` gives
`proc.dfds = ∅` and `TreeCoh.calls` gives `proc.calls = ∅`. Its log is `Sequential`, which implies
`PerSlotSeq` and `DirRenameExcl`. The switching call's start is `|V.2|` (Impl.lean:723). The switch
is sound.

## Findings

### Blockers

None.

### Major

**M1. The `os`-level shared specs are planned as Hoare triples, but a crash invariant holds half of
each claim (fitness).**

- *What the design says.* §4.2 says "the library's invariant holds half of each claim, and the
  holder thread the other half". §3 says the `os`-level counterparts are each "a second triple,
  `specS`".
- *Why that cannot work.* `os.Rename`, `os.Remove`, `os.OpenFile` and `Mkdir` are not atomic. They
  make an `LstatDir` call, then the step, inside `EINTR` loops (LinuxFs/TrustedCode/os.lean:563-576,
  :601-615). So the client cannot open its invariant around a plain triple that takes
  `osNames … 1 h`. The claim changes only at the one inner step that logs an entry, and the
  invariant's half must be updated at exactly that point.
- *Who it blocks.* The WAL's cut rename and the pipeline's create of `N.tmp` both write claims whose
  half is in `walInv`. The existing precedent, `LinuxFs/Spec/os/Crash.lean`, solves this with
  crash-aware specs parametrized by `cfInv`, which open it around each extension step.
- *Fix.* State each mutating `os`-level `specS` either as a logically atomic spec or in crash-aware
  form, and say which in the design:
  - *logically atomic:* an atomic update over `osNames j N 1 h`, committed at the logging step with
    `h' ∈ {h, h.log …}`, and aborted at the steps that do not log (`LstatDir`, failed attempts);
  - *crash-aware:* parametrized by a client invariant and a `Good` obligation on every `h'` the call
    passes through, as `Spec/os/Crash.lean` does.

  The FS-level specs can stay as they are, since each is one atomic step.

**M2. The server's purge is still unprovable, and §3 says it is covered (fitness).**

- *The design's claim.* §3 says the read spec "suffices … for purge (FU/purge.go:60, which locks
  and re-checks what it finds)". §4.1 argues that "the kept unlinks form a prefix of purge's".
- *What purge does.* `purgeFile` (purge.go:55-90) runs `readDirWithSuffix`, then for each old name
  `TryLockFile`, then `os.Remove`. It re-checks nothing. Its safety, never unlinking a live segment,
  comes entirely from the OFD lock. `Flock` and `OfdLock` return any errno (Impl.lean:684-686,
  :837-838).
- *Why the design cannot prove it.* `wp_osUnlinkS` needs `osNames j (.only [seg]) 1 h`. The purge
  goroutine can only get that claim if the WAL handed it over when it released the segment
  (`ReleaseLockTo`). Purge cannot tell whether that happened: a successful `TryLockFile` tells the
  logic nothing.
- *There is also a second gap.* `os.Remove` falls back to `rmdir` when the unlink fails
  (os.lean:601-615). That needs a no-effect `Rmdir`-of-a-file spec, which §3 does not have (m4).
- *Fix.* Tie purge to I5 (plan §0 item 3; plan :28-31, :333). With a lock model, the WAL parks a
  segment's whole claim in a pool keyed by the lock state when it unlocks it. A successful
  `TryLockFile` then lets purge take the claim. Until then:
  - say in §3 and §4.1 that purge's unlinks are verified only once I5 lands;
  - keep the §4.1 re-argument (it is correct given the claims);
  - delete "which locks and re-checks what it finds".

**M3. Several shared specs lack the resource that tells their proof which mode the state
interpretation is in (provability).**

- *Telling the modes apart.* §2.1 makes a legacy fragment refute shared mode. Nothing makes a shared
  resource refute legacy mode. In the legacy branch (`treeWorld … as now`), the authorities of
  `γs`, `γdfS`, `γcS` and `γperm` are not mentioned, so a shared step's proof cannot discharge the
  legacy case. It also leaves unsaid where the switch's `osCallPerm 1` comes from.
  *Fix.* The legacy branch must own:
  - `gAuth γdfS ∅`, `gAuth γcS ∅` and a junk `γs` authority with its whole fragment;
  - the `γperm` token, whole. Every fraction then refutes legacy mode, and the switch hands the
    token out.
  `γn` must also be an `OsGS` name or a parameter of `osNames`. It is used by `osNames` but missing
  from the list of new names.
- *The DirSync spec.* `wp_osDirSyncS` takes `osLogLb n` without `osSharedInv R`. The authority of
  `γlen` sits in that invariant (§2.2), so the step cannot learn `n ≤ |metaLog|`.
  *Fix.* Either add `osSharedInv R` and `↑osShN ⊆ E` to the spec, or keep `γlog`'s authority in the
  state interpretation's shared branch. Since `osNames_next` is a plain fancy update, the first is
  simpler.
- *The shared crash fact.* In §4.2 the shared `crashRest` fact
  `⌜TreeCrashedC Vs V' ∧ … ∧ [0, c) ⊆ S⌝` uses `S` outside the `∃ S` of `TreeCrashedC`.
  `crashRest_region` needs the same `S` for every claim and for the commit bound.
  *Fix.* Write it as `∃ S, Closed Vs.2 S ∧ (∀ y, S y → y < |Vs.2|) ∧ V' = … ∧ (∀ y < c, S y)`.

**M4. Directory-rename exclusion is global, and the design does not say who holds the permission
in the composed server (fitness).**

- *What is needed.* Create needs `osCallPerm 1` twice: at `renameWAL`'s `os.Rename(tmpdirpath,
  w.dir)` (wal.go:333), and on the error path at `cleanupWAL`'s rename to `dir.broken.*` (:300),
  plus `renameWALUnlock`'s retry (:356).
- *Why it holds today.* At :333 the pipeline has not started yet (it starts at :340). At :300,
  `w.Close` → `fp.Close` waits on `errc`, so the pipeline has exited. So the code does meet the rule.
- *What the proof needs.* The pipeline's fraction comes back through `errc`'s close. Every other
  library in the process (bbolt at bootstrap, the snapshotter) must have returned its fraction to
  whoever calls `wal.Create`.
- *Fix.* Add a short "permission protocol" paragraph covering three points:
  - where the top level keeps `osCallPerm`;
  - that libraries hold a fraction only during path calls, or park it in their invariant;
  - that `Create`'s spec takes `osCallPerm 1`, and that the pipeline gives its fraction back on
    `errc`'s close.

  Long-term option, a trusted change with its semantics example: let `CallBegin` take its path(s),
  and make a directory rename stuck only while a call whose path walks through the source is in
  flight. Claims already exclude that case, so the global permission would disappear.

### Minor

**m1. Stale against `HEAD` (I1 landed).**

- `γcm` is already in `OsGS` (Ghost.lean:575).
- `commitRes` is inside `treeCtx` (Ghost.lean:961-967) and depends only on `st`, so factoring it out
  of the mode split is mechanical.
- `crashRest` now carries `crashCommit` (CrashTok.lean:169-188), whose fact is the prefix-shaped
  `TreeCrashedLb` (TreeCrashLb.lean:20). It needs a shared form next to `TreeCrashedC`.

*Fix:* use I1's `osCommitLb` instead of a new `osCommitLbS`. `wp_osDirSync_lb` (TreeCommit.lean:138)
is the legacy counterpart. Refresh the line references; for example, `crashRest` is now at
CrashTok.lean:177.

**m2. The switch is tied to `CallBegin`.** Every path call goes through an `os` model, so the
program's first shared call needs a "switching" variant of an `os`-level spec. *Fix:* make the
switch a combinator around any extension step: `osTree 1 R V -∗ (shared resources -∗ WP e) -∗ WP e`,
for `e` an `ExternalOp fsExt`, proved in `wp_fs_stepM`. Then the top level switches with any call,
for example its first `os.MkdirAll`. Also, `osCallPerm (1 - q)` needs `q < 1`, or should return
`osCallPerm 1` from which the caller splits.

**m3. Blind reads with no claim.**

- Purge's `readDirWithSuffix`, and `wal.Exist` before the WAL owns its directory, read with no claim
  on that directory.
- `wp_osDirReadNextS` requires `osNames j N dq h`.
- An empty claim `.only []` cannot be made fresh: two holders of key `(j, .only [])` would be
  invalid.

*Fix:* either add a claim-free read spec (names are only `NameOk`, `done` says nothing), or give a
persistent, discarded empty claim per directory.

Also, `NameSet` keys are lists, so `.only [a,b]` and `.only [b,a]` are different keys. Fix a
canonical form (sorted and deduplicated) in `osNames_split` and `osNames_merge`.

**m4. Missing no-effect specs.** The `os` models reach these steps, and §3 lists none of them:

- `Open` of an absent path without `O_CREAT` (`Exist`, `openAtIndex`);
- `Rmdir` of a file or an absent name (`os.Remove`'s fallback, os.lean:607-612);
- `Unlink` of an absent name or a directory (`RemoveAll`'s first `Remove`);
- `Rename` failing without effect, when `RenameOk` is false (an `EINTR` retry after a rename that
  took effect);
- the shared `LstatDir` (only sketched).

Also make explicit, in the rename-onto-empty-directory case, the premise `hOld.next ≤ s` that §3's
general shape implies.

**m5. `os.RemoveAll` is outside the semantics.**

- Create calls `os.RemoveAll(tmpdirpath)` (wal.go:115) on a `wal.tmp` left by a crash during an
  earlier Create.
- Go's `RemoveAll` then works from a parent fd: `OpenFile(parentDir)`, then `unlinkat` and `openat`
  in `removeAllFrom` (go1.27 `os/removeall_at.go`:47-80). The extension has no `*at` calls.
- The plan lists `RemoveAll` as "no model" (:301, :322). The design should say whether I2 covers it.

With I2's inode-keyed claims and blind directory fds, a dfd-relative `Unlinkat(dfd, b)` is the
natural next trusted operation: its footprint is `(dfd.ino, b)` and it needs no spine.

**m6. The dismissal in §5 risk 3 is wrong.**

- A crash rule strengthened per slot or per directory (keeping `x` keeps every earlier `y` whose
  footprint meets `x`'s) would give the per-name prefix directly, not "only for `FsInit`".
- It is also plausibly faithful to Linux: same-directory operations serialize on the parent's
  `i_rwsem`, so the handles join transactions in order. That would need a measurement and an
  example in `examples/osfs/semantics/`.

*Fix:* correct the sentence. Keeping the logic discipline is still the better choice: it costs real
code nothing, because the os models discharge it.

**m7. Redundant ghost state.**

- `γlen` duplicates `γlog`: a `MonoList` prefix bound gives `osLogLb`.
- `NamesH` is a function of `(j, N, Vs)`, so `NamesCoh` could define it instead of constraining it.

Neither is wrong; they just cost lines.

**m8. The `filePipeline` claim hand-back (alloc).**

- `alloc` re-creates `count%2.tmp` (file_pipeline.go:77). Before the pipeline creates `0.tmp`
  again, it must hold the claim that main got with `0.tmp` and used for the rename at :936.
- The only thing ordering main's rename before the pipeline's re-create is the rendezvous of the
  next unbuffered send. Main receives `1.tmp` in the next `cut`, after the rename.
- So "parked in `walInv` between hand-offs" (§4.2) needs a channel spec under which the sender
  learns of the receiver's state. The AU channel specs exist (`Perennial/Golang/Theory/Chan/AuSpec/`).

Name this in §4.2 so that W2 plans for it. I did not check whether those specs give the sender a
resource from the receiver.

**m9. Small inaccuracies.** In §4.1, "whole region: `K` is a prefix iff `R`'s calls never
overlapped" is only "if". The legacy `crashRest_tree` (CrashTok.lean:324) takes a raw
`gElem γd dq`. In shared mode the state interpretation's `gElem γd () 1 (R, V0)` refutes it, as
claimed, but only if `crashRest`'s shared branch keeps that fragment. §4.2 says it does; keep it.

## Fitness for the four WAL operations

| Operation | Covered? | Needs |
|---|---|---|
| `cut` (rename of `N.tmp` with `dirFile` open, then `dirFile.Sync`) | Yes, at the FS level. The two claims (`.only [N.tmp]`, `.except […]`), then `osLogLb (x+1)` → `osCommitLb (x+1)` | M1 (`walInv` holds half of each claim), M3 (the DirSync spec) |
| `filePipeline.alloc` (create of `N.tmp` concurrent with main's calls, then fallocate) | Yes. Disjoint claims; fallocate is a data step (`TreeFrame`) | M1, m8 |
| `Create` (directory rename, parent fsync) | Yes, with `osCallPerm 1` | M4 (who holds the permission), m5 (`RemoveAll` of a leftover `wal.tmp`) |
| Purge (unlinks concurrent with appends) | No | M2 (I5) |

Region ownership as a crash invariant works:

- `RegionCrashed` plus the starts recorded in `h.ents` give a pure derivation of the per-thread and
  per-name prefixes;
- spine claims in `cl` give path resolution after the crash;
- new claims, keyed by the same inode numbers, connect the two generations.

This holds once M1 is fixed.

## Ranking by need of revision

1. M1: the shape of the `os`-level specs, without which the WAL's crash invariant has no specs to
   use.
2. M3: the specs that are unprovable as written.
3. M2: the purge claim and its dependence on I5.
4. M4: the permission protocol.
5. m1: rebase onto I1.
6. m2-m9.
