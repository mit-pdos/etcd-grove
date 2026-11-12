# Review, round 2: the Linux file extension, version 2 (`GooseLang/Ext/Fs/`)

**Date:** 2026-11-06. **Reviewed:** `GooseLang/Ext/Fs/Paths.lean`, `Tree.lean`, `Impl.lean` at
`884baf288f` (branch `fs-v2`): the step relation `IsFsStep`, the crash relation `OsCrash`
(`MachineCrash`, `ProcRestart`), `FsInit`, and the environment assumptions in `Impl.lean`'s header.
The focus is the redesigned metadata half: directories as inodes, operations journaled by directory
inode and name, overlapping calls (`MetaBegin`'s start token), and the crash's set of kept entries,
closed under `Follows` and replayed in log order. `Needed`/`lastTouch`/`commitThrough` for a
directory `fsync` are in scope too. I read `notes/fs-semantics-v2.md` and the docstrings as claims
to check. `Tests.lean` and `Lookup.lean` (untrusted) were read for the intended behaviour, and
`TrustedCode/os.lean` only for how the operations are called. The round-1 report is
[fs-v2](fs-v2.md); its findings were addressed (its Disposition), and the data path was re-checked
here only for regressions.

**Method.** The `axiom` skill's, adapted as in round 1. The claim under review: every behaviour
Linux (ext4 `data=ordered`/`data=journal` without `fast_commit`, or xfs, under the header's
environment) can show for the modelled calls is a behaviour of the model. That covers results,
errnos, interleavings, and crash and restart outcomes. A finding is an execution (threads, calls,
the kernel's interleaving, the crash point), the Linux outcome, and why the model excludes it, with
the lines that exclude it. As the user allowed, no Go test and no Lean counterexample was built. The
kernel claims come from my reading of Linux v6.x (`fs/namei.c`: `link_path_walk`,
`open_last_lookups`, `lock_rename`, `vfs_rename`, `vfs_unlink`; `fs/dcache.c`; `fs/jbd2/`
`transaction.c`/`commit.c`; `fs/ext4/{namei,fsync}.c`; `fs/xfs/xfs_{inode,file,log_cil}.c`). No
kernel tree was available to re-read here, so each point says what it rests on.

**How a model step is placed.** Every argument below uses one correspondence, so I state it once. A
real execution is matched by a model execution that puts each metadata call's step inside the
call's real time window. The step goes at the moment its effect becomes visible: the dcache update
(`d_instantiate`, `d_move`, `d_delete`), which comes after the journal handle has started on ext4
and after `xfs_trans_commit` on xfs. Its `MetaBegin` goes just before the system call is entered.
Steps of calls on a common locked directory go inside the lock's critical section. The simulation
may choose with hindsight (it knows where the crash falls), as an adequacy proof's simulation can.
A model behaviour is missing when no placement of this kind exists.

## Verdict

**Not sound as stated: two findings in the metadata half, one assumption to state, one wording
fix.** The core of the design survived: by-inode operations commute when their directories are
disjoint, the start-token order is sound, the cross-directory rename lock is real, and
`Needed`/`lastTouch` is no stronger than ext4's force commit or xfs's log force of the directory
inode. So did `nextIno`, `FsInit`/`TreeWf`, `lookup`'s choice, and the crash's existence from every
state. The data path has no regression.

| # | severity | finding | recommendation |
|---|---|---|---|
| R1 | high (soundness, any program; etcd and bbolt do not hit it) | path resolution is atomic in the model: every step resolves its whole path in the tree at one instant. Linux walks one component at a time, without locks above the last directory, so a concurrent rename of an ancestor makes a call succeed on a path that never existed at any instant | model change: resolve each component in a tree no older than the previous one's, since the call began (a begin token for every path-taking call); or make a directory rename stuck while another call's path runs through it |
| R2 | medium (soundness; a narrow race plus a crash) | `MetaOp.dirs` of a rename includes the moved directory, so `Follows` orders it against every earlier operation in that directory. Linux does not lock the moved directory on a same-directory rename (nor on any rename before v6.5). A stale positive dentry can then force the model's log order opposite to the journal's, and the crash that keeps only the earlier transaction is excluded | model change: leave the moved directory out of the set `Follows` compares, keeping it in `lastTouch`'s |
| R3 | low (assumption to state) | `ProcRestart` lands every in-flight change and metadata call at the restart. That is true only if the new process starts after the old one's threads have all left the kernel | environment assumption, worded below |
| R4 | low (wording) | the header's journal assumptions describe the previous design (one order, a directory's own entries) and not what `Follows`/`Needed` now use | rewrite the two sentences (below) |

Separately, under "Stuck or less defined than Linux": where etcd's WAL or bbolt would be stuck.

## Findings

### R1 (high): path resolution is not atomic on Linux

**The model's claim.** `OsState.lookup` (`Impl.lean:405-412`) walks the whole path in `st.tree`,
the tree at the step's instant, and `OsState.parent` (`:421-427`) uses it. Every path-taking step
resolves against that one tree: `Open` (`:551-568`, through `OpenEffect`, `:468-476`), `Rename`
(`:698-705`, through `RenameOk`/`RenameOp`, `:485-495`), `Unlink` (`:708-715`), `Rmdir`
(`:718-725`), `Mkdir` (`:728-736`) and `LstatDir` (`:692-694`). A call succeeds only if its path
resolves, in full, in some tree the log passes through while the call is in flight.

**The Linux behaviour.** `path_openat`/`filename_parentat` walk the path one component at a time in
`link_path_walk`, in RCU mode or by reference. No lock is held on the directories already passed,
and no check covers renames of them. The only check is each component's own `d_seq` while it is
being stepped through (a `..` would also check `rename_lock`). The last directory is locked only
afterwards (`open_last_lookups`, `filename_create`, `lock_rename`). When a component misses the
dcache, the walk sleeps in the filesystem's `->lookup` while it reads a directory block. A rename of
a directory already passed can therefore complete in the middle of the walk. The walk then
continues in the moved directory's inode, now at another path.

**Execution.** At the start, `/r` is a root, `/r/c` is a directory (inode 4) and `/r/c/x` is a
directory (inode 5). There is no `f`, and `x` is not in the dcache.

1. T1 calls `open("/r/c/x/f", O_RDONLY)`. Its walk finds `c` (inode 4) and misses `x`, so it sleeps
   in `ext4_lookup` of `x` (taking 4's `i_rwsem` shared, which the next rename does not need).
2. T2 renames `/r/c` to `/r/d` and returns 0. A same-directory rename locks inode 1 only, plus no
   child (`vfs_rename`).
3. T2 then calls `open("/r/d/x/f", O_WRONLY|O_CREAT)`, which creates `f` in inode 5 and returns.
4. T1's lookup returns `x` (inode 5), finds `f` there, and the open returns an fd.

Before step 2, `f` does not exist. From step 2 on, `/r/c` does not exist. So no tree the model's log
passes through has `/r/c/x/f`, and T1's `Open` has only its failure branch. A Go program in which T1
panics if its `os.Open` succeeds has a no-panic proof from the model (the invariant "`f` exists only
after the rename"), yet it can panic on Linux. The same holds for `O_CREAT` (T1 creates `f` in
inode 5 through `/r/c/x/f` after the rename; the model's `OpenEffect` has `st.parent p = none`), for
`mkdir`, `unlink` and `rename` through a moved ancestor, and on xfs (the walk is the VFS's).

**Why it matters although the window is small.** The `Open` step's success has no other
explanation, so the proof's conclusion "T1 fails" is false for a real run. etcd and bbolt do not
rename a directory while another of their calls resolves a path through it (`wal.Create` renames
its `.tmp` directory before any other call uses it), so the clients are unaffected. The model is
nonetheless claimed sound for every program.

**Recommendation (model change).** Resolve paths the way Linux does, through the log's intermediate
trees. The log already gives them: `replay (metaLog.take k).map (·.op) treeDur`.

- Give every path-taking call a begin token, as `MetaBegin` already does for the metadata calls.
  Plain `Open` and `LstatDir` would need one too.
- Let component *i* be looked up in the tree after `k_i` entries, where `start ≤ k_1 ≤ … ≤ k_n` and
  the last directory's lookup (create, remove, rename's final names) is in the current tree. Linux
  looks those up under the directory's lock.
- Refuse a create, mkdir or rename into a directory that has been removed or replaced since. Linux
  returns `ENOENT` (`IS_DEADDIR`). Allowing it would be extra behaviour, which is sound, but it
  would leave an unreachable entry in the tree.

When no directory on the path was renamed during the call, every choice of the `k_i` gives the same
result. One lemma then gives the clients' proofs today's resolution. A cheaper alternative is sound
too: record each in-flight call's path at its begin step, and make a directory `Rename` stuck while
an in-flight call's path lies under its source. etcd and bbolt never meet that condition.

### R2 (medium): `Follows` orders a rename after operations inside the directory it moves

**The model's claim.** `MetaOp.dirs` (`Tree.lean:88-92`) of `.rename j b j' b' n old` is
`[j, j'] ++ n.dirIno ++ …`, so it includes the moved directory itself. `Follows` (`:122-125`)
requires an earlier entry that shares any directory with a kept entry to be kept. The header's
justification (`Tree.lean:17-20`) is that "two that change a common directory are serialized by
that directory's lock, so the journal has them in the log's order".

**What Linux locks.** `vfs_rename` (v6.5 and later) locks the moved directory only for a
cross-directory rename (`lock_old_subdir = new_dir != old_dir`). Before v6.5 (commit "fs: Lock
moved directories") it locked it on no rename. A same-directory rename of `c` to `d` therefore holds
the parent's `i_rwsem` (and its own victim, if any) but not `c`'s. An unlink inside `c` holds `c`'s
`i_rwsem`, so the two are not serialized. Separately, `vfs_unlink` calls `d_delete` after
`->unlink` has returned: on ext4, after the handle has stopped; on xfs, after `xfs_trans_commit`.
Until then the victim's dentry stays positive, and an RCU-walk lookup finds it without taking any
lock.

**Execution (ext4; the same on xfs).** At the start, `/r/c` is a directory (inode 4) holding a file
`y` (inode 7). Nothing is in flight.

1. T1 calls `unlink("/r/c/y")`: it locks 4, `ext4_unlink`'s handle joins transaction T1, removes the
   entry and stops. T1 is then preempted before `d_delete`.
2. The journal starts committing T1, for example because T4 `fsync`s a file whose last transaction
   is T1. The handles have drained, so T1 switches and T2 becomes the running transaction.
3. T2 calls `rename("/r/c", "/r/d")`: it locks inode 1 only, its handle joins T2, and `d_move`
   runs. It returns 0.
4. T3 calls `open("/r/d/y", O_RDONLY)`. The RCU walk goes from `d` (dentry of 4) to `y`, which is
   still positive, and the open returns an fd on inode 7.
5. T1 resumes, calls `d_delete`, and returns 0.
6. T1's commit block reaches the disk, then the power is lost (T2 is not committed).

After recovery, `/r/c` exists (the rename is lost) and holds no `y` (the unlink was kept).

**Why the model excludes it.** T3's `Open` succeeds only at a step where `/r/d/y` resolves, so after
the rename's step and before the unlink's (`OsState.lookup`, `Impl.lean:405-412`). The log must
therefore be `[rename 1 c 1 d (.dir 4) none, remove 4 y (.file 7)]`. The rename's `dirs` is
`[1, 1, 4]` and the remove's is `[4]`, so `Follows log 1 0` holds (`Tree.lean:122-125`). The unlink
began before the rename took effect, so `start` does not order them, but the shared directory does.
Every closed set that keeps entry 1 also keeps entry 0 (`MachineCrash`, `Impl.lean:806-807`). The
model's crash trees are `c` with `y`, `d` with `y`, and `d` without `y`. Linux's tree, `c` without
`y`, is missing.

On xfs, `xfs_rename` takes the moved inode's `ILOCK`, so the CIL sequence orders the two
operations. The dcache observer in step 4 still forces the model's opposite order, and the outcome
is the same. Before v6.5, the same execution works with a cross-directory rename too.

**Recommendation (model change).** Split the two uses of `dirs`.

- **The set `Follows` compares**: the directories Linux locks and changes. For a create, a mkdir
  (its parent, and the new directory, whose order is forced the right way by its existence), a
  remove (the parent and a removed directory), and a rename (both parents and a replaced
  directory), leave out the moved directory on every rename. Leaving it out of the cross-directory
  case too keeps the model sound for kernels before v6.5, and costs nothing: `MetaOp.apply` never
  reads or writes the moved directory's entries (the tree has no `..`), so the pair still commutes.
- **The set `lastTouch` uses**: keep it as it is. ext4's `fsync` of a directory force-commits the
  whole journal (and before v5.10 completed the directory's `i_sync_tid`, which a rename's
  `ext4_mark_inode_dirty` of the moved inode updates). xfs's `xfs_dir_fsync` forces the log through
  the directory inode's `ili_commit_seq`, and `xfs_rename` logs the source inode. So a `fsync` of a
  moved directory does commit its rename.

This does not weaken anything etcd's WAL uses. `wal.Create`'s rename of its `.tmp` directory is
ordered after the creates inside it by `start`, because they returned before the rename began, not
only by the shared directory.

### R3 (low): a restart assumes the old process has left the kernel

`ProcRestart` (`Impl.lean:815-821`) lands each in-flight change as some prefix at the restart. A
metadata call that has not taken its step "did nothing". Both are right only if no system call of
the old process is still running once the new process starts. A killed process's threads finish
their system calls before it exits, and a supervisor that waits for the exit (systemd, an init
loop) meets this. A restart that does not wait for the old process to be reaped (for example a
script that sends `SIGKILL` and starts the new process at once) can let an old `pwrite` or `rename`
land after the new process has read the state. Neither the header nor the docstring says this.
**State it:** "A restart begins only after every thread of the previous process has returned from
the kernel (the process has exited)."

### R4 (low): the header's journal sentences describe the previous design

`Impl.lean:18-20` still says "Metadata operations reach the journal in the order they are made and
the journal commits in order; an `fsync` of a directory commits it up to the last change of that
directory's entries". The model now relies on three things instead:

- ext4's jbd2 and xfs's CIL commit whole transactions (checkpoints) in order, each system call's
  changes in one transaction (ext4's `journal_async_commit` and `fast_commit` excluded);
- calls on a common directory lock it, and cross-directory renames take the filesystem's rename
  mutex (R2 corrects which directories);
- a directory `fsync` commits the last transaction that logged the directory inode, together with
  every transaction before it. That covers renaming, replacing or removing the directory, not only
  changes to its entries, and `lastTouch` uses all of these.

Each of these holds for the kernels named (above). I recommend stating them in these terms, with
the kernel range the review assumed (v5.x to v6.x).

## Attacks the model survived

**`Follows`'s start-token order** (`y < ex.start`). The step goes after the handle starts on ext4
(after `xfs_trans_commit` on xfs), and `MetaBegin` goes before the call is entered. If `y`'s step
comes before `x`'s `MetaBegin`, then `y`'s transaction was fixed before `x` entered the kernel, so
`T_y ≤ T_x`. Observations cannot force a step earlier than its handle: no change becomes visible
before its handle starts, or before xfs's commit, since lookups take `ILOCK` shared and the dcache
is updated afterwards. A `MetaBegin` placed earlier than the call only lowers `start`, so the model
promises less. Sound.

**`Follows`'s shared-directory order, with locked directories** (the parents, a replaced or removed
directory, a new directory). Both calls hold the lock while their handle runs (on xfs, while the
transaction commits), and their dcache updates happen inside the lock (`d_delete` in `vfs_unlink`
and `vfs_rmdir` runs while the caller holds the parent). So the observation order, the log order
and the journal order agree. A stale positive dentry shows only the state before the call, which
pushes the step later, never earlier. The one hole is R2's unlocked moved directory.

**Cross-directory renames.** `lock_rename` takes `s_vfs_rename_mutex` for any `p1 != p2`, and
`d_move` runs under it. Sound.

**Unordered pairs commute.** `MetaOp.apply` (`Tree.lean:75-82`) reads only the entry `j b` of a
rename and writes only the directories in `dirs`. A kept operation therefore sees the same entries
whichever earlier operations on disjoint directories were dropped. Closure keeps every earlier
operation on a shared directory. So replaying a closed set in log order equals Linux's recovered
tree, which is the ordered transactions' effects (jbd2's frozen buffer copies, and xfs's
per-context shadow formatting, isolate a committing transaction from the next). Checked against:
renames of directories across parents with operations deeper in either subtree; a rename replacing
a file or an empty directory (the replaced directory is locked by `vfs_rename`, and xfs logs it);
`rmdir` against creates in the victim (both lock it; the model gives `ENOTEMPTY` or a failed lookup
either way); two cross-directory renames that could form a cycle (always ordered); and a file
renamed across directories while unlinked under its other name (they share a directory, since there
are no hard links).

**A closed set can be a tree Linux never has.** `crash_overlap`'s outcome (`Tests.lean`) is one: a
create that resolved its path through `/r/d` has, on Linux, `T_rename ≤ T_create`. This is extra
behaviour, so it is sound. Its docstring calls it a Linux behaviour, which it is only when the
create resolved through the old path before the rename (R1's case).

**`Needed` and `lastTouch` against a directory `fsync`.**

- On ext4 (v5.10 and later), `ext4_sync_file` of a directory calls `ext4_force_commit`, which
  commits everything. Earlier kernels complete the directory's `i_sync_tid`, and transactions are
  ordered.
- On xfs, `xfs_dir_fsync` forces the log through `ili_commit_seq`. Every operation in `dirs` logs
  that inode: the parents, the new directory, the removed directory, the moved source inode
  (`xfs_rename` always logs `src_ip`), and the replaced target.
- Every `Follows` edge goes to an operation in an earlier or the same transaction. So the
  `Needed` set is on disk once the force completes.
- The step goes where `fsync` reads the sequence. An operation logged later is not claimed. A crash
  before `fsync` returns has no step, as the simulation may choose with hindsight.
- A removed or renamed directory's `lastTouch` is its `rmdir` or its rename, which is logged on xfs
  and force-committed on ext4.
- A failure claims nothing, and `S` may keep more.

**The crash is always possible.** `S := committed` is closed (a union of `Needed` sets) and bounded.
Every file the kept tree names is in `files`: files are added before their create is logged and
removed only by a crash. Version lists are never empty, and `sizeLo ≤ sizeHi` holds throughout.

**`nextIno`.** Every inode in `files` or in the tree is below it (`FsInit`; `Open` and `Mkdir` take
it and increment it; a crash and a restart keep it), so `setFile nextIno` never overwrites an
unlinked file that is still open. Inode numbers are internal, so Linux's reuse of them is not
observable.

**`lookup`'s classical choice and `parent`.** Under `RootsOk`, which `FsInit` gives and no step
changes, the split into a root and components is unique: a second root would have to be
`IsUnder` the first. A root's `parent` is `none`, and `TreeName` keeps roots out of the metadata
steps (stuck: sound).

**`FsInit`/`TreeWf`.** These are satisfiable by any real tree within the header's environment (no
hard links, regular files and directories only, nothing removed at boot). File and directory
inodes may share numbers without conflict, since `Node` tags them.

**`ProcRestart` with metadata calls in flight.** The call has or has not taken its step, whichever
the old process's system call did (given R3). The log and `committed` survive, as the journal does.

**Directory fds on removed or replaced directories.** Linux's `iterate_dir` returns `ENOENT` on a
dead directory. The model returns the end or any errno. That is more behaviour, and sound.

**An `O_CREAT` of an existing name racing a create.** The second open finds the file under the
parent's lock and logs nothing, as Linux does.

**Data path (regressions).** No step of it changed except through inodes (`git diff bd5a2408e4
884baf288f`). `CrashFile`/`SecCand`, `Landed`, the short `pread`/`pwrite`, the whole-sector crash
images (F3) and `OsFile.resized`/`written` read as round 1's disposition says. Zero past the size
still holds in a run without a crash: a shrink's new versions are cut at the new size.

## Stuck or less defined than Linux (sound; what the clients may hit)

- **R1's fix** adds nondeterminism only when a directory on the path is renamed during the call,
  which neither etcd nor bbolt does. A lemma recovers today's resolution for their proofs.
- **Roots are not renameable** (`TreeName`). `wal.Create` renames `<dir>.tmp` to `<dir>`, so the
  root must be a directory above the WAL directory (the member directory), not the WAL directory
  itself.
- **`os.RemoveAll`** (`wal.Create` clears the `.tmp` directory with it) uses `openat`/`unlinkat`.
  **`os.Stat`/`fileutil.Exist`** use `stat` on a path. Neither is a step of the extension, so the
  trusted models will be stuck there unless they are added.
- **One `Readdirnames(-1)` per fd** and no `Fstat` of a directory fd: etcd's `ReadDir` opens a new
  fd each time, so it is unaffected.
- **A token per attempt.** A retried system call (`EINTR`) needs a new `MetaBegin` for each
  attempt: the step ends the token (`metaEnd`). The ported trusted models must call it inside
  Go's `ignoringEINTR` loop, or a retry is stuck.
- **Unchanged from round 1:** overlapping in-flight writes are stuck; mapped loads past EOF are
  stuck; unsupported `open` flags (`O_EXCL`, `O_APPEND`, `O_SYNC`) are stuck. None of these is on
  etcd's or bbolt's paths.

## Not tried

- No executable test and no crash test (dm-log-writes, CrashMonkey). R1's interleaving (a lookup
  that misses the dcache and sleeps) and R2's (preemption between `->unlink` and `d_delete`, with a
  commit in between) should be confirmed that way. R2 needs a preemptible kernel or a long enough
  delay.
- Kernel source was not re-read for this round (no tree available). The lock sets of `vfs_rename`
  before and after v6.5, and `ext4_sync_file`'s directory path before v5.10, are from memory and
  should be checked at the kernel versions the header will name.
- xfs's directory format conversions during readdir (round 1's open item), ext4 inline data, and
  `RENAME_EXCHANGE`/`RENAME_WHITEOUT` (Go's `os.Rename` uses neither).
- No search for an inconsistency (`⊢ False`) in the definitions beyond checking that a crash and a
  restart are always possible.

## Disposition (2026-11-06, by the author of the semantics)

- R1: the cheaper fix. Every call on a path begins with `CallBegin` (the former `MetaBegin`, now
  also for `open` without `O_CREAT` and `lstat`), and a rename of a directory is stuck while any
  other call on a path is in flight (`Rename`'s premise). Sound (less defined); etcd and bbolt never
  rename a directory while another call walks a path. The precise model (each component resolved in
  a tree no older than the previous one's) is not done.
- R2: as proposed. `Follows` compares `MetaOp.locks`, which leaves out the directory a rename moves;
  `lastTouch` still uses `MetaOp.dirs`.
- R3: the assumption, worded as proposed (`Impl.lean`'s header, "Restart").
- R4: the header's journal sentences rewritten (transactions in order; which calls join which;
  what a directory `fsync` commits; Linux 6.x).
- The test docstring: `crash_overlap` now overlaps a file's rename with a create, which Linux has.
