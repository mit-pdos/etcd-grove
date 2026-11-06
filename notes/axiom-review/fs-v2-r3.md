# Review, round 3: the fixes for round 2's R1 and R2 (`GooseLang/Ext/Fs/`)

**Date:** 2026-11-06. **Reviewed:** only the change `git diff 884baf288f c735b679f4 --
GooseLang/Ext/Fs/` (branch `fs-v2`), which addresses [fs-v2-r2](fs-v2-r2.md)'s findings R1
(non-atomic path walks) and R2 (`Follows` over-orders a rename's moved directory). The parts of the
change under review are: `CallBegin` (formerly `MetaBegin`), now taken by every call on a path
(`Impl.lean:653-661`); the token that `Open` (`:552-572`) and `LstatDir` (`:693-701`) now take;
`Rename`'s new premise (`:711`); `MetaOp.locks` (`Tree.lean:94-102`) in `Follows` (`:129-135`),
while `lastTouch` (`:151-153`) still uses `MetaOp.dirs`; and the rewritten header
(`Impl.lean:18-25`). Round 2's R3 and R4 dispositions are wording, so I read them only for
accuracy. Everything else was taken as round 2 left it.

**Method.** As in rounds 1 and 2 (the `axiom` skill, adapted). A finding is an execution (threads,
calls, the kernel's interleaving, a crash point) whose Linux outcome the model excludes, or a pair
of steps that the model leaves unordered but that does not commute. Kernel facts are from my
reading of Linux v6.x `fs/namei.c` (`link_path_walk`, `lookup_slow`, `may_create`/`may_delete`'s
`IS_DEADDIR`, `vfs_rename`, `vfs_rmdir`, `vfs_unlink`), `fs/ext4/namei.c` and `fs/jbd2/`, and
`fs/xfs/xfs_inode.c`. No kernel tree was available to re-read, and no tests were run, as the task
allowed.

**The argument a stuck premise needs.** Round 2's correspondence placed each step inside its call's
real window. A stuck premise does not add behaviours; it removes programs. Perennial's adequacy
concludes `RealNotStuck` for every thread in every reachable configuration
(`BoundedLang.lean:230`, `Grove/Adequacy.lean:69`). A verified program therefore never reaches a
state in which a thread is at a directory `Rename` while another path call is between its
`CallBegin` and its step. The step is placed at the moment the effect becomes visible.

Take the first moment of a real run at which a directory rename's `d_move` happens while another
call's walk is still in progress. Up to that moment, round 2's simulation applies. In that
simulation the walker has made its `CallBegin` (placed at or before syscall entry) and not yet its
step (its effect has not happened). The renaming thread is at its `Rename` on a path that resolves
to a directory. That state is reachable, and it is stuck. So no such moment exists for a verified
program.

## Verdict

**Both fixes are sound. Neither introduces an execution that Linux has and the model excludes.**
The checks below cover R1's rule and R2's narrower `Follows`. There are two low findings, both
wording or obligations to state, and two observations about what the rules mean for clients.

| # | severity | finding | recommendation |
|---|---|---|---|
| S1 | low (wording; soundness argument) | The header's soundness discipline still says "Metadata calls overlap freely" (`Impl.lean:51`). It does not list the new stuck case among the stuck cases. That case differs in kind from the others: it depends on what other threads are doing, so the model covers Linux only for programs whose WP is `NotStuck`. | Rewrite the bullet (wording below) |
| S2 | low (obligation on the trusted models, not yet written) | R1's argument holds only if every path system call is bracketed by its own `CallBegin`. That call must come before the attempt enters the kernel, one per attempt. The fd-based and query steps must stay path-free. The step relation enforces part of this: every path step needs a live token and ends it. The placement of `CallBegin` is the trusted models' job. | State it in `CallBegin`'s docstring (wording below); check it when `TrustedCode/os.lean` is ported |
| O1 | informational | With R1's rule, a never-stuck program cannot overlap a directory rename with any operation inside the directory it moves. `start` therefore orders every such pair, so R2's narrowing has no effect on verified programs. It stays correct, and it becomes necessary if R1's rule is refined. | none; keep `locks` |
| O2 | informational (completeness) | R1's rule is global: a directory rename waits for every other path call in the process, including read-only calls in other roots. A client's proof must account for all of them. | Refine later if a client needs it: record the path at `CallBegin`, and make the rename stuck only on in-flight paths under its source (sketch below) |

## R1: the rule "a directory rename waits for every other path call"

### Is it enough?

**Every step that resolves a path takes a token.** These are `Open` (`:556-558`), `LstatDir`
(`:697-698`), `Rename` (`:709-710`), `Unlink` (`:720-721`), `Rmdir` (`:730-731`) and `Mkdir`
(`:740-741`). Every one ends the token on every branch: `st0 := st.metaEnd …` (`:562`, `:712`,
`:722`, `:732`, `:742`) and `st.metaEnd t` (`:699`). No other step reads `lookup`, `parent` or
`TreeName`. The remaining steps are `PRead`/`PWrite*`/`Fstat`/`Ftruncate*`/`Fsync`/`Flock`/`Close`/
`Mmap`/`Munmap`/`Falloc*`/`OfdLock` (on `fds`), `DirSync`/`DirClose`/`DirReadNext` (on `dfds`) and
`FdKind`, and they act on inodes:

- An `Open` of a directory followed by `DirReadNext` reads by inode (`:680-692`). On Linux,
  `getdents64` on the fd also reads by inode, and a rename of the directory does not change its
  entries.
- `DirSync` commits by inode (`:666-670`). `ext4_sync_file` and `xfs_dir_fsync` also work on the
  fd's inode.

None of these walks a path, so none needs a token.

**When no directory is renamed, a component-by-component walk is equivalent to the model's
one-instant lookup.** Suppose a walk succeeds. It finds component `c_i` in directory `j_{i-1}` at
time `t_i`, and `t_1 < … < t_n`. Only three things can remove the entry `(j_{i-1}, c_i) = dir j_i`
after `t_i`:

- an `rmdir` of `j_i`;
- a rename of a directory onto it (excluded);
- a rename of a file onto it, which Linux refuses (`EISDIR`) and so does `RenameOk` (`:493`).

An `rmdir` of `j_i` needs `j_i` to be empty, so `c_{i+1}` would have to be gone first, and so on
down to `j_{n-1}`. But once `j_{n-1}` is dead, the lookup of `c_n` in it fails:
`lookup_slow` and `may_create`/`may_delete` check `IS_DEADDIR` and return `ENOENT`, and nothing can
be added to a dead directory. So every entry of a successful walk is still present at `t_n`. The
path resolves in the tree at `t_n`, and the last component is looked up there, under the parent's
lock for a call that creates or removes. A walk that fails is matched by the model's failure branch
(any errno). On a call that may create, that branch is without the effect: `st' = st0` (`:572`,
`:727`, `:737`, `:717`, `:748`).

This covers the cases the brief asked about:

- **`rmdir` then `mkdir` of the same name, with a walker past it.** The walker is in the dead inode
  and gets `ENOENT`, as above. The model's failure branch has it.
- **`rename` of a file onto a name a walker is about to look up.** `d_move` is atomic for lookups
  (`rename_lock`, `d_seq`), so the walker sees the old or the new file at its last-component
  instant, which is where the model places the step. A file rename never changes a directory
  entry, so walks through directories are unaffected.
- **A file rename across the walked directories.** Same as above.
- **The root.** Roots cannot be renamed or removed: `TreeName` requires a path strictly below a
  root (`:420`). A rename of an ancestor of a root takes a path that is not `TreePath`, so it is
  stuck. Another process moving one is excluded by the environment.

**Every directory rename is covered.** The premise (`:711`) applies whenever `lookup s` is a
directory at the step, and it sits outside the disjunction, so a failing rename is stuck too.

- A rename that replaces a directory has a directory source, so it is covered. An empty target `t`
  that a walker had already passed leaves the walker in a dead inode, which gives `ENOENT` as
  above.
- A rename whose source is a file cannot change a directory entry.
- The renaming call's own two walks (`filename_parentat` twice, then `lock_rename`) are covered as
  well. No other directory rename can take its step while this one is in flight, so the
  equivalence above applies to these walks too.

**The order of threads' `CallBegin`s and steps does not matter.** The premise is checked at the
rename's step, against every token in `calls`. Two orders are possible:

- **The walker's `CallBegin` came first.** Its token is present when the rename steps, so the
  rename is stuck.
- **The rename's `CallBegin` came first.** If the walker's `CallBegin` is placed while the rename
  is ready, that state is stuck. If the walker's step lands before the rename's, the sibling
  interleaving (rename first) is reachable and stuck. So a verified program must separate the two
  windows with its own synchronization. That synchronization (a Go mutex, a channel) happens
  before `CallBegin` and after the trusted model returns, which is after the system call returns.
  It therefore separates the real system calls too.

A `CallBegin` placed earlier than syscall entry, such as a model that does argument work after it,
only widens the window. That makes the model stuck in more states and lowers `start` (fewer
`Follows` edges, more crash outcomes). Both are sound.

### Is it implementable, and is "stuck" vacuous?

**Not vacuous.** A stuck external operation is not a wait. GooseLang's real semantics has no step
for it, and adequacy requires `RealNotStuck` of every thread in every reachable configuration,
whatever the scheduler does. In the bounded language a stutter only happens when the step is "(really)
reducible", per `BoundedLang.lean:16`. A program in which a directory rename can be scheduled while
another path call is in flight cannot be verified. That is the intended restriction. It hides no
Linux behaviour of a verified program, because such a program's real runs never contain the
overlap (shown above).

**Implementable by the trusted models.** Each of Go's path wrappers on linux/amd64 is one system
call per attempt:

- `os.OpenFile` is `openat`;
- `os.Mkdir` is `mkdirat`;
- `syscall.Rename` is `renameat`;
- `syscall.Unlink` is `unlinkat`;
- `syscall.Rmdir` is `unlinkat` with `AT_REMOVEDIR`;
- `os.Lstat` is `fstatat` with `AT_SYMLINK_NOFOLLOW`;
- `os.Rename`'s `Lstat` calls are separate calls.

Each wrapper retries `EINTR` through `ignoringEINTR`, so `CallBegin` goes inside the retried
closure, as round 2 already noted.

A model that calls `CallBegin` and then returns early without the step leaves a token behind. That
is sound, but it makes every later directory rename stuck (S2). Examples are a `BytePtrFromString`
failure (a NUL in the name, already stuck since it is not a `TreePath`) or an `os.Rename` branch
that returns `EEXIST` after `Lstat`.

For the program logic, the premise needs a process-wide resource: for example, an authoritative
count of outstanding call tokens, a fraction of which each `CallBegin` spec hands out, and the
whole of which a directory rename's spec requires. That is a design task for the specs, not a
soundness question (O2).

### S1 (low): the header's soundness discipline is out of date

`Impl.lean:48-52` ("*Races*") still says "Metadata calls overlap freely". "*Misuse is stuck*"
(`:41-43`) lists only conditions on the call itself. The new case differs in kind: the model now
contains Linux's behaviours only for runs in which no directory rename overlaps another path call.
The argument for that is the not-stuck property of the program's WP, not a property of the model
alone. Proposed wording for the *Races* bullet:

> Path calls (`CallBegin` … step) overlap, except that a rename of a directory is stuck while any
> other path call is in flight: Linux walks a path a component at a time, and the model resolves it
> at one instant, which agrees with Linux only when no directory is moved during the walk. This
> stuck case depends on other threads, so the model contains Linux's behaviours for the runs of
> programs proved `NotStuck` (every WP is), which never have that overlap. A crash keeps a set of
> logged operations that respects the journal's order (`Tree.lean`, `Follows`).

### S2 (low): the trusted models' obligation, stated where they will read it

The step relation forces the token to exist. The soundness argument also needs the window to cover
the real system call. Proposed addition to `CallBegin`'s docstring (`:653-657`):

> A trusted model makes one `CallBegin` per system-call attempt (inside Go's `EINTR` retry loop),
> before the attempt enters the kernel, and passes its token to that attempt's step only. A model
> that returns without the step leaves the call in flight for good, which makes every later
> directory rename stuck.

## R2: `Follows` by `MetaOp.locks`

**Removing edges cannot exclude a Linux outcome.** `Follows` now has fewer edges, so more sets are
`Closed` and every outcome the model had before is still there. The questions are whether an edge
Linux needs was lost, and whether the newly unordered pairs commute.

**Each member of `locks` is held across the visible step, or ordered by existence.**

- A create, unlink, `rmdir`, rename or mkdir holds its parents' `i_rwsem` through `d_instantiate`,
  `d_delete` and `d_move`. That includes `d_delete` in `vfs_unlink`, which runs under the caller's
  parent lock.
- `vfs_rename` locks a replaced target (`inode_lock(target)` for a directory) and unlocks it after
  `d_move`.
- `vfs_rmdir`'s victim is unlocked before `d_delete_notify`. Its `S_DEAD` is set under the lock,
  so an operation inside the victim cannot take effect between the two (`IS_DEADDIR`).
- A mkdir's new directory `j'` is not `i_rwsem`-locked, but nothing can reach it before
  `d_instantiate`. An operation inside it therefore resolves it after the mkdir's handle has
  started (ext4), so its handle joins the same or a later transaction (a jbd2 transaction in
  `T_LOCKED` blocks new handles). On xfs, it resolves it after the mkdir's `xfs_trans_commit`.

So every edge `Follows` keeps is one that Linux's journal respects. The only edge removed is round
2's, which Linux does not respect on a same-directory rename, nor on any rename before v6.5.

**Newly unordered pairs commute.** The pairs in question are a rename `R` of a directory `j`, from
`p` to `p'`, and an operation `x` whose `locks` contain `j` but share nothing with `R`'s
`[p, p'] ++ replaced`.

- `MetaOp.apply` of `R` (`Tree.lean:79-81`) reads only `(p, b)` and writes only `p` and `p'`.
- `x` writes `j`, plus a fresh inode for a mkdir, and reads only `j`'s entries.
- If `x` were a cross-directory rename out of or into `j`, it would share `crossRename` with `R`
  when `R` crosses directories. Otherwise it would lock a directory `R` locks.
- If `x` removes or replaces `j` itself, it locks `j`'s parent at that point, which is `p` or `p'`.

Replay in log order therefore gives the same tree as the journal's order.

**The moved directory's `..` entry and `nlink` are not observable.** The model has no `..`
component (`NameOk`, `Paths.lean:31-32`) and no link count. Linux's `..` and `nlink` changes for
`R` are in `R`'s own transaction, which is atomic (jbd2's frozen copies; xfs's per-checkpoint
formatting). So a kept `R` without `x`, or `x` without `R`, recovers a consistent directory whose
entries are what the model replays.

**A kept rename always keeps what created the directory it moves.** The operation that last put
`j` at its source name (its mkdir, or an earlier rename of it) has `R`'s source parent in its
`locks`, so closure keeps it. Its replay also tolerates the absence (`none => m`), so no subset
yields an ill-formed tree.

**The pairs the brief listed** all fall under these arguments:

- the moved directory's `..` or `nlink`;
- an operation that replaces or removes the moved directory, which shares its parent;
- a directory renamed across directories while creates and removes run inside it, which commute;
  on 6.5 and later Linux even serializes them, and the model allows more;
- a rename onto an empty directory that another call is creating into. Both lock the target, so
  they are ordered. `RenameOk` needs `EmptyDir` at the step, so one of the two fails if the create
  comes first. A create after the rename resolves its parent to the moved directory.

**`lastTouch` on `dirs`, `Needed` on `locks`.** `DirSync` (`:666-670`) still commits the rename of
the directory being synced, which Linux does: `ext4_rename` marks the moved inode dirty, so its
`i_sync_tid` covers the rename, and `xfs_rename` logs `src_ip`. Now, though, `Needed` of a rename
`R` of `j` no longer includes an earlier operation inside `j` that `start` does not order. Nor does
`Needed` of a later operation inside `j` include an unordered `R`. That is weaker than Linux, which
commits both (ext4 through `i_sync_tid`, ordered transactions; xfs through the last
`ili_commit_seq` of `j`), so it is sound. By O1, it never applies to a verified program.

### O1: with R1's rule, R2's narrowing has no effect on verified programs

Let `x` be any operation inside the moved directory `j` (any `x` with `j ∈ x.op.locks`, `j ∉
R.op.locks`). Suppose its window overlaps the window of the directory rename `R`.

- **`x`'s `CallBegin` is earlier.** At `R`'s `CallBegin`, `R` is ready to step. If `s` names `j`
  then, that state is stuck. If it does not, `j` is put at `s` before `x`'s step. Only a mkdir at
  `s` can do that: a directory rename to `s` would itself be stuck while `R` is in flight. After
  that mkdir, `x` is in flight, `R` is ready and `s` is a directory, so the state is stuck.
- **`x`'s `CallBegin` is later.** The same argument applies from the moment `x` begins.

So in a never-stuck program, `x` and `R` are ordered by `start` in one direction or the other.
Round 2's R2 execution in particular (T1's `unlink` in flight while T2 renames `c`) is now a stuck
state, which the program must avoid.

The `locks` change is therefore correct but has no effect today. It matters if R1's rule is
replaced by the precise walk model (round 2's first recommendation), which drops the stuck premise.
I recommend keeping it, so that that refinement needs no change to `Follows`.

I first thought of a counter-case: a mkdir of `s` and a create inside it, both overlapping `R`'s
window. It fails for the reason above. Once the mkdir has taken its step, the state with the create
in flight and `R` ready is reachable and stuck.

### O2: the rule's cost to clients, and a narrower variant

The premise forbids every other in-flight path call, including `lstat`s, plain `open`s and calls
in other roots. Linux needs much less. A walk is affected only if it passes through the moved
directory. At the rename's step, that means the walker's path lies under `s`: the path to `j` is
unique, and no directory has been moved since the walker began. A walk through the target `t`
(absent or empty) is already matched, by a lookup at one instant or by `ENOENT` in a dead inode.

A narrower premise is sound for the same reasons: `CallBegin` takes `#p` and records it, and
`Rename` is stuck only on an in-flight call whose path `p'` satisfies `IsUnder s p'`.

- **etcd.** `wal.Create`'s `renameWAL` (`server/storage/wal/wal.go:296-317`, the clone in `.lake/goose/etcd`) renames the `.tmp`
  directory before the file pipeline starts. `cleanupWAL` (`:280-293`) renames a failed WAL
  directory after `Close`. Whether other goroutines of etcd's bootstrap (the snapshotter, the
  backend) make path calls at those moments was not checked. Under the global rule they must not;
  under the narrower one they only must not be in the WAL directory.
- **renameWALUnlock.** `os.Rename` returns `*LinkError` on every failure, so `errors.As` always
  succeeds and `renameWALUnlock` (`:319-343`) runs after any failed rename, not only on Windows.
  This is not a fs-model question, so it is only noted here.

## Not tried

- No kernel source was re-read and no test was run. The walk facts (`IS_DEADDIR` on lookup and
  create in a dead directory, `rename_lock`/`d_seq` atomicity of `d_move` for a lookup) and the
  lock sets of `vfs_rename`/`vfs_rmdir` are from memory of v6.x. They should be checked at the
  kernel range the header names ("Linux 6.x").
- The program logic for the premise (the process-wide resource in O2) is not written, so I could not
  check whether a spec makes it easy to prove the premise by mistake.
- Round 2's other conclusions were not re-attacked: the start-token order, the cross-directory
  rename lock, `Needed` against directory `fsync`, and the data path.
