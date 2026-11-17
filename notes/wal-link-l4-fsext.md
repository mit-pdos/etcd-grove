# WAL link L4: the scoped directory rename (trusted text proposal)

**Date:** 2026-11-17. **Branch:** `wal-link`. **Status:** revision 2 APPROVED BY THE USER, 2026-11-17, via etcd-grove-03 (second attack: SURVIVES, its two wording
MINORs folded); applied on `wal-link`. **Condition:** the WAL link does not land until the configuration-C run ("Open
obligation" below) is done on a machine with loop devices (etcd-grove-03 arranges it). History: Revision 1 was attacked independently (etcd-grove-03, 2026-11-17): BLOCKER, a cross-root rename walks its
target's root ("Revision 2" below); revision 2 takes fix (b), decided by etcd-grove-03, and folds the three MINORs.
Next: a short second attack, then the user. Scope: `notes/wal-link-scope.md` §4.3 (F-b), §5 (L4).

## Why

Every k-member example runs k members in one process and bootstraps member j (`wal.Create`, whose last steps
rename a temporary directory over the WAL directory, wal.go `Create`) while members 1..j-1 already run: their
raft loops `Save` and `cut` (file creates and file renames in their WAL directories), their file pipelines
create the next segment (Scope C5, `examples/wallink/link_test.go` `TestCreateWhileAnotherWALCuts`). Today's
`Rename` step (`GooseLang/Ext/Fs/Impl.lean:1023-1032`) is stuck when its source is a directory and **any**
other path call is in flight, so no proof can cover member j's `Create` beside member j-1's WAL: the k-member
theorems cannot use layer 1. With P2 (approved: each WAL in a dedicated directory under a per-member `fsExt`
root) the two WALs' path calls are in different roots' trees, and the overlap the stuck clause excludes cannot
happen between them.

## What Linux does (the evidence)

- **The reason for the stuck clause** (`examples/osfs/semantics/meta_dir_rename_stuck.go`): Linux walks a path
  a component at a time without locking the directories it has passed (`Documentation/filesystems/path-lookup.rst`),
  so a walk racing the move of a directory *on its path* can resolve a path no single tree has. The model resolves
  a path at its step, in one tree.
- **A walk only reads the dentries of its own path's components** (`link_path_walk`, `walk_component`,
  `lookup_fast`/`lookup_slow` in `fs/namei.c`): starting at `/` (an absolute path; the models pass only absolute
  paths, `cleanAbsPath`), it visits the ancestors of its path and the path's components. `rename(2)` walks **both**
  its paths (the source's and the target's parents): revision 1 missed this (below). The roots are distinct,
  none in another's tree (the environment, `Impl.lean`'s header), and the program renames only `TreeName`s
  (strictly below a root): so a directory moved in root A's tree is never on the walk of a path in root B's tree
  (B's ancestors are not below A, else B would be in A's tree), nor on a walk of a strict ancestor of a root
  (`Open`'s outside case). A `Rename`'s target `t` must be in its source's root (revision 2), so its walks stay in that root too.
- **What the walk sees of another rename** (corrected after the attack): `d_lookup`/`d_alloc_parallel` retry their
  hash lookups on `rename_lock`; a walk validates only each parent's `d_seq` as it steps, so a rename *on its path*
  can be seen mid-walk (the walk then holds a component found before the move and the next found after it: a path
  no single tree has). A rename *off its path* changes only timing (`rename_lock` retries in
  `d_lookup`/`d_alloc_parallel`, waits on `s_vfs_rename_mutex`), never the result.
- **Measured** (`examples/osfs/semantics/meta_rename_scoped_test.go`, `TestDirRenameScopedToRoot`): root A's thread
  renames directories as `wal.Create` does (mkdir a temporary directory, create a file in it, rename it over the
  target, fsync the parent) and moves a directory across subdirectories of A, while four workers in root B run
  fixed sequences of 15 path calls each (MkdirAll of a deep path, create-exclusive, lstat, file rename, a
  directory rename inside B, open through the moved directory, unlink, rmdir, mkdir of an existing name, rmdir of a
  missing one) and check each result against the sequential outcome: 4 x 3000 sequences against 1350 directory
  renames, no deviation (2.3 s; again 1444 renames, 2.5 s). **Where:** this machine's root filesystem (ext4, Linux 7.0.0-1014-aws), not a
  `c_mkfs` image: the container has no loop devices (`losetup: … failed to set up loop device`) and no
  `/proc/fs/ext4` (so `check.sh` cannot run). The claim is about the VFS's path walk, not ext4's on-disk format,
  so the mount options C fixes do not bear on it; a run on a `c_mkfs` image should be added where loop devices exist.
  Command: `cd examples/osfs/semantics && SEMANTICS_C_DIR=<dir on ext4> GOWORK=off go test -count=1 -run
  TestDirRenameScopedToRoot -v .`

## Revision 2: the attack's blocker and fix (b)

**Blocker** (independent attack, test `/shared/tmp/l4-attack/race/race_test.go`, `TestCrossRootTargetWalk`):
`Rename.impl` records only `oldname` at `CallBegin`, but `rename(2)` walks `newname` too. Root C's
`rename(C/f, A/p/<chain>/q/g)` blocks no directory rename in A (its recorded path is in C), yet walks A's tree; with
A moving `p` to `z` and then `q` into `z/<chain>`, `A/p/<chain>/q` exists in no tree of the log, and still the
rename succeeds (g lands at `A/z/<chain>/q/g`): 296 of 20000 at depth 1900 on ext4 (the attack); reproduced here,
13 of 2000 (`meta_rename_scoped_test.go`, `TestCrossRootRenameExcluded`, the excluded case).

**Fix (b)** (decided by etcd-grove-03): `Rename` is stuck unless its source and target are in one root's tree
(`st.SameRoot s t`): cross-root renames are outside the model. Then every walk of a `Rename` stays in the root of its
recorded path (`oldname`), and recording `oldname` suffices. etcd never renames across members' directories (`cut`
and `Create` rename within one WAL directory and its parent, which P2 puts in one root). Example:
`examples/osfs/semantics/meta_rename_cross_root.go` (indexed in `doc.go`, marked proposed).

## The change (old → new), `GooseLang/Ext/Fs/Impl.lean` and `TrustedCode/os.lean`

1. **A call records its path.** `ProcState.calls : GMap Nat Nat` → `GMap Nat (Nat × GoString)` (the log's length
   when the call began, and the path the call's step names). Docstring: "...and its calls on paths in flight (by
   the token `CallBegin` returned: the length of the log when the call began, and the call's path)".
2. **`CallBegin` takes the path.**
   ```
   | "CallBegin" => ∃ t : Nat, v = #() ∧ st.proc.calls !! t = none ∧ st.proc.inflight !! t = none ∧
       st' = st.setProc { st.proc with calls := <[t := st.fs.metaLog.length]> st.proc.calls } ∧ e' = Val (osTokV t)
   ```
   →
   ```
   | "CallBegin" => ∃ (t : Nat) (p : GoString), v = #p ∧ st.proc.calls !! t = none ∧ st.proc.inflight !! t = none ∧
       st' = st.setProc { st.proc with calls := <[t := (st.fs.metaLog.length, p)]> st.proc.calls } ∧ e' = Val (osTokV t)
   ```
   No condition on `p` (a call on a path outside the trees is stuck at its step, as today).
3. **A call's step names the path it began with.** In `Open`, `OpenOutside`, `LstatDir`, `Unlink`, `Rmdir`,
   `Mkdir`: `st.proc.calls !! t = some start` → `st.proc.calls !! t = some (start, p)` (`p` the step's path); in
   `Rename`: `st.proc.calls !! k = some (start, s)`. A model that begins a call on one path and steps on another
   is stuck (never more defined than before).
4. **The stuck clause, scoped.** New definition beside `TreeName`:
   ```
   /-- `a` and `b` are in one root's tree (`IsUnder`: the root itself or below it). -/
   def OsState.SameRoot (st : OsState) (a b : GoString) : Prop :=
     ∃ rj ∈ st.fs.roots, IsUnder rj.1 a ∧ IsUnder rj.1 b
   ```
   `Rename` gains the conjunct `st.SameRoot s t` (beside `st.TreeName s ∧ st.TreeName t`), and its clause
   `((∃ j, st.lookup s = some (.dir j)) → ∀ k' start', st.proc.calls !! k' = some start' → k' = k)` →
   `((∃ j, st.lookup s = some (.dir j)) → ∀ k' start' p', st.proc.calls !! k' = some (start', p') →
      k' = k ∨ ¬ st.SameRoot s p')`
   (`t` is in `s`'s root by the new conjunct; roots are not nested, `RootsOk`). Its comment: "A rename across roots is stuck (its walks of the
   target's path would race the target root's renames unseen: `meta_rename_cross_root.go`). A rename of a directory
   is stuck while another call on a path in its root's tree is in flight: Linux walks a path a component at a time,
   validating only each parent as it steps, so a call walking through a directory being moved may find a path that
   no single tree of the log has; a call in another root's tree, or above the roots, never walks through it (no root
   is in another's tree, and no root's ancestor resolves into another root's tree)".
5. **`TrustedCode/os.lean`: the 11 `CallBegin` sites pass their path**: `OpenFile.impl` (`"name"`), `Rename.impl`
   (`"newname"` for the `LstatDir` call, `"oldname"` for the `rename` call), `Remove.impl` (`"name"`, both loops),
   `Mkdir.impl` (`"name"`), `Stat`'s open (`"name"`), `model.unlinkLoop`/`rmdirLoop`/`openLoop` (`"p"`),
   `RemoveAll.impl`'s guard (`"path"`; its `LstatDir("g", "path")` ends it). Each docstring unchanged but
   "`CallBegin` of the path".
6. **Environment** (the header's paragraph, MINOR 2): after "none in another's tree" add "and no root's ancestor
   resolves (through a symlink or a mount) into another root's tree".
7. **Docstrings that say every directory rename by another thread is stuck** (MINOR 3), to the scoped wording:
   - `Impl.lean:96-101` (header, "Races"): "Path calls (`CallBegin` … step) overlap, except that a rename of a
     directory is stuck while any other path call is in flight" → "… overlap, except that a rename of a directory is
     stuck while another path call in its root's tree is in flight, and a rename across roots is stuck"; "…only when
     no directory is moved during the walk" → "…only when no directory on the walk's path is moved during it".
   - `Impl.lean:954-958` (`CallBegin`): "`#() ↦ tok`" → "`#p ↦ tok`, `p` the path the call's step names"; "but a
     directory's rename waits for every other one" → "but a directory's rename waits for every other one in its root's
     tree"; "makes every later directory rename stuck" → "makes every later directory rename in that root's tree stuck".
   - `os.lean:846` (`Stat`): "The `CallBegin` makes a directory rename by another thread stuck until the `open`" →
     "The `CallBegin` of `name` makes a directory rename in `name`'s root's tree by another thread stuck until the
     `open`".
   - `os.lean:1243-1245` (`RemoveAll.impl`): "the model takes a `CallBegin` at its start" → "the model takes a
     `CallBegin` of `path` at its start"; "so that every rename of a directory by another thread is stuck while it
     runs" → "so that every rename of a directory in `path`'s root's tree by another thread is stuck while it runs
     (`path`'s entries are in that tree: a directory above it is in it or above the root, which no step moves)".
8. **Go example:** `meta_dir_rename_stuck.go` restated as the scoped decision (Lean names: `SameRoot`, the clause;
   Allowed: a directory rename in root A while a call in root B is in flight; Excluded: the overlap within one
   root's tree; Why: the evidence above, the test cited); `doc.go`'s row updated.

## Open obligation: the configuration-C run (the attack's plan; this container cannot run it)

No `/dev/loop*` and no `/proc/fs/ext4` here, so neither `c_mkfs` nor `check.sh` runs. On a machine with loop devices:

1. `examples/osfs/semantics/run-models-on-c.sh -run 'TestDirRenameScopedToRoot|TestCrossRootRenameExcluded' -v`
   (makes and mounts a C image, records `check.sh`, runs both tests in it). Expected: the first passes with no
   deviation; the second reports a positive count (the excluded race is real on C).
2. Each test with a **warm** and a **cold** dcache: run once, then `sync; echo 2 > /proc/sys/vm/drop_caches` (dentries
   and inodes) before a second run, so that the walks take `lookup_slow` (`d_alloc_parallel`) as well as RCU walks.
3. A **large hashed B directory**: before the workers start, fill each worker's `m/n/o` parent (and root B) with
   about 100k entries (ext4 `dir_index`, htree), so that the workers' lookups are hashed directory searches that take
   long enough to overlap A's renames; plus `L4_CROSS_DEPTH`/`L4_CROSS_ITERS` raised (1900 / 20000) for the excluded
   case.
For this run, `TestCrossRootRenameExcluded` asserts a positive count when `L4_CROSS_EXPECT=1` (set it with the
1900 / 20000 parameters). Record the outputs in `notes/axiom-review/fs-config/` style beside the note. **The WAL link
does not land before this run** (the user's condition, 2026-11-17).

## What it does not change

The call tokens' numbering, every step's effect, the crash rule, the journal order (two
overlapping calls stay unordered, `meta_overlapping_calls.go`). The environment gains one clause (item 6). Programs proved today: the directory-rename clause is weaker (fewer stuck
states), `CallBegin`'s and the steps' new arguments are what every model already has, and the new `SameRoot s t`
conjunct is stronger (more stuck states): every proved rename today (layer 1's `cut` and `Create`, `os` specs) is
within one directory and its parent, so within one root; the proofs gain that side condition.

## The Lean side (not trusted; for the estimate)

- The fs ghost library (`GooseLang/Ext/Fs/TreeShared*.lean`, `TreeSpecs.lean`): the call permission
  (`osCallPerm q`, whose whole is what a directory rename takes) becomes per root (`osCallPerm r q`); `CallBegin`'s
  spec takes a share of the path's root's permission; `fs_start` hands one whole permission per root. Clients of
  `osCallPerm` (`Spec/os`, `Proof/os`, fileutil, layer 1's specs and proofs, WalTester: about 140 files) gain
  the root argument (their WAL's area's root).
- Layer 1: one `WalGS` per WAL area (`[W : WalGS GF]` stays a class; the server's k members instantiate it k
  times through an explicit instance argument, `(W := Wj)`), the lock token per area.
- Estimate (Scope §5): 1500-3000 lines, of which the fs library's permission split is the uncertain part.

## Attack prompts for the independent review

- Is there a walk of a path `p'` in root B (or above the roots) that reads a dentry a rename of a directory in
  root A changes? (Symlinks: the environment excludes them in the roots' trees; an ancestor of a root may be a
  symlink to an existing directory, which the program never changes.)
- Can a call's recorded path differ from the path its step resolves? (`Rename.impl`'s two calls; `RemoveAll`'s
  guard.) With `SameRoot s t`, does any walk of a `Rename` leave its recorded path's root?
- Does any other step walk two paths (none today but `Rename`)?
- Is `IsUnder` (textual) enough, given that every step requires canonical paths (`TreeName`/`TreePath`), and the
  roots are canonical and absolute (`RootForm`)?
