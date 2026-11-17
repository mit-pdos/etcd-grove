# WAL link L4: the scoped directory rename (trusted text proposal)

**Date:** 2026-11-17. **Branch:** `wal-link`. **Status:** PROPOSAL, not applied (hard stop (a): new trusted
text; needs an independent attack and the user's review). Scope: `notes/wal-link-scope.md` §4.3 (F-b), §5 (L4).

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
  paths, `cleanAbsPath`), it visits the ancestors of its path and the path's components. The roots are distinct,
  none in another's tree (the environment, `Impl.lean`'s header), and the program renames only `TreeName`s
  (strictly below a root): so a directory moved in root A's tree is never on the walk of a path in root B's tree
  (B's ancestors are not below A, else B would be in A's tree), nor on a walk of a strict ancestor of a root
  (`Open`'s outside case). The rename's target `t` is treated the same way (both roots of `s` and `t` count).
- **What the walk does see of the other rename**: `rename_lock` (a seqlock taken by `d_move`) makes an RCU walk
  that *might* have raced a rename retry (`read_seqretry(&rename_lock, …)` in `path_init`/`legitimize_path`; ref-walk
  fallback): a retry, never a different answer; `s_vfs_rename_mutex` (`lock_rename`) serializes cross-directory
  renames among themselves only. Neither changes what an unrelated walk resolves.
- **Measured** (`examples/osfs/semantics/meta_rename_scoped_test.go`, `TestDirRenameScopedToRoot`): root A's thread
  renames directories as `wal.Create` does (mkdir a temporary directory, create a file in it, rename it over the
  target, fsync the parent) and moves a directory across subdirectories of A, while four workers in root B run
  fixed sequences of 15 path calls each (MkdirAll of a deep path, create-exclusive, lstat, file rename, a
  directory rename inside B, open through the moved directory, unlink, rmdir, mkdir of an existing name, rmdir of a
  missing one) and check each result against the sequential outcome: 4 x 3000 sequences against 1350 directory
  renames, no deviation (2.3 s). **Where:** this machine's root filesystem (ext4, Linux 7.0.0-1014-aws), not a
  `c_mkfs` image: the container has no loop devices (`losetup: … failed to set up loop device`) and no
  `/proc/fs/ext4` (so `check.sh` cannot run). The claim is about the VFS's path walk, not ext4's on-disk format,
  so the mount options C fixes do not bear on it; a run on a `c_mkfs` image should be added where loop devices exist.
  Command: `cd examples/osfs/semantics && SEMANTICS_C_DIR=<dir on ext4> GOWORK=off go test -count=1 -run
  TestDirRenameScopedToRoot -v .`

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
   `Rename`'s clause
   `((∃ j, st.lookup s = some (.dir j)) → ∀ k' start', st.proc.calls !! k' = some start' → k' = k)` →
   `((∃ j, st.lookup s = some (.dir j)) → ∀ k' start' p', st.proc.calls !! k' = some (start', p') →
      k' = k ∨ (¬ st.SameRoot s p' ∧ ¬ st.SameRoot t p'))`.
   Its comment and the header's "Races" paragraph: "a rename of a directory is stuck while another call on a path
   in the tree of the source's or the target's root is in flight (a walk reads only its own path's components, and
   no root is in another's tree, so a call in another root's tree, or above the roots, never walks through the
   moved directory or its target)".
5. **`TrustedCode/os.lean`: the 11 `CallBegin` sites pass their path**: `OpenFile.impl` (`"name"`), `Rename.impl`
   (`"newname"` for the `LstatDir` call, `"oldname"` for the `rename` call), `Remove.impl` (`"name"`, both loops),
   `Mkdir.impl` (`"name"`), `Stat`'s open (`"name"`), `model.unlinkLoop`/`rmdirLoop`/`openLoop` (`"p"`),
   `RemoveAll.impl`'s guard (`"path"`; its `LstatDir("g", "path")` ends it). Each docstring unchanged but
   "`CallBegin` of the path".
6. **Go example:** `meta_dir_rename_stuck.go` restated as the scoped decision (Lean names: `SameRoot`, the clause;
   Allowed: a directory rename in root A while a call in root B is in flight; Excluded: the overlap within one
   root's tree; Why: the evidence above, the test cited); `doc.go`'s row updated.

## What it does not change

The roots' environment, the call tokens' numbering, every step's effect, the crash rule, the journal order (two
overlapping calls stay unordered, `meta_overlapping_calls.go`). Programs proved today stay proved: the new clause
is weaker (fewer stuck states); `CallBegin`'s and the steps' new arguments are what every model already has.

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
  guard.)
- Is `IsUnder` (textual) enough, given that every step requires canonical paths (`TreeName`/`TreePath`), and the
  roots are canonical and absolute (`RootForm`)?
