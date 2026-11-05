# Questions and pending decisions: the namespace of the Linux file extension (branch `worktree-walfs-ext`)

Each item is **decided by the agent, pending the user** (`notes/spec-first-plan.md`, "Proceed with a
veto"): what was chosen, the options, and what depends on it. The design is
`notes/walfs-ext-plan.md`. All of them change the **trust base** (trusted semantics, trusted Go
models, adequacy premises): a hard stop in the plan, carried out here because the user asked for
the extension to be built autonomously; nothing is on `lean`.

1. **N1, the crash model of names: the journal's order** (chosen) vs POSIX (each directory durable
   through its own fsync, independently). Chosen: a crash keeps a prefix of the metadata
   operations since the last commit; an fsync of a directory commits the journal through the last
   operation that changed it. True of ext4 (`data=ordered`/`journal`, journal on, no `fast_commit`)
   and xfs; a new environment assumption. Under POSIX, etcd's `wal.Create` is not crash-safe (it
   never syncs `dirpath.tmp` after creating the first segment in it; `examples/osfs/walfs/dirswap.go`,
   `TestBootDirPOSIX`): verifying the WAL under POSIX would need a fork change (sync the temporary
   directory). Depends on it: every crash proof over the namespace.

2. **N2, two regimes** (chosen): the existing per-path model stays for paths outside the roots
   (bbolt's, crashlog's); paths in the roots' trees go through the namespace, files there keyed by
   fresh NUL-containing keys. Rejected: one inode-keyed model for all paths (every existing spec and
   bbolt proof restated). Consequence: a program cannot rename a legacy path, and a root cannot be
   renamed or removed. The trusted `os.OpenFile`/`Sync`/`Close` dispatch through two queries of the
   model's state (`Regime`, `FdKind`), which are not system calls.

3. **A crash forces a file the namespace names to survive** (`NsCrash`'s last clause) while
   `OsCrashFiles` alone lets a file created since boot vanish (D4): the namespace decides names.
   The bytes keep D1/D2.

4. **An fsync of a file commits no name** (weaker than ext4/xfs, where it commits the journal up to
   the file's last change, its creation included). Not needed by the WAL; a stronger model would
   be sound on ext4/xfs.

5. **Directory identity is its path**: an fsync of a directory commits the operations recorded with
   that path as a parent. After a directory is renamed, an fsync of it by its new path commits less
   than Linux does (sound: weaker). Directory fds pin their directory: renaming or removing a
   directory with an open fd (or one in its tree) is stuck.

6. **Readdir across concurrent changes** is POSIX's (any of the names added or removed meanwhile, all
   of the names there throughout, each once); a second `Readdirnames` on one fd is stuck (Go returns
   nothing); `Readdirnames(n)` with `n > 0` panics in the model (not modelled).

7. **Locks are trivial** (`OfdLock`, as `Flock`, D7): any errno. etcd's purge relies on OFD locks
   excluding a second open file description in the same process (`linux_test.go`,
   `TestOfdLockConflict`); proving the purge safe would need the lock state.

8. **`fallocate`**: mode 0 is a truncate to `max size (off+len)` (two steps, as `ftruncate`);
   `KEEP_SIZE` changes nothing visible; other modes panic in the model.

9. **Not in this round**: `Seek`/`Write`/`Read` at the file offset (the plan: an offset field in the
   trusted `os.file` model over `pread`/`pwrite`), `RemoveAll` (translatable Go), `MkdirAll`, the
   namespace's program logic (ghost state, specs), the crash proof of `segdir.Boot`.
