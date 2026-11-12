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

9. **Not in this round**: `RemoveAll` (translatable Go) and `MkdirAll`. The file offset is
   modelled (round 4: a field of the trusted `os.file`, `File.Seek`/`Write`/`Read` over
   `pread`/`pwrite`; after a failed `Write` the model sets the offset to `-1` (unknown)
   where Go's has moved by the bytes written, so the model is less defined there than Go, never more; an offset that would
   pass `2^62` is a model panic, unreachable for etcd's 64 MB segments).

10. **No two metadata calls at once** (round 1 of the review, finding 4; `NsBegin`): two calls that
    change the namespace and overlap in time are a stuck run, since the journal may order them
    against what the program saw. So no verified program may make metadata calls from two
    goroutines at once. **The WAL does**: `filePipeline`'s goroutine creates the next `N.tmp`
    (`LockFile`, `O_CREATE`) right after handing one over, while `cut` renames the previous one
    (and etcd's purge goroutines remove old files beside both). So with this repair the WAL's
    `cut` is not verifiable; `segdir.Boot` (one goroutine) is. The fix to make before the WAL:
    start/finish steps for the namespace's calls, each logged with the calls that had finished
    when it began, and a crash that keeps a set of logged calls closed under "finished before the
    other began" (with calls on one directory serialized, as the directory's lock serializes
    them). Recommended next; it changes `NsCrash` and the steps again.

11. **An fsync of a directory whose path was rebound commits nothing** (finding 1;
    `dirCommitLen`): sound, and the WAL's `Create`/`cut` are unaffected, but a program that renames
    a directory and then relies on an fsync of it by its new path, before the parent's fsync, cannot
    be proved crash-safe. Directory identities would lift it.

12. **etcd's data directory as a root** (the reviewer's note 11): `wal.Create` syncs `member/`, so the
    root must contain `member/`, which then contains `member/snap/db`. bbolt's file would be in the
    namespace, not the legacy regime: bbolt's proof (legacy paths) and the WAL's (the namespace)
    meet there; the per-key ghost state is the same for both, so the gap is `Open`'s regime, not
    the file specs.

13. **Adequacy is proved for all three examples** (round 4, `notes/walfs-ext-plan.md`):
    `crash_safety` (segdir), `seglog_crash_safety`, `dirswap_crash_safety`, no `sorry`. The
    namespace's ghost state is one element, the history since boot: a program that changes
    directories (`dirswap`) holds it whole around each call, so **two threads cannot change the
    namespace concurrently under this logic** (one owner; a per-directory view, `osDir`, can be
    shared for reading and for file operations in a directory that stays one). That is enough for
    the examples and for etcd's WAL (one goroutine creates, renames and purges), not for a program
    whose threads make directories concurrently: before such a client, split the history (e.g.
    an authoritative history with per-subtree fragments).

14. **`os.Rename.wp_proof` is still an axiom** (`Proof/os/Rename.lean`, D22 S-f, used by the
    server's `Link.lean`), stated over the server's abstract `fileHolds`/`pathOwn`. This branch
    gives `os.Rename` a trusted model (`TrustedCode/os.lean`'s `Rename.impl`) whose specs are
    proved (`wp_renameSeg`, in the walfs proof). The axiom is not refuted by the model, but it is
    now a claim about a modelled function rather than a boundary: before merging, either keep it
    (the server's file predicates are not tied to the namespace) or plan its proof from the
    model (needs the server's data directory as a root, item 12).

15. **What the crash-safety theorems assume about the initial state** (stated for `crash_safety`;
    `seglog_crash_safety`: `dir` a directory, `seg.log` not one; `dirswap_crash_safety`: the
    namespace `Safe`, `wal`'s `seg` `DataGood` if `wal` is a directory): `OsInit`, `dir` a directory of the
    namespace, `seg` and `seg.tmp` not directories, and `seg`'s file, if any, `DataGood` (exactly
    the data). As for crashlog, the package initializer is a hypothesis (`Hinit_wp`). The theorem's
    axioms are the axiomatized Go types and untranslated initializers (`X.init`) of `os`,
    `syscall` and `golang.org/x/sys/unix` (1130 names against crashlog's 390: `seglog.go` imports
    `unix`, which `initialize'` reaches); `#print axioms` shows no `sorryAx` and no proof axiom.

